import Nyxis.Internal.PostgresResult

/-! 判定材料の点検索(Assumption 1。定理の外)。判定材料の限定(`Nyxis.Materials`)の接続層。

1 回のアクション呼び出しの判定に必要な実体だけを、主キーの点検索(`PostgresSql.operation` の読み取りの SELECT)で
DB から取得し、部分的な取得 `Nyxis.Materials.Known`(取得した行と、引いたが無かった実体)を組み立てる。
一覧の効果では対象テーブルの行のうちハンドラの問い合わせの絞り込みに合う行(`PostgresSql.selectFiltered`。
絞り込みは DB 側の WHERE 句)を取得する。どちらも SQL はコアが生成したものだけで、要求由来の値(主キー・絞り込みの
定数)はパラメータとして分離する。

取得の範囲は認可層と同じ規則で決める: 要求(主体・アクション・対象・文脈)に現れる実体から、正本のポリシーの
level(`Nyxis.Materials.levelOf`)の段数で到達できる実体(cedar-lean の slicing が辿る集合
`Entities.sliceAtLevel.sliceAtLevel`)を、取得した行の属性を見ながら繰り返し点検索する(`closeOp`)。
テーブルでない型(予約型 `Anonymous`・アクション)は行を持たないので「無い」と記録する。所属行を宣言した型の実体は、行の有無に加えてその所属行(所属する側の列がその実体である行)を WHERE 句つきの SELECT ですべて取得し、
`Known.fetched` に記録する(行の実体の祖先が所属行から決まるため)。

ここで組んだ `Known` が判定材料を覆っているかは、呼び出し側(`PostgresRun.runStaged`)が実行可能な検査
`Nyxis.Authz.coversStep` で確かめてから判定する(通らなければ要求全体を閉じる)。取得が DB の現在の行と
整合すること(`Known.Consistent`、一覧では対象テーブルの行のうち絞り込みに合う行の全部)は、点検索(一覧では
WHERE 句つきの SELECT)の結果が DB の現在の行であるという信頼(`ASSUMPTIONS.md` Assumption 1)に当たる。この未選別の
`Known` をハンドラに出してはならない。
-/
namespace Nyxis.Internal.PostgresMaterials
open Nyxis Nyxis.Db Nyxis.Authz Cedar.Spec
open Nyxis.Materials (Known)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL materials acquisition")

/-- 点検索の SELECT を発行する境界。到達するのはコアが生成したコマンドだけ。 -/
abbrev Select := PostgresSql.Command → IO PostgresResult.Reader

/-- 正本のテーブル(行を持つエンティティ型)か。 -/
def isTable (schema : Authz.Schema) (ty : EntityType) : Bool :=
  schema.tables.any (·.1 == ty)

/-- 取得していない部分的な取得。 -/
def Known.empty : Known := ⟨Cedar.Data.Map.empty, [], []⟩

/-- テーブルの現在の行のうち絞り込みに合う行を取得して加え、その絞り込みをすべて取得したと記録する(一覧の対象
    テーブル・制約の判定が見る行・所属行。絞り込みが無ければ全行)。既に記録していれば何もしない。既に取得した行と
    重なれば取得した行が優先するが、同じトランザクションの中では同じ行。 -/
def loadTable (schema : Authz.Schema) (select : Select) (k : Known) (table : Table) (filters : List Filter) :
    IO Known := do
  if k.fetched.contains (table, filters) then return k
  let .ok command := PostgresSql.selectFiltered schema table filters | invalid
  let result ← PostgresResult.extract schema table (← select command)
  let .ok rows := PostgresSnapshot.tableRows schema table result | invalid
  return { k with rows := Cedar.Data.Map.make (rows ++ k.rows.toList), fetched := (table, filters) :: k.fetched }

/-- 実体 `uid` の所属行(型の各宣言について、所属する側の列が `uid` である行)を WHERE 句つきの SELECT で
    すべて取得する。宣言が無い型では何もしない。 -/
def loadMemberships (schema : Authz.Schema) (select : Select) (k : Known) (uid : EntityUID) : IO Known :=
  ((schema.memberships.lookup uid.ty).getD []).foldlM (fun k m => loadTable schema select k m.table (m.filterOf uid)) k

/-- 1 つの実体の行の有無を点検索で決め、その所属行を取得する。既に分かっていれば何もしない。テーブルでない型は
    行を持たないので「無い」と記録する。主キーの SELECT は不在なら 0 行、あれば要求した主キーの 1 行だけを受け入れる。 -/
def lookup (schema : Authz.Schema) (select : Select) (k : Known) (uid : EntityUID) : IO Known := do
  if k.knows schema.types schema.memberships uid then return k
  if !isTable schema uid.ty then return { k with absent := uid :: k.absent }
  let k ← if k.decided uid then pure k else do
    let .ok command := PostgresSql.operation schema (.read uid.ty uid.eid) | invalid
    let result ← PostgresResult.extract schema uid.ty (← select command)
    let .ok rows := PostgresSnapshot.tableRows schema uid.ty result | invalid
    match rows with
    | [] => pure { k with absent := uid :: k.absent }
    | [(u, row)] =>
      unless u == uid do invalid
      pure { k with rows := k.rows.put uid.ty uid.eid row }
    | _ => invalid
  loadMemberships schema select k uid

/-- 要求から `level` 段で到達できる実体のうち、まだ答えの無いもの(`coversOp` の閉包の検査が見る集合: 行の有無と
    所属行)。 -/
def missing (schema : Authz.Schema) (k : Known) (principal : Principal) (generated : Generated)
    (action : EntityUID) (op : Operation) (level : Nat) : List EntityUID :=
  let es := judgementEntities schema principal k.rows op
  let req := judgementRequest schema principal generated action op
  (Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level).toList.filter fun u =>
    !k.knows schema.types schema.memberships u

/-- 到達できる実体を、段数の分だけ繰り返し点検索する。各回で取得した行の属性が指す実体が次の回の対象になる。
    `fuel` は繰り返しの上限(level + 1 回で閉じる。閉じたかは呼び出し側が `coversOp` で検査する)。 -/
def closeOp (schema : Authz.Schema) (select : Select) (principal : Principal) (generated : Generated)
    (action : EntityUID) (op : Operation) (level : Nat) : Nat → Known → IO Known
  | 0, k => return k
  | fuel + 1, k => do
    match missing schema k principal generated action op level with
    | [] => return k
    | uids =>
      let k ← uids.foldlM (lookup schema select) k
      closeOp schema select principal generated action op level fuel k

/-! ## 制約の判定材料 -/

/-- 一意性の組と同じ値の行(置く行が分かってから。`Authz.uniqueFilters`)。 -/
def loadUnique (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known :=
  (Authz.uniqueFilters schema k.rows op).foldlM (fun k tf => loadTable schema select k tf.1 tf.2) k

/-- 置く行が参照する実体の行の有無(`Authz.referencedUIDs`)。 -/
def loadReferences (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known :=
  match op.newRow k.rows with
  | none => pure k
  | some (t, _, new) => (Authz.referencedUIDs schema t new).foldlM (fun k o =>
      match o with
      | some uid => lookup schema select k uid
      | none => pure k) k

/-- 削除で消える行を参照する行を、連鎖の段ごとに取得する: 消える各行について、その行のテーブルを参照する宣言の列で
    それを参照する行(`restrict` も `cascade` も)。`cascade` で取得した行が次の段の消える行になる。`fuel` は段数の上限
    (`Authz.cascadeFuel`)。 -/
def loadCascade (schema : Authz.Schema) (select : Select) : Nat → Known → List (Table × Key) → IO Known
  | 0, k, _ => pure k
  | fuel + 1, k, frontier => do
    let mut k := k
    let mut next : List (Table × Key) := []
    for (t, key) in frontier do
      for r in schema.constraints.references.filter (·.target == t) do
        k ← loadTable schema select k r.table (Reference.filterOf r.column ⟨t, key⟩)
        if let .cascade _ := r.onDelete then
          next := next ++ (Authz.referencing k.rows r ⟨t, key⟩).map fun kv => (r.table, kv.1)
    if next.isEmpty then pure k else loadCascade schema select fuel k next

/-- 制約の判定が見る行: 一意性の組と同じ値の行、参照先の行、削除で消える行を参照する行(連鎖の段ごと)。 -/
def loadIntegrity (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known := do
  let k ← loadUnique schema select k op
  let k ← loadReferences schema select k op
  match op with
  | .delete t key => loadCascade schema select (Authz.cascadeFuel schema) k [(t, key)]
  | _ => pure k

/-- 1 回のアクション呼び出しの判定材料を点検索で組む。効果の無いアクションは何も取得しない(認可層が拒否する)。
    一覧では対象テーブルの行のうち問い合わせの絞り込みに合う行と主体の行を取得し、取得した行のうち絞り込みに合う
    各行の読み取りについて閉包を取る。それ以外では主体の行と対象の行(無ければ「無い」と記録。挿入では提案される
    行が判定の実体になる)を取得し、制約の判定が見る行を取得し、閉包を取り、連鎖で消える各行の削除についても
    閉包を取る(消した後の状態での検査は呼び出し側の `coversStep`)。 -/
def load (schema : Authz.Schema) (policies : Policies) (select : Select) (principal : Principal)
    (generated : Generated) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) : IO Known := do
  let level := (Nyxis.Materials.levelOf policies schema.types).getD 0
  match schema.effectOf action with
  | none => return Known.empty
  | some effect =>
    match effect.kind with
    | .list =>
      let k ← loadTable schema select Known.empty effect.table query.filters
      let k ← lookup schema select k principal.uid
      (Authz.matchingRows k.rows effect.table query.filters).foldlM (fun k kv =>
        closeOp schema select principal generated action (.read effect.table kv.1) level (level + 1) k) k
    | _ =>
      let op := Operation.ofEffect effect key values
      let k ← lookup schema select Known.empty principal.uid
      let k ← lookup schema select k op.target
      let k ← loadIntegrity schema select k op
      let k ← closeOp schema select principal generated action op level (level + 1) k
      (Authz.deletePlan schema k.rows op).foldlM (fun k e =>
        closeOp schema select principal generated e.1 (.delete e.2.1 e.2.2) level (level + 1) k) k

end Nyxis.Internal.PostgresMaterials
