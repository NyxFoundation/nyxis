import Nyxis.Materials

/-!
# Nyxis.Authz — 認可層

ハンドラが呼ぶアクションごとに、そのリクエストの認証された主体と、DB の現在の行から構成した対象
(挿入・更新では提案される値も含む)について Cedar の判定を行い、permit のときだけ宣言された効果を
DB 層で実行する。

- 主体はそのリクエストの JWT から、対象は DB の現在の行から、効果はスキーマの宣言から、nyxis が決める。
  ハンドラはこれらを指定も差し替えもできない。
- 判定は cedar-spec の `Cedar.Spec.isAuthorized` に委ね、自前で再実装しない。
- Cedar に渡す判定材料の組み立て方(`judgementRequest` / `judgementEntities`):
  - 主体: 認証された主体のエンティティ UID。匿名は予約型 `Anonymous::"anonymous"`。
  - アクション: ハンドラが呼んだアクション。
  - 対象: 操作の対象(テーブルと主キー)。
  - 実体: DB の現在の行のうちスキーマに適合する行がそのまま実体になる(テーブル = 型、主キー = ID、
    列 = 属性。正本が `entity T in [P]` と `@parents("列, …")` で親を指す列を宣言していれば、その列の値が
    実体の祖先 — ポリシーの `in` の判定材料)。それにスキーマの全アクションの実体を加える
    (`Nyxis.Materials.entities`)。
    挿入で現在の行が無ければ、提案される行を対象の実体として加える。ただし主体自身の実体は常に
    DB の現在の行から決まり、提案される値で置き換えない。
  - 文脈: 挿入・更新では提案される値を `context.values` に置く。読み取り・一覧・削除では無い。正本のアクションの
    `context` が `now`(datetime)/ `id`(String)を宣言していれば、nyxis が要求ごとに決めたサーバー生成値
    (`Generated`: 現在時刻と新しい一意 ID)を `context.now` / `context.id` に置く。ハンドラはこの値を
    指定も差し替えもできない(判定に使う値は `Runtime.AuthenticatedRequest` のもの)。
- 判定は判定材料の全体ではなく、要求に現れる実体から有限の段数で到達できる実体だけ(`materials` =
  cedar-lean の `Entities.sliceAtLevel`。段数は正本のポリシーが level 検証に通る最小の level)で行う(`permits`)。
  その判定が判定材料の全体での判定と一致することは `permits_authorized` が cedar-lean の slicing 定理から導き、
  主定理(`Nyxis.Runtime.authorization_safety`)の「正当な権限」(`Authorized`)は判定材料の全体での判定で述べる
 。一致の前提(型環境の well-formedness・要求のインスタンス性・level 検証)は判定ごとに実行可能な検査と
  して確かめ、通らなければ拒否する。実 DB では、限定した材料を主キーの点検索で取得することになる: 部分的な取得
  (`Nyxis.Materials.Known`)が全体の状態と整合し、実行可能な検査 `coversOp` / `coversStep` に通れば、取得した行
  だけでの判定と `step` の結果は全体の状態でのものと一致する(`permits_eq_of_covers` / `step_eq_of_covers`)。
- 一覧(効果 `list`)は、対象テーブルの現在の行のうちハンドラの問い合わせ(`Nyxis.Db.ListQuery`)の絞り込みに
  合う各行について、その行の読み取りと同じ判定材料で Cedar の判定を行い、permit された行(`permittedRows`。件数は
  その数)を並べ替えてページを切ったものを返す(`listRows`)。発行する DB 操作は返す行ごとの読み取りで、
  ハンドラが渡した主キーと値は使わない。絞り込み・並べ替え・ページは判定を変えない(判定は行ごとに同じ材料で行う)。
- 宣言された外部効果(効果 `upload` / `download` — 添付の署名付き URL の発行。`mail` — メール送信。`call` —
  外部 API 呼び出し)は、対象の行の読み取りと同じ判定材料(主体・対象 = その行・文脈。`context.values` を取る
  呼び出しでは提案値を文脈に置く)で Cedar の判定を行い、permit されたときだけ外部効果の記録(`External`: 主体・生成値・
  判定時の状態・アクション・対象の行・提案値・nyxis が決めた内容 `payloadOf` — オブジェクトのパス、行の宣言された列から
  決めた宛先と件名・本文、または正本の送り先の宣言と行の列と提案値から決めた送り先・メソッド・URL・本文)を残す
  (`externalStep`)。DB 操作は発行せず状態も変えない。ハンドラに渡る結果は、署名付き URL の発行では接続層が Storage から
  得た URL(`Outcome.signed`)、`sync` の呼び出しでは接続層が送り先から得て宣言した型に復号した応答(`Outcome.called` /
  `calledError`。純粋モデルではいずれも要求の外部効果の結果の列から来る任意の値)、メールと `async` の呼び出しでは
  `Outcome.ok none` で、行は渡らない。発行・送信の可否はポリシーが決め、パス・バケット・宛先・内容・送り先・URL・ヘッダを
  ハンドラは名指しできない。
- サービス主体: 定期処理(`Nyxis.Runtime.Job`)の主体は JWT ではなくコア設定から決まる、予約型 `Service` の
  実体 `Principal.service id`(= `.user ⟨serviceType, id⟩`。テーブルではないので行は無い)。HTTP の要求の主体は
  接続層が JWT から利用者の型で作るので、サービス主体にはならない(`Nyxis.Internal.ApprovedServer.readAll_response`)。
-/

namespace Nyxis.Authz

open Cedar.Spec
open Nyxis.Db

/-- アクションの宣言。Cedar のアクション(エンティティ UID)と、それに添えられる効果。 -/
structure ActionDecl where
  action : EntityUID
  effect : Nyxis.Db.Effect
  deriving Repr, DecidableEq

/-- スキーマ。テーブル(エンティティ型)とその列、アクションの宣言、そして同じ正本から構成した cedar-lean の
    型環境(属性の型・`appliesTo`・祖先・文脈の型。判定材料の限定の前提検査に使う)。Cedar スキーマ
    (`.cedarschema`)からビルド時に構成される(`Nyxis.CedarSchema` / `Nyxis.Build` の `nyxis_schema`)。 -/
structure Schema where
  tables : List (Table × List Column)
  actions : List ActionDecl
  types : Cedar.Validation.Schema
  /-- 親を指す列: `entity T in [P]` に `@parents("列, …")` を添えたテーブルごとの列。その列の値のうち宣言された
      親の型の実体が、行の実体の祖先になる(`Nyxis.Materials.rowAncestors`)。無いテーブルは祖先を持たない。 -/
  parents : Nyxis.Materials.ParentColumns := []
  /-- 所属行: `entity T in [P]` に `@memberships("M: 列 -> 列, …")` を添えたテーブルごとの宣言。所属行の
      テーブル `M` の行のうち所属する側の列が行の実体であるものの、親を指す列の値が、その実体の祖先になる
      (`Nyxis.Materials.membershipRefs`)。多対多の所属を別テーブルの行で表す形。 -/
  memberships : Nyxis.Materials.MembershipColumns := []
  /-- 一意性と参照整合の宣言: `@unique` / `@references`。判定は `step` が permit の後に行い、違反は
      `Outcome.conflict`。参照される行の削除の連鎖(`cascade`)は、参照する各行をそのテーブルの削除効果を持つ
      宣言済みアクションで判定して発行する。 -/
  constraints : Nyxis.Db.Constraints := {}
  /-- 添付の列: `@attachment("列")` を添えたテーブルごとの、添付のオブジェクトの名を保存する String 列。
      `download` の効果はこの列の現在の値からオブジェクトのパスを決める(`payloadOf`)。 -/
  attachments : List (Table × Column) := []
  /-- 名前付きの送り先: `@external` を添えた予約の仲間ごとの、ベース URL と認証方式。`call` の効果はここから
      URL を組む(`payloadOf`)。認証ヘッダの値はコア設定で、記録には載らない。 -/
  destinations : List (String × Nyxis.Db.Destination) := []
  deriving Repr, DecidableEq

/-- 宣言されたアクションの効果を引く。宣言が無ければ `none`。 -/
def Schema.effectOf (s : Schema) (action : EntityUID) : Option Nyxis.Db.Effect :=
  (s.actions.find? (fun d => d.action == action)).map (·.effect)

/-- 認証された主体。JWT の検証に成功したときだけ `user`、それ以外(JWT 無し・検証失敗)は `anonymous`。 -/
inductive Principal where
  | anonymous
  | user (uid : EntityUID)
  deriving Repr, DecidableEq

/-- 匿名の主体の Cedar エンティティ型 `Anonymous`。nyxis が予約し、テーブルには対応しない。 -/
def anonymousType : EntityType := ⟨"Anonymous", []⟩

/-- 匿名の主体のエンティティ UID `Anonymous::"anonymous"`。 -/
def anonymousUID : EntityUID := ⟨anonymousType, "anonymous"⟩

/-- 主体の Cedar エンティティ UID。 -/
def Principal.uid : Principal → EntityUID
  | .anonymous => anonymousUID
  | .user uid => uid

/-- サービス主体の Cedar エンティティ型 `Service`。nyxis が予約し、テーブルには対応しない。正本が `entity Service;` と
    宣言したときだけ、そのアクションの `appliesTo` の主体に書ける。 -/
def serviceType : EntityType := ⟨"Service", []⟩

/-- サービス主体: JWT ではなくコア設定(`NYXIS_SERVICE_PRINCIPAL`)から決まる ID を持つ `Service` の実体。
    定期処理(`Nyxis.Runtime.Job`)の主体としてだけ現れ、HTTP の要求の主体にはならない(接続層は JWT の主体を利用者の型
    `userType ≠ serviceType` で作る)。行は無いので、ポリシーは `principal is Service` / `principal == Service::"…"` で判定する。 -/
def Principal.service (id : String) : Principal := .user ⟨serviceType, id⟩

/-- サーバー生成値: nyxis が要求ごとに決める現在時刻と新しい一意 ID。ハンドラには値の提案のために
    渡し、ポリシーには正本のアクションの `context` が宣言していれば `context.now` / `context.id` として渡す。
    値を決めるのは接続コード(`Nyxis.Internal.Generated.fresh`: 実時計と乱数。Assumption 1・2)で、純粋モデルは任意の値について
    述べる(一意性や時計の正しさは定理の主張に含まない)。 -/
structure Generated where
  /-- 要求の処理を始めた現在時刻。 -/
  now : Cedar.Spec.Ext.Datetime
  /-- この要求のために新しく作った一意 ID(挿入の主キーに使える)。 -/
  id : String
  deriving Repr, DecidableEq

/-- 正本のアクションの `context` の型に属性 `attr` が宣言されているか(型環境のアクションの項目。
    `Nyxis.CedarSchema.actionEntry` はサーバー生成値の属性を、正本に書かれたときだけ、その名前と型で型環境に置く)。 -/
def Schema.contextHas (s : Schema) (action : EntityUID) (attr : Attr) : Bool :=
  match s.types.acts.find? action with
  | some entry => (entry.context.find? attr).isSome
  | none => false

/-- 判定の文脈の属性: 挿入・更新では提案される値 `values`。正本が宣言していればサーバー生成値 `now` / `id`。 -/
def contextAttrs (schema : Schema) (generated : Generated) (action : EntityUID) (op : Operation) :
    List (Attr × Value) :=
  (match op.proposed with
    | some values => [("values", Value.record values)]
    | none => []) ++
  (if schema.contextHas action "now" then [("now", Value.ext (.datetime generated.now))] else []) ++
  (if schema.contextHas action "id" then [("id", Value.prim (.string generated.id))] else [])

/-- Cedar に渡すリクエスト。主体・アクション・対象と、文脈(挿入・更新で提案される値 `context.values`、
    正本が宣言していればサーバー生成値 `context.now` / `context.id`)。 -/
def judgementRequest (schema : Schema) (principal : Principal) (generated : Generated) (action : EntityUID)
    (op : Operation) : Request :=
  { principal := principal.uid
    action := action
    resource := op.target
    context := Cedar.Data.Map.make (contextAttrs schema generated action op) }

/-- Cedar に渡す実体(判定材料の全体)。DB の現在の行のうちスキーマに適合する行と、スキーマの全アクション
    (`Nyxis.Materials.entities`)。挿入で現在の行が無ければ提案される行を対象の実体として加える
    (主体自身を除く)。 -/
def judgementEntities (schema : Schema) (principal : Principal) (store : Store) (op : Operation) : Entities :=
  match op with
  | .insert t k row =>
    if (store.find? t k).isNone && (⟨t, k⟩ : EntityUID) != principal.uid
    then Nyxis.Materials.entities schema.types schema.parents schema.memberships (store.put t k row)
    else Nyxis.Materials.entities schema.types schema.parents schema.memberships store
  | _ => Nyxis.Materials.entities schema.types schema.parents schema.memberships store

/-- 限定した判定材料: 判定材料の全体のうち、要求(主体・アクション・対象・文脈)に現れる実体から `level` 段で
    到達できる実体だけ(cedar-lean の `Entities.sliceAtLevel`)。`level = 1` なら主体・対象(と文脈に現れる実体)
    そのもの、`level = 2` ならそれらの属性が参照する実体まで。 -/
def materials (schema : Schema) (principal : Principal) (generated : Generated) (store : Store)
    (action : EntityUID) (op : Operation) (level : Nat) : Entities :=
  (judgementEntities schema principal store op).sliceAtLevel
    (judgementRequest schema principal generated action op) level

/-- Cedar の判定が allow か。主体・アクション・対象・文脈を nyxis が組み立てた `Request` に対して判定する。 -/
def isPermitted (policies : Policies) (req : Request) (entities : Entities) : Bool :=
  match (isAuthorized req entities policies).decision with
  | .allow => true
  | .deny => false

/-- 認可層の判定: 正本のポリシーが level 検証に通る最小の level を求め(無ければ拒否)、判定ごとの前提
    (型環境の well-formedness・要求のインスタンス性)を検査し(通らなければ拒否)、限定した判定材料
    `materials` について Cedar が permit と判定したとき真。`permits_authorized` により、これは判定材料の全体
    での判定(`Authorized`)と一致する。 -/
def permits (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (op : Operation) : Bool :=
  let req := judgementRequest schema principal generated action op
  match Nyxis.Materials.levelOf policies schema.types with
  | none => false
  | some level =>
    Nyxis.Materials.premisesHold schema.types req &&
      isPermitted policies req (materials schema principal generated store action op level)

/-- 認可層が発行した 1 つの DB 操作と、その判定に使った材料。定理はこの記録について述べる。 -/
structure Issued where
  /-- 判定に使った主体。そのリクエストの認証された主体。 -/
  principal : Principal
  /-- 判定に使ったサーバー生成値。そのリクエストのために nyxis が決めたもの。 -/
  generated : Generated
  /-- 判定時(操作の適用前)の DB の状態。 -/
  store : Store
  /-- ハンドラが呼んだアクション。 -/
  action : EntityUID
  /-- 発行した DB 操作。 -/
  op : Operation

/-- 発行した操作が「認証された主体の正当な権限」の範囲内であること:
    ハンドラが呼んだアクションにスキーマが効果を宣言しており、操作がその効果の範囲内にあり、
    その時点の DB の状態から組み立てた判定材料について Cedar のポリシーが permit と判定した。 -/
def Authorized (schema : Schema) (policies : Policies) (i : Issued) : Prop :=
  ∃ effect, schema.effectOf i.action = some effect
    ∧ i.op.withinEffect effect = true
    ∧ isPermitted policies (judgementRequest schema i.principal i.generated i.action i.op)
        (judgementEntities schema i.principal i.store i.op) = true

/-- 判定材料の全体は、ある DB の状態から組み立てた `Nyxis.Materials.entities` である
    (挿入では提案される行を置いた状態)。 -/
theorem judgementEntities_entities (schema : Schema) (principal : Principal) (store : Store)
    (op : Operation) :
    ∃ s, judgementEntities schema principal store op
      = Nyxis.Materials.entities schema.types schema.parents schema.memberships s := by
  cases op <;> simp only [judgementEntities]
  all_goals try exact ⟨_, rfl⟩
  split <;> exact ⟨_, rfl⟩

/-- 認可層の判定(限定した判定材料)が permit なら、判定材料の全体でも permit である
    (cedar-lean の slicing 定理。前提は `permits` が検査した型環境・要求・level の検査の成功と、
    `Nyxis.Materials.entities` の構成による実体の適合性)。 -/
theorem permits_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (op : Operation)
    (h : permits schema policies principal generated store action op = true) :
    isPermitted policies (judgementRequest schema principal generated action op)
      (judgementEntities schema principal store op) = true := by
  unfold permits at h
  split at h
  · cases h
  · rename_i level hlevel
    simp only [Bool.and_eq_true] at h
    obtain ⟨hprem, hperm⟩ := h
    obtain ⟨hwf, hreq⟩ := Nyxis.Materials.premisesHold_spec hprem
    have hl := Nyxis.Materials.levelOf_spec hlevel
    obtain ⟨s, hs⟩ := judgementEntities_entities schema principal store op
    unfold materials at hperm
    rw [hs] at hperm ⊢
    unfold isPermitted at hperm ⊢
    rw [Nyxis.Materials.isAuthorized_slice _ _ _ _ _ _ _ hwf hreq hl] at hperm
    exact hperm

/-! ## 宣言された外部効果

添付の署名付き URL の発行(効果 `upload T` / `download T`)、メール送信(`mail T(宛先列; 件名列, 本文列…)`)、
外部 API 呼び出し(`call <送り先> <メソッド> <パス | url: 列> T(列, …) (sync … | async)`)。これらを宣言した
アクションは、対象の行 `T::"key"` について permit されたときだけ、nyxis が決めた内容(`Payload`)の外部効果を記録する:

- `upload` / `download`: Supabase Storage のオブジェクト `T/<key>/<名>` への署名付き URL の発行。名はアップロードでは
  要求のサーバー生成値の一意 ID、ダウンロードでは正本が `@attachment("列")` で名指しした列の現在の値。パスの要素として
  使えない主キーや名(`Nyxis.Db.isObjectToken`)ではパスが決まらない。
- `mail`: 宛先は行の宣言された列の値(Auth からは読まない)、件名は内容の列の先頭の値、本文は残りの列の値(段落)。
- `call`: 送り先は正本の `@external` の宣言(名前・ベース URL・認証方式)で、URL はベース URL に正本の固定のパス
  (`{key}` は主キー)を続けたもの、または対象行の String 列の値(`url: 列`。`https://` のみ。`Nyxis.Db.callUrl`)。
  本文は対象行の宣言された列の名前と値に、`context.values` を取る呼び出しではその提案値(判定の文脈に置かれ、ポリシーが
  絞れる)を続けたもの(`GET` / `DELETE` では本文なし)。認証ヘッダの値はコア設定で、記録には載らない。

対象の行が無い・列が無い・文字列でない値・URL として使えない値では内容が決まらず `Outcome.notFound`(記録しない)。
発行・送信自体は DB を変えず、ハンドラに渡るのは署名付き URL の発行では接続層が Storage から得た URL(`Outcome.signed`)、
`sync` の呼び出しでは接続層が送り先から得て宣言した型に復号した応答(`Outcome.called`)か 2xx 以外の状態コードと本文
(`Outcome.calledError`)、メールと `async` の呼び出しでは `Outcome.ok none` だけ(行は渡らない)。ダウンロードの URL の
パスは添付の列の値を含む: その流出は `download` の効果が宣言する範囲(permit された行の添付への到達)そのものである。 -/

/-- 外部効果の種類。 -/
inductive ExternalKind where
  | upload
  | download
  | mail
  | call
  deriving Repr, DecidableEq

/-- 外部効果の内容。nyxis が正本の宣言・対象の行の列・要求の生成値(・判定を通った提案値)から決め、ハンドラは提案できない。 -/
inductive Payload where
  /-- 署名付きアップロード URL の発行。オブジェクトのパス `テーブル/<主キー>/<生成 ID>`。 -/
  | upload (object : String)
  /-- 署名付きダウンロード URL の発行。オブジェクトのパス `テーブル/<主キー>/<添付の列の値>`。 -/
  | download (object : String)
  /-- メール送信。宛先(行の宣言された列の値)、件名、本文。 -/
  | mail (recipient subject body : String)
  /-- 外部 API 呼び出し。送り先の名前(認証ヘッダはコア設定から送信時に付ける)、メソッド、解決済みの URL、
      本文(列の名前と値。`GET` / `DELETE` では `none`)、実行時機(`sync` なら応答の型と上限の上書き)。 -/
  | call (destination : String) (method : CallMethod) (url : String) (body : Option (List (Column × Cell)))
      (mode : CallMode)
  deriving Repr, DecidableEq

/-- 内容の種類。 -/
def Payload.kind : Payload → ExternalKind
  | .upload _ => .upload
  | .download _ => .download
  | .mail .. => .mail
  | .call .. => .call

/-- 外部効果の結果(接続層が外界から得た値。純粋モデルでは要求の結果の列 `Nyxis.Runtime.Externals` の要素で、任意):
    結果なし(メール・`async` の呼び出し・オブジェクトが無い)、Storage が発行した署名付き URL、`sync` の呼び出しの
    2xx の応答を宣言した型に復号した値、2xx 以外の応答の状態コードと本文。 -/
inductive ExternalResult where
  | none
  | signed (url : String)
  | called (value : Value)
  | calledError (status : Nat) (body : String)
  deriving Repr, DecidableEq

/-- 外部効果の結果としてハンドラに渡る値: 署名付き URL の発行では接続層が得た結果(`signed url` なら `signed url`、
    それ以外ならオブジェクトが無い `notFound`)、メールと `async` の呼び出しでは `ok none`(結果の値は使わない)、`sync` の
    呼び出しでは応答(`called` / `calledError`。応答が無ければ `notFound`)。 -/
def Payload.outcome : Payload → ExternalResult → Outcome
  | .upload _, .signed url | .download _, .signed url => .signed url
  | .upload _, _ | .download _, _ => .notFound
  | .mail .., _ => .ok none
  | .call _ _ _ _ .async, _ => .ok none
  | .call _ _ _ _ (.sync _ _), .called value => .called value
  | .call _ _ _ _ (.sync _ _), .calledError status body => .calledError status body
  | .call _ _ _ _ (.sync _ _), .none | .call _ _ _ _ (.sync _ _), .signed _ => .notFound

/-- テーブルの添付の列(`@attachment("列")`)。宣言が無ければ `none`。 -/
def Schema.attachmentOf (s : Schema) (table : Table) : Option Column :=
  s.attachments.lookup table

/-- 名前付きの送り先(`@external`)の宣言。無ければ `none`。 -/
def Schema.destinationOf (s : Schema) (name : String) : Option Nyxis.Db.Destination :=
  s.destinations.lookup name

/-- 行の String 列の値。列が無い・文字列でなければ `none`。 -/
def stringColumn (row : Row) (column : Column) : Option String :=
  match row.find? column with
  | some (.prim (.string s)) => some s
  | _ => none

/-- メールの内容: 宛先の列の値、内容の列の先頭の値が件名、残りの値が本文(空行で区切る)。 -/
def mailOf (row : Row) (recipient : Column) (content : List Column) : Option Payload := do
  let to ← stringColumn row recipient
  let parts ← content.mapM (stringColumn row)
  match parts with
  | [] => none
  | subject :: body => some (.mail to subject ("\n\n".intercalate body))

/-- 呼び出しの本文: 対象の行の宣言された列の名前と値(列が無ければ決まらない)に、提案値の列を続けたもの。 -/
def callBody (row : Row) (columns : List Column) (values : Row) : Option (List (Column × Cell)) := do
  let fields ← columns.mapM fun c => (row.find? c).map (c, ·)
  some (fields ++ values.toList)

/-- メソッドに応じた本文: `GET` / `DELETE` では本文なし(`some none`)、それ以外では `callBody`(決まらなければ `none`)。 -/
def callBodyOf (method : CallMethod) (row : Row) (columns : List Column) (values : Row) :
    Option (Option (List (Column × Cell))) :=
  if method.hasBody then (callBody row columns values).map some else some none

/-- 呼び出しの内容: 正本の送り先の宣言を引き、URL(`Nyxis.Db.callUrl`: ベース URL と固定のパス、または行の
    URL の列)と本文(行の列と、`proposes` なら提案値)を決める。送り先の宣言が無い・URL が決まらない・列が無ければ
    決まらない。認証ヘッダの値は含まない(送信時にコア設定から付ける)。 -/
def callOf (schema : Schema) (row : Row) (key : Key) (values : Row) (destination : String) (method : CallMethod)
    (target : CallTarget) (columns : List Column) (proposes : Bool) (mode : CallMode) : Option Payload := do
  let decl ← schema.destinationOf destination
  let url ← callUrl decl target key row
  let body ← callBodyOf method row columns (if proposes then values else Cedar.Data.Map.empty)
  some (.call destination method url body mode)

/-- 外部効果の内容: 対象の行があり、効果の種類に応じて正本の宣言・行の列・生成値(・判定を通った提案値 `values`)から
    決まるときだけ。外部効果でない効果では `none`。アップロードのパスの名は生成 ID、ダウンロードの名は添付の列の値
    (`objectPath`: 主キーと名はパスの要素として使えること)。 -/
def payloadOf (schema : Schema) (generated : Generated) (store : Store) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) : Option Payload := do
  let row ← store.find? effect.table key
  match effect.kind with
  | .upload => (objectPath effect.table key generated.id).map .upload
  | .download => do
    let column ← schema.attachmentOf effect.table
    let token ← stringColumn row column
    (objectPath effect.table key token).map .download
  | .mail recipient content => mailOf row recipient content
  | .call destination method target columns proposes mode =>
    callOf schema row key values destination method target columns proposes mode
  | .read | .list | .insert | .update _ | .delete => none

/-- 認可層が発行した 1 つの外部効果(添付の署名付き URL の発行、メール送信、外部 API 呼び出し)の記録と、その判定に
    使った材料。主定理の (6)(8) はこの記録について述べる。 -/
structure External where
  /-- 判定に使った主体。そのリクエストの認証された主体(定期処理ではサービス主体)。 -/
  principal : Principal
  /-- 判定に使ったサーバー生成値。そのリクエストのために nyxis が決めたもの。 -/
  generated : Generated
  /-- 判定時の DB の状態(外部効果は状態を変えない)。 -/
  store : Store
  /-- ハンドラが呼んだアクション。 -/
  action : EntityUID
  /-- 対象の行のテーブルと主キー。 -/
  table : Table
  key : Key
  /-- ハンドラが提案した値(`context.values` を取る呼び出しでだけ判定の文脈と本文に使う。他の効果では使わない)。 -/
  values : Row
  /-- nyxis が決めた内容(オブジェクトのパス、宛先と件名・本文、送り先・メソッド・URL・本文)。 -/
  payload : Payload

/-- 記録の種類。 -/
def External.kind (e : External) : ExternalKind := e.payload.kind

/-- 外部効果の記録が「認証された主体の正当な権限」の範囲内であること: ハンドラが呼んだアクションにスキーマが効果を
    宣言しており(その対象が記録のテーブル)、その効果の判定材料(`Operation.ofEffect`: 対象の行の読み取りと同じ主体・
    対象・文脈。`context.values` を取る呼び出しでは提案値を文脈に置く)について Cedar のポリシーが permit と判定し、
    内容はその効果の宣言・その時点の状態・生成値・提案値から nyxis が決めたもの(`payloadOf`。外部効果の宣言についてだけ
    決まる)である。 -/
def ExternalAuthorized (schema : Schema) (policies : Policies) (e : External) : Prop :=
  ∃ effect, schema.effectOf e.action = some effect ∧ effect.table = e.table
    ∧ isPermitted policies
        (judgementRequest schema e.principal e.generated e.action (Operation.ofEffect effect e.key e.values))
        (judgementEntities schema e.principal e.store (Operation.ofEffect effect e.key e.values)) = true
    ∧ payloadOf schema e.generated e.store effect e.key e.values = some e.payload

/-- 呼び出しの記録の内容の由来(主定理の (8)): 記録の内容が呼び出し `call destination method url body mode` なら、
    ハンドラが呼んだアクションにスキーマがその送り先・メソッド・実行時機の `call` の効果を(送り先の決め方 `target`・
    本文の列 `columns`・提案値を取るか `proposes` とともに)対象テーブルについて宣言しており、送り先 `destination` は
    スキーマに宣言された送り先 `decl` で、対象の行 `row` が判定時の状態にあり、URL は送り先の宣言と固定のパス(または行の
    URL の列)と主キーから(`Nyxis.Db.callUrl`)、本文は行の宣言された列と(`proposes` なら)判定を通った提案値から
    (`callBodyOf`)nyxis が決めたものである。ハンドラの値が入る余地は提案値だけで、それはポリシーの判定を通っている。 -/
def CallRecorded (schema : Schema) (e : External) : Prop :=
  ∀ destination method url body mode, e.payload = .call destination method url body mode →
    ∃ target columns proposes decl row,
      schema.effectOf e.action = some ⟨.call destination method target columns proposes mode, e.table⟩ ∧
      schema.destinationOf destination = some decl ∧
      e.store.find? e.table e.key = some row ∧
      callUrl decl target e.key row = some url ∧
      callBodyOf method row columns (if proposes then e.values else Cedar.Data.Map.empty) = some body

/-- メールの内容が決まれば、それはメールの内容である。 -/
theorem mailOf_kind (row : Row) (recipient : Column) (content : List Column) (p : Payload)
    (h : mailOf row recipient content = some p) : p.kind = .mail := by
  unfold mailOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, parts, _, h⟩ := h
  split at h
  · cases h
  · cases h; rfl

/-- 認可済みの記録の呼び出しの内容は、正本の宣言と対象の行と提案値から決まる(`ExternalAuthorized` の `payloadOf` の展開)。 -/
theorem call_recorded (schema : Schema) (policies : Policies) (e : External)
    (h : ExternalAuthorized schema policies e) : CallRecorded schema e := by
  intro destination method url body mode hpay
  obtain ⟨effect, heff, htable, _, hp⟩ := h
  obtain ⟨kind, table⟩ := effect
  simp only at htable
  subst htable
  rw [hpay] at hp
  unfold payloadOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨row, hrow, hp⟩ := hp
  cases kind with
  | call dest method' target columns proposes mode' =>
    simp only at hp
    unfold callOf at hp
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Payload.call.injEq] at hp
    obtain ⟨decl, hdecl, url', hurl, body', hbody, rfl, rfl, rfl, rfl, rfl⟩ := hp
    exact ⟨target, columns, proposes, decl, row, heff, hdecl, hrow, hurl, hbody⟩
  | upload =>
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨_, _, h⟩ := hp
    cases h
  | download =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨_, _, _, _, _, _, h⟩ := hp
    cases h
  | mail recipient content =>
    simp only at hp
    have := mailOf_kind _ _ _ _ hp
    simp [Payload.kind] at this
  | read => simp at hp
  | list => simp at hp
  | insert => simp at hp
  | update _ => simp at hp
  | delete => simp at hp

/-- 1 回のアクション呼び出しの処理結果。 -/
structure StepResult where
  /-- 処理後の DB の状態。 -/
  store : Store
  /-- 発行した DB 操作の記録(発行順)。発行しなければ空。行の操作では 1 つ、一覧では permit された行ごとの
      読み取り。 -/
  issued : List Issued
  /-- 発行した外部効果の記録。外部効果の宣言で permit され内容が決まったときだけ 1 つ、それ以外は空。 -/
  external : List External
  /-- ハンドラに返す結果。 -/
  outcome : Outcome

-- テーブル `table` の現在の行のうち絞り込みに合う行(`Nyxis.Materials.matchingRows`)。一覧の候補と、一意性・参照整合
-- の判定、所属行がこの経路で行を見る(実 DB では WHERE 句つきの SELECT)。
export Nyxis.Materials (matchingRows)

/-- 一覧の候補: テーブル `table` の現在の行のうち問い合わせの絞り込みに合う行で、その行の読み取り
    (`Operation.read table key`)と同じ判定材料(主体・アクション・対象 = その行。提案される値は無い)で Cedar が
    permit と判定したもの。一覧の件数はこの長さ、返す行はこれを並べ替えてページを切ったもの。 -/
def permittedRows (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (table : Table) (query : ListQuery) : List (Key × Row) :=
  (matchingRows store table query.filters).filter fun kv =>
    permits schema policies principal generated store action (Operation.read table kv.1)

/-- 一覧が返す行: permit された候補(`permittedRows`)を並べ替えてページを切ったもの(`ListQuery.select`)。 -/
def listRows (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (table : Table) (query : ListQuery) : List (Key × Row) :=
  query.select (permittedRows schema policies principal generated store action table query)

/-- 候補の各行は判定材料の全体でも permit されている(`permits_authorized`)。 -/
theorem permittedRows_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (table : Table) (query : ListQuery)
    (kv : Key × Row) (h : kv ∈ permittedRows schema policies principal generated store action table query) :
    isPermitted policies (judgementRequest schema principal generated action (.read table kv.1))
      (judgementEntities schema principal store (.read table kv.1)) = true :=
  permits_authorized _ _ _ _ _ _ _ (List.mem_filter.mp h).2

/-! ## 一意性と参照整合

正本が宣言した制約(`Schema.constraints`)の判定。permit された操作について、DB 操作を発行する前に行う
(permit されない操作は判定せず拒否するので、permit されない主体には制約の判定の結果が見えない。permit された主体には
競合(`conflict`)が、同じ値の行や参照する行の存在を伝えうる — 主キーの競合(409)と同じ種類で、定理の (3) の範囲外)。

- 一意性(`Unique`): 置く行(挿入では提案される行、更新では現在の行に変更を重ねた行)と組の列の値が同じ、別の主キーの
  行があれば競合(`Outcome.conflict`)。置く行に組の列が 1 つでも無ければ比べない。
- 参照整合(`Reference`)の挿入・更新: 置く行の参照の列の値が宣言された型の実体でないか、その行が無ければ競合。
- 参照される行の削除: 削除する行(と連鎖で消える各行)を参照する行が `restrict` の列にあれば競合。`cascade` の列に
  あれば、その行も消える(`cascadePlan`: 深い行から順)。消える各行は、宣言されたアクション(そのテーブルの削除効果を
  持つこと)で、その時点の状態について Cedar の判定を行い(`cascadeRun`)、1 行でも permit されなければ要求全体を
  拒否して何も発行しない。発行する記録の `action` はその宣言されたアクションになる(主定理の (5))。 -/

/-- 操作が置く行: 挿入では提案される行、更新では現在の行に変更を重ねた行(行が無ければ無し)、それ以外は無し。 -/
def _root_.Nyxis.Db.Operation.newRow (store : Store) : Operation → Option (Table × Key × Row)
  | .insert t k row => some (t, k, row)
  | .update t k changes => (store.find? t k).map fun row => (t, k, row.patch changes)
  | .read _ _ | .delete _ _ => none

/-- 一意性の判定で見る行の絞り込み: 置く行のテーブルの一意性の組ごとに、組の列の値との等値。 -/
def uniqueFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  match op.newRow store with
  | none => []
  | some (t, _, new) =>
    (schema.constraints.uniques.filter (·.table == t)).filterMap fun u => (u.filtersOf new).map (t, ·)

/-- 一意性の違反: 置く行と組の列の値が同じ、別の主キーの行がある。 -/
def uniqueViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  match op.newRow store with
  | none => false
  | some (t, k, _) => (uniqueFilters schema store op).any fun tf =>
      (matchingRows store t tf.2).any fun kv => kv.1 != k

/-- 置く行が参照する実体: 参照整合を宣言した列ごとに、列が無ければ無し(参照しない)、値が宣言された型の実体なら
    `some uid`、それ以外(型違い・実体でない値)は `none`(違反)。 -/
def referencedUIDs (schema : Schema) (table : Table) (new : Row) : List (Option EntityUID) :=
  (schema.constraints.references.filter (·.table == table)).filterMap fun r =>
    match new.find? r.column with
    | none => none
    | some (.prim (.entityUID uid)) => some (if uid.ty == r.target then some uid else none)
    | some _ => some none

/-- 参照整合の違反(挿入・更新): 参照する実体が宣言された型の実体でないか、その行が無い。 -/
def referenceViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  match op.newRow store with
  | none => false
  | some (t, _, new) => (referencedUIDs schema t new).any fun
    | none => true
    | some uid => (Cedar.Data.Map.find? store uid).isNone

/-- 実体 `uid` を宣言 `r` の列で参照する行。 -/
def referencing (store : Store) (r : Reference) (uid : EntityUID) : List (Key × Row) :=
  matchingRows store r.table (Reference.filterOf r.column uid)

/-- 削除の連鎖の計画: テーブル `table` の主キー `key` の行を削除するとき、`cascade` の宣言で消える行(その行を参照する
    行と、さらにそれを参照する行 … 深い行が先)と、各行を判定するアクション。`fuel` は辿る段数の上限
    (宣言の数 + 1 で、宣言に循環が無ければ閉じる。正本の検査が循環を拒む)。 -/
def cascadePlan (schema : Schema) (store : Store) : Nat → Table → Key → List (EntityUID × Table × Key)
  | 0, _, _ => []
  | fuel + 1, table, key =>
    (schema.constraints.references.filter (·.target == table)).flatMap fun r =>
      match r.onDelete with
      | .restrict => []
      | .cascade action =>
        (referencing store r ⟨table, key⟩).flatMap fun kv =>
          cascadePlan schema store fuel r.table kv.1 ++ [(action, r.table, kv.1)]

/-- 同じ行(テーブルと主キー)は最初の 1 回だけ残す(2 つの参照の経路で同じ行に届いても 1 回だけ消す)。 -/
def dedupePlan (plan : List (EntityUID × Table × Key)) : List (EntityUID × Table × Key) :=
  plan.foldl (fun acc e => if acc.any (fun d => d.2.1 == e.2.1 && d.2.2 == e.2.2) then acc else acc ++ [e]) []

/-- 連鎖の段数の上限。 -/
def cascadeFuel (schema : Schema) : Nat := schema.constraints.references.length + 1

/-- 削除の操作の連鎖の計画(重複を含む)。削除以外の操作では空。 -/
def cascadePlanOf (schema : Schema) (store : Store) : Operation → List (EntityUID × Table × Key)
  | .delete t k => cascadePlan schema store (cascadeFuel schema) t k
  | _ => []

/-- 削除の操作で消える行の計画(重複を除く)。発行はこの順(深い行が先)。 -/
def deletePlan (schema : Schema) (store : Store) (op : Operation) : List (EntityUID × Table × Key) :=
  dedupePlan (cascadePlanOf schema store op)

/-- 削除の操作で消える行(削除する行と、連鎖の計画の各行。重複を含んでよい)。削除以外の操作では空。 -/
def deletedRows (schema : Schema) (store : Store) : Operation → List (Table × Key)
  | .delete t k => (t, k) :: (cascadePlan schema store (cascadeFuel schema) t k).map (·.2)
  | _ => []

/-- 削除の判定で見る行の絞り込み: 消える各行について、その行のテーブルを参照する宣言ごとに、その行を参照する行。 -/
def deleteFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  (deletedRows schema store op).flatMap fun (t, k) =>
    (schema.constraints.references.filter (·.target == t)).map fun r =>
      (r.table, Reference.filterOf r.column ⟨t, k⟩)

/-- 削除の拒否(`restrict`): 消える行を参照する行が `restrict` の列にあれば競合。 -/
def restrictViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  (deletedRows schema store op).any fun (t, k) =>
    (schema.constraints.references.filter fun r => r.target == t && r.onDelete == .restrict).any fun r =>
      !(referencing store r ⟨t, k⟩).isEmpty

/-- 制約の違反(競合)。 -/
def integrityViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  uniqueViolation schema store op || referenceViolation schema store op || restrictViolation schema store op

/-- 制約の判定が見る行の絞り込み(一意性と削除)。接続層はこれらの行を取得し、取得の整合(絞り込みに合う行の全部)は
    `step_eq_of_covers` の前提になる。 -/
def integrityFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  uniqueFilters schema store op ++ deleteFilters schema store op

/-- 連鎖の削除を順に判定して適用する: 各行について、宣言されたアクションがそのテーブルの削除効果を持ち、その時点の
    状態について permit されれば削除を発行して次へ。1 行でも通らなければ `none`(要求全体を拒否)。 -/
def cascadeRun (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → List (EntityUID × Table × Key) → Option (Store × List Issued)
  | store, [] => some (store, [])
  | store, (action, t, k) :: rest =>
    if schema.effectOf action == some ⟨.delete, t⟩ &&
        permits schema policies principal generated store action (.delete t k) then
      match cascadeRun schema policies principal generated (store.apply (.delete t k)).1 rest with
      | some (s, issued) => some (s, ⟨principal, generated, store, action, .delete t k⟩ :: issued)
      | none => none
    else none

/-- 行の操作(一覧・外部効果以外)の処理: 操作が効果の範囲内にあり、Cedar が permit のときだけ、制約の判定(違反は競合)と
    削除の連鎖(各行の判定。1 行でも通らなければ拒否して何も発行しない)を経て DB 操作を発行する。 -/
def stepOp (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) : StepResult :=
  if op.withinEffect effect then
    if permits schema policies principal generated store action op then
      if integrityViolation schema store op then ⟨store, [], [], .conflict⟩
      else
        match cascadeRun schema policies principal generated store (deletePlan schema store op) with
        | none => ⟨store, [], [], .denied⟩
        | some (s, issued) =>
          -- 連鎖で行が消えた後の状態についてもう一度判定する(発行の記録の `store` はその状態。連鎖が無ければ同じ判定)。
          if permits schema policies principal generated s action op then
            let applied := s.apply op
            ⟨applied.1, issued ++ [⟨principal, generated, s, action, op⟩], [], applied.2⟩
          else ⟨store, [], [], .denied⟩
    else ⟨store, [], [], .denied⟩
  else ⟨store, [], [], .denied⟩

/-- 外部効果(添付の署名付き URL の発行。メール送信。外部 API 呼び出し)の処理: その効果の判定材料
    (`Operation.ofEffect`: 対象の行の読み取りと同じ主体・対象・文脈。`context.values` を取る呼び出しでは提案値 `values` を
    文脈に置く)で Cedar が permit のときだけ、nyxis が決めた内容(`payloadOf`。決まらなければ `notFound`)の発行・送信を
    記録し、結果(`Payload.outcome`: 署名付き URL の発行では接続層が Storage から得た `external`、`sync` の呼び出しでは
    接続層が送り先から得た応答、メールと `async` の呼び出しでは `ok none`)をハンドラに渡す。DB 操作は発行せず状態も
    変えない。permit されなければ `denied` で何も記録しない。 -/
def externalStep (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) : StepResult :=
  if permits schema policies principal generated store action (Operation.ofEffect effect key values) then
    match payloadOf schema generated store effect key values with
    | none => ⟨store, [], [], .notFound⟩
    | some payload =>
      ⟨store, [], [⟨principal, generated, store, action, effect.table, key, values, payload⟩], payload.outcome external⟩
  else ⟨store, [], [], .denied⟩

/-- 1 回のアクション呼び出しを処理する。スキーマで効果を引き、
    一覧の効果なら絞り込みに合う各行について判定し、permit された行(件数)を並べ替えてページを切って返し、
    返す行の読み取りを発行する。
    外部効果(`upload` / `download` / `mail` / `call`)なら対象の行について判定し、permit されたときだけ発行・送信を
    記録して、結果(接続層が外界から得た `external`)をハンドラに渡す(`externalStep`)。
    それ以外の効果なら操作を組み立て、`stepOp` で処理する(効果の範囲内で permit のときだけ、制約の判定と
    削除の連鎖を経て発行)。`external` は外部効果の結果で、他の効果では使われない。 -/
def step (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery)
    (external : ExternalResult := .none) : StepResult :=
  match schema.effectOf action with
  | none => ⟨store, [], [], .denied⟩
  | some effect =>
    match effect.kind with
    | .list =>
      let candidates := permittedRows schema policies principal generated store action effect.table query
      let rows := query.select candidates
      ⟨store, rows.map (fun kv => ⟨principal, generated, store, action, .read effect.table kv.1⟩), [],
        .list rows candidates.length⟩
    | .upload | .download | .mail _ _ | .call .. =>
      externalStep schema policies principal generated store action effect key values external
    | .read | .insert | .update _ | .delete =>
      stepOp schema policies principal generated store action effect (Operation.ofEffect effect key values)

/-- 記録と DB の状態の遷移が整合していること: 状態 `s` から始めて、各記録の `store` がその時点の状態であり、
    記録の操作を順に適用した結果が状態 `s'` である。すなわち DB の状態は記録された操作だけで変わる。 -/
def Coherent : Store → List Issued → Store → Prop
  | s, [], s' => s' = s
  | s, i :: rest, s' => i.store = s ∧ Coherent (s.apply i.op).1 rest s'

theorem Coherent.append {s s' s'' : Store} {l₁ l₂ : List Issued}
    (h₁ : Coherent s l₁ s') (h₂ : Coherent s' l₂ s'') : Coherent s (l₁ ++ l₂) s'' := by
  induction l₁ generalizing s with
  | nil =>
    simp only [Coherent] at h₁
    subst h₁
    simpa using h₂
  | cons i rest ih =>
    simp only [Coherent, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, ih h₁.2⟩

/-- 同じ状態からの読み取りの記録の列は、状態を変えずに整合している。 -/
theorem Coherent.reads (store : Store) (principal : Principal) (generated : Generated) (action : EntityUID)
    (table : Table) (rows : List (Key × Row)) :
    Coherent store (rows.map fun kv => (⟨principal, generated, store, action, .read table kv.1⟩ : Issued)) store := by
  induction rows with
  | nil => rfl
  | cons kv rest ih =>
    simp only [List.map_cons, Coherent, Store.apply_read_fst, true_and]
    exact ih

/-- 連鎖の記録は状態の遷移と整合している(各記録の `store` はその削除の直前の状態)。 -/
theorem cascadeRun_coherent (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (store : Store) (plan : List (EntityUID × Table × Key)) (s : Store) (issued : List Issued),
      cascadeRun schema policies principal generated store plan = some (s, issued) → Coherent store issued s
  | store, [], s, issued, h => by
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | store, (action, t, k) :: rest, s, issued, h => by
    simp only [cascadeRun] at h
    split at h
    · split at h
      · rename_i s' issued' hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, cascadeRun_coherent schema policies principal generated _ rest s' issued' hrest⟩
      · cases h
    · cases h

/-- 連鎖の記録はすべて、そのリクエストの主体とサーバー生成値について、計画に載った行の削除を、その行を判定する
    宣言されたアクション(そのテーブルの削除効果を持つ)について正当な権限の範囲内で発行したものである。 -/
theorem cascadeRun_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (store : Store) (plan : List (EntityUID × Table × Key)) (s : Store) (issued : List Issued),
      cascadeRun schema policies principal generated store plan = some (s, issued) → ∀ i ∈ issued,
        i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
        ∃ t k, i.op = .delete t k ∧ (i.action, t, k) ∈ plan
  | store, [], s, issued, h => by
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i hi
    simp at hi
  | store, (action, t, k) :: rest, s, issued, h => by
    simp only [cascadeRun] at h
    split at h
    · rename_i hcond
      split at h
      · rename_i s' issued' hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro i hi
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨heff, hperm⟩ := hcond
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨rfl, rfl, ⟨⟨.delete, t⟩, heff, by simp [Operation.withinEffect],
            permits_authorized _ _ _ _ _ _ _ hperm⟩, t, k, rfl, List.mem_cons_self⟩
        · obtain ⟨hp, hg, ha, t', k', hop, hmem⟩ :=
            cascadeRun_authorized schema policies principal generated _ rest s' issued' hrest i hi
          exact ⟨hp, hg, ha, t', k', hop, List.mem_cons_of_mem _ hmem⟩
      · cases h
    · cases h

/-- 計画に載る行は、`cascade` の宣言の列でその上位の行を参照する行で、判定するアクションはその宣言のもの。 -/
theorem mem_cascadePlan (schema : Schema) (store : Store) :
    ∀ (fuel : Nat) (table : Table) (key : Key) (e : EntityUID × Table × Key),
      e ∈ cascadePlan schema store fuel table key →
      ∃ r ∈ schema.constraints.references, r.onDelete = .cascade e.1 ∧ r.table = e.2.1
  | 0, _, _, _, h => by simp [cascadePlan] at h
  | fuel + 1, table, key, e, h => by
    simp only [cascadePlan, List.mem_flatMap] at h
    obtain ⟨r, hr, he⟩ := h
    have hr' := (List.mem_filter.mp hr).1
    split at he
    · simp at he
    · rename_i action hod
      simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at he
      obtain ⟨kv, _, he | rfl⟩ := he
      · exact mem_cascadePlan schema store fuel r.table kv.1 e he
      · exact ⟨r, hr', hod, rfl⟩

private theorem mem_dedupe_foldl (e : EntityUID × Table × Key) :
    ∀ (plan acc : List (EntityUID × Table × Key)),
      e ∈ plan.foldl (fun acc e => if acc.any (fun d => d.2.1 == e.2.1 && d.2.2 == e.2.2) then acc else acc ++ [e]) acc →
      e ∈ acc ∨ e ∈ plan
  | [], acc, h => Or.inl h
  | x :: rest, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_dedupe_foldl e rest _ h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_dedupePlan (plan : List (EntityUID × Table × Key)) (e : EntityUID × Table × Key)
    (h : e ∈ dedupePlan plan) : e ∈ plan := by
  rcases mem_dedupe_foldl e plan [] h with h | h
  · simp at h
  · exact h

/-- 記録の判定アクションの由来(主定理の (5)): ハンドラが呼んだアクション `callAction` か、正本が宣言した連鎖の
    削除のアクション(`@references` の `cascade`。その記録はその宣言のテーブルの行の削除)。 -/
def ActionOrigin (schema : Schema) (callAction : EntityUID) (i : Issued) : Prop :=
  i.action = callAction ∨
    ∃ r ∈ schema.constraints.references, r.onDelete = .cascade i.action ∧ ∃ key, i.op = .delete r.table key

/-- `stepOp` の記録は状態の遷移と整合している。 -/
theorem stepOp_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    Coherent store (stepOp schema policies principal generated store action effect op).issued
      (stepOp schema policies principal generated store action effect op).store := by
  unfold stepOp
  split
  · split
    · split
      · simp [Coherent]
      · split
        · simp [Coherent]
        · rename_i s issued hrun
          split
          · exact Coherent.append (cascadeRun_coherent schema policies principal generated store _ s issued hrun)
              ⟨rfl, rfl⟩
          · simp [Coherent]
    · simp [Coherent]
  · simp [Coherent]

/-- `stepOp` が発行した操作はすべて正当な権限の範囲内にあり、判定アクションはハンドラのものか宣言された連鎖のもの。 -/
theorem stepOp_authorized (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (i : Issued)
    (heff : schema.effectOf action = some effect)
    (h : i ∈ (stepOp schema policies principal generated store action effect op).issued) :
    i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
      ActionOrigin schema action i := by
  unfold stepOp at h
  split at h
  · rename_i hwe
    split at h
    · rename_i hperm
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i s issued hrun
          split at h
          · rename_i hperm'
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · obtain ⟨hp, hg, ha, t, k, hop, hmem⟩ :=
                cascadeRun_authorized schema policies principal generated store _ s issued hrun i h
              refine ⟨hp, hg, ha, Or.inr ?_⟩
              have hmem' := mem_dedupePlan _ _ hmem
              cases op with
              | delete t' k' =>
                simp only [cascadePlanOf] at hmem'
                obtain ⟨r, hr, hod, ht⟩ := mem_cascadePlan schema store _ t' k' _ hmem'
                exact ⟨r, hr, hod, k, by rw [hop, ht]⟩
              | read _ _ => simp [cascadePlanOf] at hmem'
              | insert _ _ _ => simp [cascadePlanOf] at hmem'
              | update _ _ _ => simp [cascadePlanOf] at hmem'
            · exact ⟨rfl, rfl, ⟨_, heff, hwe, permits_authorized _ _ _ _ _ _ _ hperm'⟩, Or.inl rfl⟩
          · simp at h
    · simp at h
  · simp at h

/-- `stepOp` がハンドラに(主キー, 行)の組を渡したなら、操作は読み取りで、連鎖も制約の違反も無く、判定時の状態から
    その読み取りを 1 つ発行しており、行はその状態でその主キーが指す行である。 -/
theorem stepOp_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (key : Key) (kv : Key × Row)
    (heff : schema.effectOf action = some effect)
    (h : kv ∈ (stepOp schema policies principal generated store action effect op).outcome.entries key) :
    ∃ i ∈ (stepOp schema policies principal generated store action effect op).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.store = store ∧
      i.action = action ∧ ∃ table readKey, op = .read table readKey ∧ kv.1 = key ∧ i.op = .read table readKey ∧
        store.find? table readKey = some kv.2 := by
  unfold stepOp at h ⊢
  split at h
  · rename_i hwe
    split at h
    · rename_i hperm
      split at h
      · simp [Outcome.entries] at h
      · rename_i hviol
        split at h
        · simp [Outcome.entries] at h
        · rename_i s issued hrun
          split at h
          · rename_i hperm'
            dsimp only at h
            obtain ⟨t, rk, hop, hk, hrow⟩ := Store.apply_entries _ _ _ _ h
            subst hop
            simp only [deletePlan, cascadePlanOf, dedupePlan, List.foldl_nil, cascadeRun, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            refine ⟨⟨principal, generated, store, action, .read t rk⟩, ?_, rfl, rfl,
              ⟨_, heff, hwe, permits_authorized _ _ _ _ _ _ _ hperm'⟩, rfl, rfl, t, rk, rfl, hk, rfl, hrow⟩
            simp [hwe, hperm, hviol]
          · simp [Outcome.entries] at h
    · simp [Outcome.entries] at h
  · simp [Outcome.entries] at h

/-- 行の操作の結果は一覧の結果にならない。 -/
theorem stepOp_outcome_ne_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (rows : List (Key × Row))
    (total : Nat) : (stepOp schema policies principal generated store action effect op).outcome ≠ .list rows total := by
  unfold stepOp
  split
  · split
    · split
      · simp
      · split
        · simp
        · split
          · exact Store.apply_snd_ne_list _ _ _ _
          · simp
    · simp
  · simp

/-- 行の操作の結果は外部効果の結果(署名付き URL・呼び出しの応答)にならない。 -/
theorem stepOp_outcome_isExternal (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    (stepOp schema policies principal generated store action effect op).outcome.isExternal = false := by
  unfold stepOp
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split
          · exact Store.apply_snd_isExternal _ _
          · rfl
    · rfl
  · rfl

/-- 行の操作は外部効果を記録しない。 -/
theorem stepOp_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    (stepOp schema policies principal generated store action effect op).external = [] := by
  unfold stepOp
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · rfl
  · rfl

/-! ### 外部効果の処理の性質 -/

/-- 外部効果の結果は行を渡さない。 -/
theorem Payload.outcome_entries (p : Payload) (external : ExternalResult) (k : Key) :
    (p.outcome external).entries k = [] := by
  cases p with
  | upload _ => cases external <;> rfl
  | download _ => cases external <;> rfl
  | mail _ _ _ => cases external <;> rfl
  | call _ _ _ _ mode => cases mode <;> cases external <;> rfl

/-- 外部効果の結果は一覧の結果にならない。 -/
theorem Payload.outcome_ne_list (p : Payload) (external : ExternalResult) (rows : List (Key × Row)) (total : Nat) :
    p.outcome external ≠ .list rows total := by
  cases p with
  | upload _ => cases external <;> simp [Payload.outcome]
  | download _ => cases external <;> simp [Payload.outcome]
  | mail _ _ _ => cases external <;> simp [Payload.outcome]
  | call _ _ _ _ mode => cases mode <;> cases external <;> simp [Payload.outcome]

/-- 呼び出しの応答(`called` / `calledError`)は呼び出しの内容(`Payload.call`)からだけ生じる。 -/
theorem Payload.outcome_isCalled (p : Payload) (external : ExternalResult)
    (h : (p.outcome external).isCalled = true) : p.kind = .call := by
  cases p with
  | upload _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | download _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | mail _ _ _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | call _ _ _ _ mode => rfl

/-- 外部効果の処理は DB 操作を発行せず、状態を変えない。 -/
theorem externalStep_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) :
    Coherent store (externalStep schema policies principal generated store action effect key values external).issued
      (externalStep schema policies principal generated store action effect key values external).store := by
  unfold externalStep
  split
  · split <;> simp [Coherent]
  · simp [Coherent]

/-- 外部効果の処理は DB 操作を発行しない。 -/
theorem externalStep_issued (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) :
    (externalStep schema policies principal generated store action effect key values external).issued = [] := by
  unfold externalStep
  split
  · split <;> rfl
  · rfl

/-- 外部効果の処理は行を渡さない。 -/
theorem externalStep_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) (k : Key) :
    (externalStep schema policies principal generated store action effect key values external).outcome.entries k
      = [] := by
  unfold externalStep
  split
  · split
    · rfl
    · exact Payload.outcome_entries _ _ _
  · rfl

/-- 外部効果の結果は一覧の結果にならない。 -/
theorem externalStep_outcome_ne_list (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) (external : ExternalResult) (rows : List (Key × Row)) (total : Nat) :
    (externalStep schema policies principal generated store action effect key values external).outcome
      ≠ .list rows total := by
  unfold externalStep
  split
  · split
    · simp
    · exact Payload.outcome_ne_list _ _ _ _
  · simp

/-- 外部効果の記録は、permit された対象の行への、nyxis が決めた内容の発行・送信である: 記録の主体・生成値・状態・
    アクション・対象・提案値は処理のもので、その効果の判定材料で permit され、内容は `payloadOf` が決めたもの。 -/
theorem externalStep_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) (e : External)
    (h : e ∈ (externalStep schema policies principal generated store action effect key values external).external) :
    ∃ payload, e = ⟨principal, generated, store, action, effect.table, key, values, payload⟩ ∧
      permits schema policies principal generated store action (Operation.ofEffect effect key values) = true ∧
      payloadOf schema generated store effect key values = some payload := by
  cases hperm : permits schema policies principal generated store action (Operation.ofEffect effect key values) <;>
    simp only [externalStep, hperm, Bool.false_eq_true, ↓reduceIte] at h
  · simp at h
  · cases hpay : payloadOf schema generated store effect key values <;> simp only [hpay] at h
    · simp at h
    · rename_i payload
      simp only [List.mem_singleton] at h
      exact ⟨payload, h, rfl, rfl⟩

/-- 外部効果の結果の値(署名付き URL・呼び出しの応答)がハンドラに渡ったなら、その呼び出しは外部効果を 1 つ記録しており、
    結果はその記録の内容の `Payload.outcome`。 -/
theorem externalStep_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult)
    (h : (externalStep schema policies principal generated store action effect key values external).outcome.isExternal
      = true) :
    ∃ e, (externalStep schema policies principal generated store action effect key values external).external = [e] ∧
      (externalStep schema policies principal generated store action effect key values external).outcome
        = e.payload.outcome external := by
  cases hperm : permits schema policies principal generated store action (Operation.ofEffect effect key values) <;>
    simp only [externalStep, hperm, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · simp [Outcome.isExternal] at h
  · cases hpay : payloadOf schema generated store effect key values <;> simp only [hpay] at h ⊢
    · simp [Outcome.isExternal] at h
    · exact ⟨_, rfl, rfl⟩

/-- `step` の記録は状態の遷移と整合している: 発行しなければ状態は変わらず、発行すれば記録の `store` は
    判定時の状態で、新しい状態はその操作を適用した結果である(一覧の読み取りと外部効果は状態を変えない)。 -/
theorem step_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult) :
    Coherent store (step schema policies principal generated store action key values query external).issued
      (step schema policies principal generated store action key values query external).store := by
  simp only [step]
  split
  · simp [Coherent]
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => exact Coherent.reads store principal generated action table _
    all_goals first
      | exact externalStep_coherent schema policies principal generated store action _ key values external
      | exact stepOp_coherent schema policies principal generated store action _ _

/-- `step` が発行した操作はすべて、そのリクエストの主体とサーバー生成値について正当な権限の範囲内にあり、
    判定アクションはハンドラが呼んだアクションか、正本が宣言した連鎖の削除のアクションである。
    一覧では、発行した各読み取りの対象の行について、その主体にそのアクションが permit されている。 -/
theorem step_authorized (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (i : Issued)
    (h : i ∈ (step schema policies principal generated store action key values query external).issued) :
    i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
      ActionOrigin schema action i := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [List.mem_map] at h
      obtain ⟨kv, hkv, rfl⟩ := h
      exact ⟨rfl, rfl, ⟨⟨.list, table⟩, heff, by simp [Operation.withinEffect],
        permittedRows_authorized _ _ _ _ _ _ _ _ _ (ListQuery.mem_select _ _ _ hkv)⟩, Or.inl rfl⟩
    all_goals first
      | (rw [externalStep_issued] at h; simp at h)
      | exact stepOp_authorized schema policies principal generated store action _ _ i heff h

/-- `step` が記録した外部効果はすべて、そのリクエストの主体とサーバー生成値について、ハンドラが呼んだアクションで
    判定時の状態について正当な権限の範囲内にある(`ExternalAuthorized`)。対象の主キーと提案値はハンドラが渡したもの。 -/
theorem step_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (e : External)
    (h : e ∈ (step schema policies principal generated store action key values query external).external) :
    e.principal = principal ∧ e.generated = generated ∧ e.store = store ∧ e.action = action ∧ e.key = key ∧
      e.values = values ∧ ExternalAuthorized schema policies e := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => simp at h
    all_goals first
      | (rw [stepOp_external] at h; simp at h)
      | (obtain ⟨payload, rfl, hperm, hpay⟩ := externalStep_external _ _ _ _ _ _ _ _ _ _ e h
         exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, table⟩, heff, rfl, permits_authorized _ _ _ _ _ _ _ hperm, hpay⟩)

/-- 外部効果の結果の値(署名付き URL・呼び出しの応答)がハンドラに渡ったなら、その呼び出しは外部効果を 1 つ記録しており
    (その記録は `step_external` のとおり認可済み)、結果はその記録の内容について結果の列の値から決めたもの。一覧と行の
    操作の結果はこうした値にならない。 -/
theorem step_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (h : (step schema policies principal generated store action key values query external).outcome.isExternal = true) :
    ∃ e, (step schema policies principal generated store action key values query external).external = [e] ∧
      (step schema policies principal generated store action key values query external).outcome
        = e.payload.outcome external := by
  simp only [step] at h ⊢
  split at h
  · simp [Outcome.isExternal] at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => simp [Outcome.isExternal] at h
    all_goals first
      | exact externalStep_result _ _ _ _ _ _ _ _ _ _ h
      | (rw [stepOp_outcome_isExternal] at h; cases h)

/-- 外部効果の結果の値は、発行した DB 操作・外部効果の記録・状態を変えない(ハンドラに渡る結果だけが変わる)。
    接続層は結果を得る前に判定して記録を読み、結果を得た後に同じ呼び出しを結果つきで進める。応答の値が後の呼び出しの
    判定に入る経路は、ハンドラが別のアクションで提案する `values` だけで、それは (1) の判定を通る。 -/
theorem step_external_indep (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (e₁ e₂ : ExternalResult) :
    (step schema policies principal generated store action key values query e₁).issued
        = (step schema policies principal generated store action key values query e₂).issued ∧
      (step schema policies principal generated store action key values query e₁).external
        = (step schema policies principal generated store action key values query e₂).external ∧
      (step schema policies principal generated store action key values query e₁).store
        = (step schema policies principal generated store action key values query e₂).store := by
  simp only [step]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    have indep : ∀ effect : Nyxis.Db.Effect,
        (externalStep schema policies principal generated store action effect key values e₁).issued
            = (externalStep schema policies principal generated store action effect key values e₂).issued ∧
          (externalStep schema policies principal generated store action effect key values e₁).external
            = (externalStep schema policies principal generated store action effect key values e₂).external ∧
          (externalStep schema policies principal generated store action effect key values e₁).store
            = (externalStep schema policies principal generated store action effect key values e₂).store := by
      intro effect
      unfold externalStep
      split
      · split <;> exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
    cases kind
    all_goals first
      | exact ⟨rfl, rfl, rfl⟩
      | exact indep _

/-! ## 部分的な取得との一致(接続層のための定理)

実 DB の接続層は全テーブルではなく、要求に必要な行だけを主キーの点検索で取得する(`Nyxis.Materials.Known`:
取得した行と、引いたが無かった実体)。`coversOp` は、その取得が 1 つの操作の判定材料を覆っているか(対象の行の
有無が分かっており、要求から到達できる実体がすべて取得済みか)を実行可能に検査する。検査に通り、取得が全体の
状態と整合していれば(`Known.Consistent`)、取得した行だけでの判定(`permits`)と `step` の結果(ハンドラに渡る
結果・発行する操作)は、全テーブルを取得した場合と一致する(`permits_eq_of_covers` / `step_eq_of_covers`)。
判定が絞り込みで行を見るところ(一覧の候補、一意性の組と同じ値の行、削除する行を参照する行。`rowFilters`)では
その絞り込みに合う行をすべて取得し(絞り込んだ行列の一致。実 DB では WHERE 句)、取得した行について `coversOp`
(一覧では各行の読み取り、削除の連鎖では各行の削除)と参照先の行の有無を検査する。 -/

open Nyxis.Materials (Known)

/-- 部分的な取得が 1 つの操作の判定材料を覆っているか(実行可能な検査): 対象の行の有無が分かっており、
    ポリシーの level について要求から到達できる実体がすべて取得済み(または行の実体にならない型)である。 -/
def coversOp (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (op : Operation) : Bool :=
  k.decided op.target &&
  match Nyxis.Materials.levelOf policies schema.types with
  | none => true
  | some level =>
    Nyxis.Materials.closedAt (judgementEntities schema principal k.rows op)
      (k.knows schema.types schema.memberships) (judgementRequest schema principal generated action op) level

/-- 行を消した後の部分的な取得: 行は消した後の状態(`Store.apply` の削除)、消した実体は無いと分かっている。
    すべて取得した絞り込みの記録は保つ(消した行は両方の状態から消える)。 -/
def _root_.Nyxis.Materials.Known.remove (k : Known) (t : Table) (key : Key) : Known :=
  ⟨(k.rows.apply (.delete t key)).1, ⟨t, key⟩ :: k.absent, k.fetched⟩

/-- 参照整合の判定材料を覆っているか: 置く行が参照する実体の行の有無が分かっている。 -/
def coversReferences (schema : Schema) (k : Known) (op : Operation) : Bool :=
  match op.newRow k.rows with
  | none => true
  | some (t, _, new) => (referencedUIDs schema t new).all fun
    | none => true
    | some uid => k.decided uid

/-- 削除の連鎖の判定材料を覆っているか: 計画の各行の削除について、その時点(前の行を消した後)の取得で `coversOp`。 -/
def coversCascade (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Known → List (EntityUID × Table × Key) → Bool
  | _, [] => true
  | k, (action, t, key) :: rest =>
    coversOp schema policies k principal generated action (.delete t key) &&
      coversCascade schema policies principal generated (k.remove t key) rest

/-- 連鎖の計画の行をすべて消した後の部分的な取得。 -/
def _root_.Nyxis.Materials.Known.removeAll (k : Known) (plan : List (EntityUID × Table × Key)) : Known :=
  plan.foldl (fun k e => k.remove e.2.1 e.2.2) k

/-- 制約の判定と連鎖の判定材料を覆っているか: 参照先の行の有無、連鎖の各行の判定、連鎖の後の状態での操作の判定。 -/
def coversIntegrity (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (op : Operation) : Bool :=
  let plan := deletePlan schema k.rows op
  coversReferences schema k op && coversCascade schema policies principal generated k plan &&
    coversOp schema policies (k.removeAll plan) principal generated action op

/-- 1 回のアクション呼び出し(`step`)の判定材料を覆っているか: 一覧では取得した対象テーブルの行のうち絞り込みに
    合う各行の読み取りについて、外部効果ではその判定材料の操作について `coversOp`(制約の判定は無い)、それ以外では
    組み立てた操作について `coversOp`、さらに制約と連鎖の判定材料。 -/
def coversStep (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) : Bool :=
  match schema.effectOf action with
  | none => true
  | some effect =>
    match effect.kind with
    | .list => (matchingRows k.rows effect.table query.filters).all fun kv =>
        coversOp schema policies k principal generated action (.read effect.table kv.1)
    | .upload | .download | .mail _ _ | .call .. =>
      coversOp schema policies k principal generated action (Operation.ofEffect effect key values)
    | .read | .insert | .update _ | .delete =>
      let op := Operation.ofEffect effect key values
      coversOp schema policies k principal generated action op &&
        coversIntegrity schema policies k principal generated action op

/-- 判定が絞り込みで見る行(テーブルと絞り込み): 一覧では対象テーブルの問い合わせの絞り込み、外部効果では無し、それ以外
    では制約の判定が見る絞り込み(`integrityFilters`)。接続層はこの行をすべて取得し、その一致が `step_eq_of_covers` の
    前提。 -/
def rowFilters (schema : Schema) (store : Store) (action : EntityUID) (key : Key) (values : Row)
    (query : ListQuery) : List (Table × List Filter) :=
  match schema.effectOf action with
  | none => []
  | some effect =>
    match effect.kind with
    | .list => [(effect.table, query.filters)]
    | .upload | .download | .mail _ _ | .call .. => []
    | .read | .insert | .update _ | .delete => integrityFilters schema store (Operation.ofEffect effect key values)

/-- 行を置いても、絞り込みに合う行の集合の一致は保たれる(両方に同じ行を置く)。 -/
theorem RowsAgree.put {s₁ s₂ : Store} {table : Table} {filters : List Filter}
    (h : Nyxis.Materials.RowsAgree s₁ s₂ table filters) (t : Table) (key : Key) (row : Row) :
    Nyxis.Materials.RowsAgree (s₁.put t key row) (s₂.put t key row) table filters := by
  intro kv
  have := h kv
  rw [Nyxis.Materials.mem_matchingRows_iff, Nyxis.Materials.mem_matchingRows_iff] at this ⊢
  rw [Nyxis.Materials.find?_put, Nyxis.Materials.find?_put]
  by_cases heq : (⟨table, kv.1⟩ : EntityUID) = ⟨t, key⟩
  · simp only [heq, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    exact this

/-- 判定材料の全体は、取得が整合し対象の有無が分かっていれば、答えを持つ実体(行の有無が分かり、所属行を取得済み)
    について全体の状態から組んだものと同じ `find?` を返す(挿入で提案される行を置く分岐も一致する)。 -/
theorem judgementEntities_find?_eq (schema : Schema) (k : Known) (full : Store) (principal : Principal)
    (op : Operation) (u : EntityUID) (hc : k.Consistent full)
    (ht : k.decided op.target = true) (hk : k.knows schema.types schema.memberships u = true) :
    (judgementEntities schema principal k.rows op).find? u
      = (judgementEntities schema principal full op).find? u := by
  have hagree : (schema.types.ets.find? u.ty).isSome = true → Cedar.Data.Map.find? k.rows u = Cedar.Data.Map.find? full u :=
    fun htab => Nyxis.Materials.Known.find?_eq_of_knows hc hk htab
  have hmem : (schema.types.ets.find? u.ty).isSome = true → ∀ m ∈ (schema.memberships.lookup u.ty).getD [],
      Nyxis.Materials.RowsAgree k.rows full m.table (m.filterOf u) :=
    fun htab => Nyxis.Materials.Known.memberships_eq_of_knows hc hk htab
  cases op with
  | insert t key row =>
    have htarget : Store.find? k.rows t key = Store.find? full t key :=
      Nyxis.Materials.Known.find?_eq_of_decided hc ht
    simp only [judgementEntities, htarget]
    split
    · apply Nyxis.Materials.entities_find?_eq
      · intro htab
        rw [Nyxis.Materials.find?_put, Nyxis.Materials.find?_put]
        split
        · rfl
        · exact hagree htab
      · intro htab m hm
        exact RowsAgree.put (hmem htab m hm) t key row
    · exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | read t key => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | update t key changes => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | delete t key => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem

/-- 検査に通った部分的な取得から組んだ限定した判定材料は、全体の状態から組んだものと等しい。 -/
theorem materials_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (op : Operation) (level : Nat)
    (hc : k.Consistent full)
    (hlevel : Nyxis.Materials.levelOf policies schema.types = some level)
    (hcov : coversOp schema policies k principal generated action op = true) :
    materials schema principal generated k.rows action op level
      = materials schema principal generated full action op level := by
  simp only [coversOp, hlevel, Bool.and_eq_true] at hcov
  obtain ⟨ht, hclosed⟩ := hcov
  unfold materials
  apply Nyxis.Materials.sliceAtLevel_eq
  intro u hu
  exact judgementEntities_find?_eq schema k full principal op u hc ht
    (Nyxis.Materials.closedAt_spec hclosed u hu)

/-- 検査に通った部分的な取得だけでの認可層の判定は、全体の状態での判定と一致する(許可も拒否も)。 -/
theorem permits_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (op : Operation)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action op = true) :
    permits schema policies principal generated k.rows action op
      = permits schema policies principal generated full action op := by
  simp only [permits]
  cases hlevel : Nyxis.Materials.levelOf policies schema.types with
  | none => rfl
  | some level =>
    dsimp only
    rw [materials_eq_of_covers schema policies k full principal generated action op level hc hlevel hcov]

/-- 対象の行の `find?` が一致すれば、操作の結果(ハンドラに渡る `Outcome`)は一致する。 -/
theorem apply_snd_eq (s₁ s₂ : Store) (op : Operation)
    (h : Cedar.Data.Map.find? s₁ op.target = Cedar.Data.Map.find? s₂ op.target) :
    (s₁.apply op).2 = (s₂.apply op).2 := by
  cases op <;> simp only [Store.apply, Store.find?, Operation.target] at h ⊢ <;> rw [h] <;> split <;> rfl

/-- 対象テーブルの行のうち絞り込みに合う行をすべて取得し(絞り込んだ行列の一致)、その各行の読み取りについて検査に
    通れば、一覧の候補は全体の状態での候補と一致する(したがって件数も返す行も一致する)。 -/
theorem permittedRows_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (table : Table) (query : ListQuery)
    (hc : k.Consistent full)
    (htable : matchingRows k.rows table query.filters = matchingRows full table query.filters)
    (hcov : (matchingRows k.rows table query.filters).all
      (fun kv => coversOp schema policies k principal generated action (.read table kv.1)) = true) :
    permittedRows schema policies principal generated k.rows action table query
      = permittedRows schema policies principal generated full action table query := by
  unfold permittedRows
  rw [← htable]
  apply List.filter_congr
  intro kv hkv
  exact permits_eq_of_covers schema policies k full principal generated action _ hc
    (List.all_eq_true.mp hcov kv hkv)

/-! ### 制約の判定と連鎖の一致 -/

private theorem flatMap_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a List.mem_cons_self]
    rw [flatMap_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

private theorem any_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a List.mem_cons_self]
    rw [any_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- 対象の行の有無が分かっていれば、置く行は一致する。 -/
theorem newRow_eq (k : Known) (full : Store) (op : Operation) (hc : k.Consistent full)
    (hd : k.decided op.target = true) : op.newRow k.rows = op.newRow full := by
  have h := Nyxis.Materials.Known.find?_eq_of_decided hc hd
  cases op <;> try rfl
  simp only [Operation.target] at h
  simp only [Operation.newRow, Store.find?, h]

/-- 一意性の判定は、置く行が一致し、組の列と同じ値の行をすべて取得していれば一致する。 -/
theorem uniqueViolation_eq (schema : Schema) (k : Known) (full : Store) (op : Operation)
    (hnew : op.newRow k.rows = op.newRow full)
    (hfilt : ∀ tf ∈ uniqueFilters schema k.rows op,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    uniqueViolation schema k.rows op = uniqueViolation schema full op := by
  have hf : uniqueFilters schema k.rows op = uniqueFilters schema full op := by
    simp only [uniqueFilters, hnew]
  unfold uniqueViolation
  rw [hnew, ← hf]
  split
  · rfl
  · rename_i t key new heq
    apply any_congr
    intro tf htf
    have := hfilt tf htf
    have hft : tf.1 = t := by
      simp only [uniqueFilters, hnew, heq, List.mem_filterMap, Option.map_eq_some_iff] at htf
      obtain ⟨u, _, fs, _, rfl⟩ := htf
      rfl
    rw [hft] at this
    rw [this]

/-- 参照整合の判定は、置く行が一致し、参照する実体の行の有無が分かっていれば一致する。 -/
theorem referenceViolation_eq (schema : Schema) (k : Known) (full : Store) (op : Operation)
    (hc : k.Consistent full) (hnew : op.newRow k.rows = op.newRow full)
    (hcov : coversReferences schema k op = true) :
    referenceViolation schema k.rows op = referenceViolation schema full op := by
  unfold coversReferences at hcov
  unfold referenceViolation
  rw [hnew] at hcov ⊢
  split at hcov
  · rfl
  · rename_i t key new heq
    apply any_congr
    intro o ho
    cases o with
    | none => rfl
    | some uid =>
      have hd := List.all_eq_true.mp hcov (some uid) ho
      simp only at hd
      simp only [Nyxis.Materials.Known.find?_eq_of_decided hc hd]

/-- 連鎖の計画は、消える各行を参照する行をすべて取得していれば一致する。 -/
theorem cascadePlan_eq (schema : Schema) (s₁ s₂ : Store) :
    ∀ (fuel : Nat) (t : Table) (k : Key),
      (∀ r ∈ schema.constraints.references, r.target = t → referencing s₁ r ⟨t, k⟩ = referencing s₂ r ⟨t, k⟩) →
      (∀ e ∈ cascadePlan schema s₁ fuel t k, ∀ r ∈ schema.constraints.references, r.target = e.2.1 →
        referencing s₁ r ⟨e.2.1, e.2.2⟩ = referencing s₂ r ⟨e.2.1, e.2.2⟩) →
      cascadePlan schema s₁ fuel t k = cascadePlan schema s₂ fuel t k
  | 0, _, _, _, _ => rfl
  | fuel + 1, t, k, h₁, h₂ => by
    simp only [cascadePlan]
    apply flatMap_congr
    intro r hr
    have hr' := List.mem_filter.mp hr
    have ht : r.target = t := by simpa using hr'.2
    cases hod : r.onDelete with
    | restrict => rfl
    | cascade action =>
      have hrows := h₁ r hr'.1 ht
      rw [← hrows]
      apply flatMap_congr
      intro kv hkv
      have hmem : ∀ e, e ∈ cascadePlan schema s₁ fuel r.table kv.1 ++ [(action, r.table, kv.1)] →
          e ∈ cascadePlan schema s₁ (fuel + 1) t k := by
        intro e he
        simp only [cascadePlan, List.mem_flatMap]
        refine ⟨r, hr, ?_⟩
        simp only [hod, List.mem_flatMap]
        exact ⟨kv, hkv, he⟩
      rw [cascadePlan_eq schema s₁ s₂ fuel r.table kv.1
        (fun r' hr'' ht' => h₂ (action, r.table, kv.1) (hmem _ (List.mem_append_right _ List.mem_cons_self)) r' hr'' ht')
        (fun e he r' hr'' ht' => h₂ e (hmem e (List.mem_append_left _ he)) r' hr'' ht')]

/-- 連鎖で消える行(計画と削除する行)は、消える各行を参照する行をすべて取得していれば一致する。 -/
theorem deletedRows_eq (schema : Schema) (s₁ s₂ : Store) (op : Operation)
    (hr : ∀ tk ∈ deletedRows schema s₁ op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing s₁ r ⟨tk.1, tk.2⟩ = referencing s₂ r ⟨tk.1, tk.2⟩) :
    cascadePlanOf schema s₁ op = cascadePlanOf schema s₂ op ∧
      deletedRows schema s₁ op = deletedRows schema s₂ op := by
  cases op with
  | delete t k =>
    simp only [cascadePlanOf, deletedRows] at hr ⊢
    have hplan := cascadePlan_eq schema s₁ s₂ (cascadeFuel schema) t k
      (fun r hr' ht => hr (t, k) List.mem_cons_self r hr' ht)
      (fun e he r hr' ht => hr e.2 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩)) r hr' ht)
    exact ⟨hplan, by rw [hplan]⟩
  | read _ _ => exact ⟨rfl, rfl⟩
  | insert _ _ _ => exact ⟨rfl, rfl⟩
  | update _ _ _ => exact ⟨rfl, rfl⟩

/-- 削除の拒否の判定は、消える各行を参照する行をすべて取得していれば一致する。 -/
theorem restrictViolation_eq (schema : Schema) (s₁ s₂ : Store) (op : Operation)
    (hr : ∀ tk ∈ deletedRows schema s₁ op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing s₁ r ⟨tk.1, tk.2⟩ = referencing s₂ r ⟨tk.1, tk.2⟩) :
    restrictViolation schema s₁ op = restrictViolation schema s₂ op := by
  unfold restrictViolation
  rw [← (deletedRows_eq schema s₁ s₂ op hr).2]
  apply any_congr
  intro tk htk
  apply any_congr
  intro r hr'
  have hr'' := List.mem_filter.mp hr'
  simp only [Bool.and_eq_true, beq_iff_eq] at hr''
  rw [hr tk htk r hr''.1 hr''.2.1]

/-- 行を消した後の `find?`: 消した主キーなら無く、それ以外は元のまま。 -/
theorem find?_remove (s : Store) (t : Table) (key : Key) (u : EntityUID) :
    Cedar.Data.Map.find? (s.remove t key) u = if u = ⟨t, key⟩ then none else Cedar.Data.Map.find? s u := by
  rw [Nyxis.Materials.map_find?_eq_list_find?, Nyxis.Materials.map_find?_eq_list_find?]
  simp only [Store.remove, Cedar.Data.Map.filter, Cedar.Data.Map.toList, List.find?_filter]
  split
  · rename_i heq
    subst heq
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro kv _
      simp
  · rename_i hne
    congr 2
    funext a
    by_cases hk : a.fst = u
    · simp [hk, hne]
    · simp [hk]

/-- 行を消しても、絞り込みに合う行の集合の一致は保たれる(両方から同じ行を消す)。 -/
theorem RowsAgree.remove {s₁ s₂ : Store} {table : Table} {filters : List Filter}
    (h : Nyxis.Materials.RowsAgree s₁ s₂ table filters) (t : Table) (key : Key) :
    Nyxis.Materials.RowsAgree (s₁.remove t key) (s₂.remove t key) table filters := by
  intro kv
  have := h kv
  rw [Nyxis.Materials.mem_matchingRows_iff, Nyxis.Materials.mem_matchingRows_iff] at this ⊢
  rw [find?_remove, find?_remove]
  by_cases heq : (⟨table, kv.1⟩ : EntityUID) = ⟨t, key⟩
  · simp only [heq, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    exact this

/-- 行を消した後の部分的な取得は、消す行の有無が分かっていれば、消した後の全体の状態と整合する(すべて取得した
    絞り込みの記録も保たれる)。 -/
theorem Known.remove_consistent {k : Known} {full : Store} (hc : k.Consistent full) (t : Table) (key : Key)
    (hd : k.decided ⟨t, key⟩ = true) :
    (k.remove t key).Consistent (full.apply (.delete t key)).1 := by
  have hfind : Store.find? k.rows t key = Store.find? full t key :=
    Nyxis.Materials.Known.find?_eq_of_decided hc hd
  simp only [Known.remove, Store.apply, hfind]
  cases hf : Store.find? full t key with
  | none =>
    refine ⟨fun uid row h => hc.1 uid row h, ?_, hc.2.2⟩
    intro uid hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hf
    · exact hc.2.1 uid hu
  | some row =>
    refine ⟨?_, ?_, ?_⟩
    · intro uid r h
      rw [find?_remove] at h ⊢
      split at h
      · cases h
      · rename_i hne
        simp only [hne, ↓reduceIte]
        exact hc.1 uid r h
    · intro uid hu
      rw [find?_remove]
      split
      · rfl
      · rename_i hne
        rcases List.mem_cons.mp hu with rfl | hu
        · exact absurd rfl hne
        · exact hc.2.1 uid hu
    · intro tf htf
      exact RowsAgree.remove (hc.2.2 tf htf) t key

/-- 行を消しても、有無が分かっている実体は分かったまま。 -/
theorem Known.decided_remove {k : Known} (t : Table) (key : Key) {u : EntityUID}
    (hd : k.decided u = true) : (k.remove t key).decided u = true := by
  simp only [Known.decided, Known.remove, Store.apply, Bool.or_eq_true, List.contains_iff_mem,
    List.mem_cons] at hd ⊢
  by_cases hu : u = ⟨t, key⟩
  · exact Or.inr (Or.inl hu)
  · rcases hd with hd | hd
    · left
      split
      · rw [find?_remove]
        simp only [hu, ↓reduceIte]
        exact hd
      · exact hd
    · exact Or.inr (Or.inr hd)

/-- 連鎖の計画の行を消しても、有無が分かっている実体は分かったまま。 -/
theorem Known.decided_removeAll : ∀ (plan : List (EntityUID × Table × Key)) (k : Known) (u : EntityUID),
    k.decided u = true → (k.removeAll plan).decided u = true
  | [], _, _, hd => hd
  | e :: rest, k, u, hd =>
    Known.decided_removeAll rest (k.remove e.2.1 e.2.2) u (Known.decided_remove e.2.1 e.2.2 hd)

/-- 2 つの連鎖の結果の一致: 成功か拒否かが同じで、両方とも成功なら、取得した行の状態は計画の行を消した後の部分的な
    取得の行で、それが全体の状態と整合し、記録(主体・生成値・アクション・操作)が一致する。 -/
def CascadeAgree (k : Known) (plan : List (EntityUID × Table × Key))
    (r₁ r₂ : Option (Store × List Issued)) : Prop :=
  r₁.isSome = r₂.isSome ∧
  ∀ s₁ is₁ s₂ is₂, r₁ = some (s₁, is₁) → r₂ = some (s₂, is₂) →
    (k.removeAll plan).rows = s₁ ∧ (k.removeAll plan).Consistent s₂ ∧
      is₁.map (fun i => (i.principal, i.generated, i.action, i.op))
        = is₂.map (fun i => (i.principal, i.generated, i.action, i.op))

/-- 検査に通った部分的な取得だけでの連鎖の判定と記録は、全体の状態でのものと一致する。 -/
theorem cascadeRun_eq_of_covers (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (plan : List (EntityUID × Table × Key)) (k : Known) (full : Store), k.Consistent full →
      coversCascade schema policies principal generated k plan = true →
      CascadeAgree k plan (cascadeRun schema policies principal generated k.rows plan)
        (cascadeRun schema policies principal generated full plan)
  | [], k, full, hc, _ => by
    refine ⟨rfl, ?_⟩
    intro s₁ is₁ s₂ is₂ h₁ h₂
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, hc, rfl⟩
  | (action, t, key) :: rest, k, full, hc, hcov => by
    simp only [coversCascade, Bool.and_eq_true] at hcov
    obtain ⟨hop, hrest⟩ := hcov
    have hperm := permits_eq_of_covers schema policies k full principal generated action (.delete t key) hc hop
    have hd : k.decided ⟨t, key⟩ = true := by
      simp only [coversOp, Bool.and_eq_true] at hop
      exact hop.1
    have ih := cascadeRun_eq_of_covers schema policies principal generated rest (k.remove t key)
      (full.apply (.delete t key)).1 (Known.remove_consistent hc t key hd) hrest
    have hrows : (k.remove t key).rows = (k.rows.apply (.delete t key)).1 := rfl
    rw [hrows] at ih
    obtain ⟨hsome, hboth⟩ := ih
    have hall : (k.removeAll ((action, t, key) :: rest)) = (k.remove t key).removeAll rest := rfl
    simp only [cascadeRun, hperm]
    split
    · refine ⟨?_, ?_⟩
      · cases h₁ : cascadeRun schema policies principal generated (k.rows.apply (.delete t key)).1 rest <;>
          cases h₂ : cascadeRun schema policies principal generated (full.apply (.delete t key)).1 rest <;>
          simp only [h₁, h₂, Option.isSome] at hsome ⊢ <;> try rfl
        all_goals cases hsome
      · intro s₁ is₁ s₂ is₂ h₁ h₂
        cases hr₁ : cascadeRun schema policies principal generated (k.rows.apply (.delete t key)).1 rest with
        | none => simp [hr₁] at h₁
        | some p₁ =>
          obtain ⟨s₁', is₁'⟩ := p₁
          cases hr₂ : cascadeRun schema policies principal generated (full.apply (.delete t key)).1 rest with
          | none => simp [hr₂] at h₂
          | some p₂ =>
            obtain ⟨s₂', is₂'⟩ := p₂
            simp only [hr₁, hr₂, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            obtain ⟨rfl, rfl⟩ := h₁
            obtain ⟨rfl, rfl⟩ := h₂
            obtain ⟨hk', hcons, hmap⟩ := hboth s₁' is₁' s₂' is₂' hr₁ hr₂
            rw [hall]
            exact ⟨hk', hcons, by simp [hmap]⟩
    · exact ⟨rfl, fun _ _ _ _ h _ => by cases h⟩

/-- **部分的な取得での行の操作の一致**: 取得が全体の状態と整合し、検査(`coversOp` と `coversIntegrity`)に通り、
    制約の判定が見る絞り込みに合う行をすべて取得しているなら、取得した行だけで処理した `stepOp` の結果と発行した
    操作(主体・生成値・アクション・操作)は、全体の状態で処理したものと一致する。 -/
theorem stepOp_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (effect : Nyxis.Db.Effect)
    (op : Operation)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action op = true)
    (hint : coversIntegrity schema policies k principal generated action op = true)
    (hfetch : ∀ tf ∈ integrityFilters schema k.rows op,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    (stepOp schema policies principal generated k.rows action effect op).outcome
        = (stepOp schema policies principal generated full action effect op).outcome ∧
    (stepOp schema policies principal generated k.rows action effect op).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (stepOp schema policies principal generated full action effect op).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) := by
  have hperm := permits_eq_of_covers schema policies k full principal generated action op hc hcov
  have hd : k.decided op.target = true := by
    simp only [coversOp, Bool.and_eq_true] at hcov
    exact hcov.1
  have hnew := newRow_eq k full op hc hd
  simp only [coversIntegrity, Bool.and_eq_true] at hint
  obtain ⟨⟨href, hcasc⟩, hafter⟩ := hint
  have hr : ∀ tk ∈ deletedRows schema k.rows op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing k.rows r ⟨tk.1, tk.2⟩ = referencing full r ⟨tk.1, tk.2⟩ := by
    intro tk htk r hr ht
    apply hfetch (r.table, Reference.filterOf r.column ⟨tk.1, tk.2⟩)
    simp only [integrityFilters, List.mem_append]
    right
    simp only [deleteFilters, List.mem_flatMap, List.mem_map]
    exact ⟨tk, htk, r, List.mem_filter.mpr ⟨hr, by simp [ht]⟩, rfl⟩
  obtain ⟨hplan, _⟩ := deletedRows_eq schema k.rows full op hr
  have hviol : integrityViolation schema k.rows op = integrityViolation schema full op := by
    unfold integrityViolation
    rw [uniqueViolation_eq schema k full op hnew
      (fun tf h => hfetch tf (by simp only [integrityFilters, List.mem_append]; exact Or.inl h)),
      referenceViolation_eq schema k full op hc hnew href, restrictViolation_eq schema k.rows full op hr]
  have hdplan : deletePlan schema k.rows op = deletePlan schema full op := by
    simp only [deletePlan, hplan]
  obtain ⟨hsome, hboth⟩ :=
    cascadeRun_eq_of_covers schema policies principal generated (deletePlan schema k.rows op) k full hc hcasc
  unfold stepOp
  rw [hperm, hviol]
  split
  · split
    · split
      · exact ⟨rfl, rfl⟩
      · cases h₁ : cascadeRun schema policies principal generated k.rows (deletePlan schema k.rows op) with
        | none =>
          cases h₂ : cascadeRun schema policies principal generated full (deletePlan schema full op) with
          | none => exact ⟨rfl, rfl⟩
          | some p =>
            have h₂' : cascadeRun schema policies principal generated full (deletePlan schema k.rows op) = some p := by
              rw [hdplan]; exact h₂
            rw [h₁, h₂'] at hsome; cases hsome
        | some p₁ =>
          obtain ⟨s₁, is₁⟩ := p₁
          cases h₂ : cascadeRun schema policies principal generated full (deletePlan schema full op) with
          | none =>
            have h₂' : cascadeRun schema policies principal generated full (deletePlan schema k.rows op) = none := by
              rw [hdplan]; exact h₂
            rw [h₁, h₂'] at hsome; cases hsome
          | some p₂ =>
            obtain ⟨s₂, is₂⟩ := p₂
            obtain ⟨hk', hcons, hmap⟩ := hboth s₁ is₁ s₂ is₂ h₁ (by rw [hdplan]; exact h₂)
            have hperm' : permits schema policies principal generated s₁ action op
                = permits schema policies principal generated s₂ action op := by
              rw [← hk']
              exact permits_eq_of_covers schema policies _ s₂ principal generated action op hcons hafter
            dsimp only
            rw [hperm']
            split
            · refine ⟨?_, ?_⟩
              · apply apply_snd_eq
                rw [← hk']
                exact Nyxis.Materials.Known.find?_eq_of_decided hcons
                  (Known.decided_removeAll _ k _ hd)
              · simp only [List.map_append, hmap, List.map_cons, List.map_nil]
            · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- 外部効果の記録のうち、判定時の状態を除いた部分(主体・生成値・アクション・対象・提案値・内容)。部分的な取得との
    一致はこの部分について述べる(記録の `store` は取得した状態と全体の状態で異なる)。 -/
def External.view (e : External) : Principal × Generated × EntityUID × Table × Key × Row × Payload :=
  (e.principal, e.generated, e.action, e.table, e.key, e.values, e.payload)

/-- 外部効果の内容は対象の行の `find?` だけで決まる。 -/
theorem payloadOf_eq (schema : Schema) (generated : Generated) (s₁ s₂ : Store) (effect : Nyxis.Db.Effect)
    (key : Key) (values : Row)
    (h : Cedar.Data.Map.find? s₁ (⟨effect.table, key⟩ : EntityUID) = Cedar.Data.Map.find? s₂ ⟨effect.table, key⟩) :
    payloadOf schema generated s₁ effect key values = payloadOf schema generated s₂ effect key values := by
  simp only [payloadOf, Store.find?, h]

/-- 効果の判定材料の操作の対象は、対象の行(テーブルと主キー)である。 -/
theorem ofEffect_target (effect : Nyxis.Db.Effect) (key : Key) (values : Row) :
    (Operation.ofEffect effect key values).target = ⟨effect.table, key⟩ := by
  unfold Operation.ofEffect
  split <;> first | rfl | (split <;> rfl)

/-- 部分的な取得での外部効果の処理の一致: 対象の行の有無が分かり、検査に通れば、結果・発行(無し)・外部効果の記録
    (状態を除く)は全体の状態でのものと一致する。 -/
theorem externalStep_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) (external : ExternalResult)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action (Operation.ofEffect effect key values) = true) :
    (externalStep schema policies principal generated k.rows action effect key values external).outcome
        = (externalStep schema policies principal generated full action effect key values external).outcome ∧
    (externalStep schema policies principal generated k.rows action effect key values external).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (externalStep schema policies principal generated full action effect key values external).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
    (externalStep schema policies principal generated k.rows action effect key values external).external.map
        External.view
        = (externalStep schema policies principal generated full action effect key values external).external.map
            External.view := by
  have hperm := permits_eq_of_covers schema policies k full principal generated action
    (Operation.ofEffect effect key values) hc hcov
  have hd : k.decided (Operation.ofEffect effect key values).target = true := by
    simp only [coversOp, Bool.and_eq_true] at hcov
    exact hcov.1
  have hfind := Nyxis.Materials.Known.find?_eq_of_decided hc hd
  rw [ofEffect_target] at hfind
  have hpay := payloadOf_eq schema generated k.rows full effect key values hfind
  unfold externalStep
  rw [hperm, hpay]
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **部分的な取得での `step` の一致**: 取得が全体の状態と整合し、検査(`coversStep`)に通り、判定が絞り込みで見る行
    (`rowFilters`: 一覧の候補、一意性の組と同じ値の行、削除する行を参照する行)をすべて取得しているなら、取得した行
    だけで処理した `step` の結果(ハンドラに渡る結果。一覧では返す行と件数、外部効果では同じ結果の値)と発行した操作
    (主体・生成値・アクション・操作)、外部効果の記録(主体・生成値・アクション・対象・内容)は、全体の状態で
    処理した `step` のものと一致する。発行と記録の `store` だけが取得した状態と全体の状態で異なる。 -/
theorem step_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (key : Key) (values : Row)
    (query : ListQuery) (external : ExternalResult)
    (hc : k.Consistent full)
    (hcov : coversStep schema policies k principal generated action key values query = true)
    (hfetch : ∀ tf ∈ rowFilters schema k.rows action key values query,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    (step schema policies principal generated k.rows action key values query external).outcome
        = (step schema policies principal generated full action key values query external).outcome ∧
    (step schema policies principal generated k.rows action key values query external).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (step schema policies principal generated full action key values query external).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
    (step schema policies principal generated k.rows action key values query external).external.map External.view
        = (step schema policies principal generated full action key values query external).external.map
            External.view := by
  unfold step coversStep rowFilters at *
  revert hcov hfetch
  cases heff : schema.effectOf action with
  | none => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | some effect =>
    intro hcov hfetch
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      dsimp only at hcov hfetch ⊢
      rw [permittedRows_eq_of_covers schema policies k full principal generated action table query hc
        (hfetch (table, query.filters) List.mem_cons_self) hcov]
      exact ⟨rfl, by simp only [List.map_map, Function.comp_def], rfl⟩
    case upload =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.upload, table⟩ key values
        external hc hcov
    case download =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.download, table⟩ key values
        external hc hcov
    case mail recipient content =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.mail recipient content, table⟩
        key values external hc hcov
    case call destination method target columns proposes mode =>
      exact externalStep_eq_of_covers schema policies k full principal generated action
        ⟨.call destination method target columns proposes mode, table⟩ key values external hc hcov
    all_goals
      dsimp only at hcov hfetch ⊢
      simp only [Bool.and_eq_true] at hcov
      obtain ⟨ho, hi⟩ := stepOp_eq_of_covers schema policies k full principal generated action _ _ hc hcov.1 hcov.2 hfetch
      exact ⟨ho, hi, by rw [stepOp_external, stepOp_external]⟩

end Nyxis.Authz
