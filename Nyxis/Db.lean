import Cedar.Spec
import Cedar.Validation

/-!
# Nyxis.Db — DB 層

Lean バックエンドが PostgreSQL に対して発行する DB 操作と、アクションに添えられる
「効果」の宣言、そして DB の状態の純粋モデル(`Store`)を定める。

- テーブルは Cedar のエンティティ型、列は属性、主キーはエンティティ ID に 1 対 1 で対応する。
  写像のコードは持たず、Cedar の型をそのまま使う。
- 効果は 1 アクションに 1 つ。種類(読み取り・一覧・挿入・更新・削除、および宣言された外部効果 — 添付の署名付き
  URL の発行 `upload` / `download`、メール送信 `mail`、外部 API 呼び出し `call`)と対象のテーブル、
  更新では列、メールでは宛先の列と件名・本文の列、外部 API 呼び出しでは送り先・メソッド・パス(または URL の列)・
  本文の列・実行時機を定める。
  一覧は、対象テーブルの各行についてそのアクションの判定を行い、permit された行だけを返す。DB 操作としては
  permit された行ごとの読み取りを発行する(`Nyxis.Authz.step`)。外部効果は DB 操作を発行せず、
  対象の行について permit されたときだけ外部効果(Supabase Storage への署名付き URL の発行、その行の宣言された列の
  値を宛先・内容とするメールの送信、正本で宣言した送り先への HTTP の呼び出し)を記録する
  (`Nyxis.Authz.External`)。オブジェクトのパスは nyxis が決め(`objectPath`)、宛先・内容・送り先・本文は正本の
  宣言と行の宣言された列(呼び出しでは `context.values` の提案値も)から決まり、ハンドラは名指しできない。
- DB 操作は認可層(`Nyxis.Authz`)が permit のときだけ発行する。ハンドラはこの層に触れない。
- `Store` は PostgreSQL の内容を抽象した純粋モデルで、認可安全性の定理(`Nyxis.Runtime`)はこの上で述べる。
  DB が nyxis の発行する操作以外で変わらないこと(DB へは nyxis 専用ロール以外から到達できないこと)と、
  操作を PostgreSQL に伝えるランタイムが正しいことは、証明の外側で信頼する(`ASSUMPTIONS.md`)。
-/

namespace Nyxis

open Cedar.Spec

namespace Db

/-- テーブル名。Cedar のエンティティ型に 1 対 1 で対応する。 -/
abbrev Table := EntityType

/-- 列名。Cedar の属性に 1 対 1 で対応する。 -/
abbrev Column := Attr

/-- 行の主キー。Cedar のエンティティ ID に 1 対 1 で対応する。 -/
abbrev Key := String

/-- 列の値。Cedar の値をそのまま使う。 -/
abbrev Cell := Value

/-- 行の内容。列名から値への写像。 -/
abbrev Row := Cedar.Data.Map Column Cell

/-- 行に変更を重ねる。変更にある列は新しい値、無い列は元の値。 -/
def Row.patch (row changes : Row) : Row :=
  Cedar.Data.Map.make (changes.toList ++ row.toList.filter (fun kv => !changes.contains kv.1))

/-! ## 外部 API 呼び出しの宣言

正本は名前付きの送り先(`@external` を添えた予約の仲間 `entity Stripe;`。テーブルではない)を宣言し、効果
`@effect("call <送り先> <メソッド> <パス | url: 列> T(列, …) (sync [<秒>s] -> <レコード型> | async)")` で呼び出しを
宣言する。送り先はベース URL(`base`。無ければ対象行の String 列の値を `url: 列` で送り先にする — 旧 Webhook の形)と
認証方式(環境変数名だけが正本に載り、値はコア設定)を持つ。ハンドラは URL もヘッダも組めない。 -/

/-- 呼び出しの HTTP メソッド。 -/
inductive CallMethod where
  | get
  | post
  | put
  | patch
  | delete
  deriving Repr, DecidableEq

/-- HTTP 上の名前。 -/
def CallMethod.name : CallMethod → String
  | .get => "GET"
  | .post => "POST"
  | .put => "PUT"
  | .patch => "PATCH"
  | .delete => "DELETE"

/-- 本文を送るメソッドか(`GET` / `DELETE` では本文を送らない)。 -/
def CallMethod.hasBody : CallMethod → Bool
  | .get | .delete => false
  | .post | .put | .patch => true

/-- 送り先の認証方式。環境変数名だけが正本に載り、値はコア設定(`NYXIS_EXT_<名前>`)で渡す。 -/
inductive DestinationAuth where
  /-- 認証ヘッダを付けない。 -/
  | none
  /-- `Authorization: Bearer <環境変数の値>`。 -/
  | bearer (env : String)
  /-- 任意の 1 ヘッダ `<name>: <環境変数の値>`。 -/
  | header (name env : String)
  deriving Repr, DecidableEq

/-- 名前付きの送り先(`@external`)。`base` は `https://` で始まる固定のベース URL(末尾の `/` は無い)。`base` の無い
    送り先は `url: 列` の呼び出しでだけ使える。 -/
structure Destination where
  base : Option String
  auth : DestinationAuth
  deriving Repr, DecidableEq

/-- 呼び出しの送り先の決め方。 -/
inductive CallTarget where
  /-- 送り先のベース URL に続ける固定のパス。`{key}` だけを対象行の主キーで埋める。 -/
  | path (path : String)
  /-- 対象行の String 列の値(`https://` で始まるもの)を URL にする(`url: 列`)。送り先に `base` は無い。 -/
  | column (url : Column)
  deriving Repr, DecidableEq

/-- 実行時機。`sync` は要求のトランザクション内で同期に送り、応答を正本で宣言したレコード型に復号してハンドラへ渡す
    (`timeout` は全転送の上限(秒)の上書き)。`async` は応答なしでアウトボックス(`_nyxis_outbox`)に書いて
    COMMIT の後に nyxis の内部ループが送る。 -/
inductive CallMode where
  | sync (timeout : Option Nat) (response : Cedar.Validation.CedarType)
  | async
  deriving Repr, DecidableEq

/-- アクションの効果の種類。更新では変更してよい列を定める。
    一覧(`list`)は、対象テーブルの各行についてそのアクションの判定を行い、permit された行だけを返す。
    `upload` / `download`は対象の行への添付の署名付きアップロード / ダウンロード URL の発行で、DB を変えない
    宣言された外部効果。オブジェクトのパスは `objectPath`(`テーブル/<主キー>/<生成 ID>`、ダウンロードでは正本が
    `@attachment("列")` で名指しした列の値)で nyxis が決める。
    `mail`は対象の行の宣言された列の値を宛先(`recipient`。メールアドレスの String 列)と内容(`content`: 先頭が
    件名、残りが本文の段落。String 列)とするメールの送信。
    `call`は正本で宣言した送り先 `destination` への HTTP の呼び出し: メソッド、送り先の決め方(ベース URL に続ける
    固定のパス、または対象行の URL の列)、本文に載せる対象行の列 `columns`、`context.values` の提案値も本文に混ぜて
    判定の文脈に置くか(`proposes`。正本のアクションの `context` が `values` を宣言したとき)、実行時機 `mode`。
    どれも DB を変えない宣言された外部効果で、宛先・内容・送り先・本文はすべて正本の宣言と行の列(と判定を通った提案値)
    から決まり、ハンドラは選べない。 -/
inductive EffectKind where
  | read
  | list
  | insert
  | update (columns : List Column)
  | delete
  | upload
  | download
  | mail (recipient : Column) (content : List Column)
  | call (destination : String) (method : CallMethod) (target : CallTarget) (columns : List Column) (proposes : Bool)
      (mode : CallMode)
  deriving Repr, DecidableEq

/-- 宣言された外部効果の種類か。 -/
def EffectKind.isExternal : EffectKind → Bool
  | .upload | .download | .mail _ _ | .call .. => true
  | .read | .list | .insert | .update _ | .delete => false

/-- アクションに添えられる効果の宣言。1 アクションに 1 つ。 -/
structure Effect where
  kind : EffectKind
  table : Table
  deriving Repr, DecidableEq

/-- DB 操作。Lean バックエンドが PostgreSQL に対して発行する読み取り・挿入・更新・削除。
    一覧は、permit された行ごとの読み取りとして発行される(一覧だけの操作は無い)。 -/
inductive Operation where
  | read (table : Table) (key : Key)
  | insert (table : Table) (key : Key) (row : Row)
  | update (table : Table) (key : Key) (changes : Row)
  | delete (table : Table) (key : Key)

/-- 操作の対象(テーブルと主キー)。Cedar の対象のエンティティ UID になる。 -/
def Operation.target : Operation → EntityUID
  | .read t k | .insert t k _ | .update t k _ | .delete t k => ⟨t, k⟩

/-- 操作が提案する値。挿入では行全体、更新では変更する列、読み取りと削除では無し。 -/
def Operation.proposed : Operation → Option Row
  | .insert _ _ row => some row
  | .update _ _ changes => some changes
  | .read _ _ | .delete _ _ => none

/-- 効果の宣言から、主キー `key` と提案する値 `values` に対する DB 操作を組み立てる。
    操作の種類とテーブルは効果が決め、ハンドラは選べない。一覧の効果は `Nyxis.Authz.step` が先に行ごとに
    扱う(各行の主キーについて、その行の読み取り)ので、ここの `.list` の分岐には到達しない。関数を全域に
    するために置いてある。
    外部効果では、この操作は判定材料(主体・対象の行・文脈)を組むためにだけ使い、DB 操作としては
    発行されない(`Nyxis.Authz.externalStep`): 対象の行の読み取りと同じ判定材料で、`context.values` の提案値を取る
    呼び出し(`call` の `proposes`)では提案値を文脈に置くために更新の形(対象の行と提案値)で組む。 -/
def Operation.ofEffect (e : Effect) (key : Key) (values : Row) : Operation :=
  match e.kind with
  | .read => .read e.table key
  | .list => .read e.table key
  | .insert => .insert e.table key values
  | .update _ => .update e.table key values
  | .delete => .delete e.table key
  | .upload => .read e.table key
  | .download => .read e.table key
  | .mail _ _ => .read e.table key
  | .call _ _ _ _ proposes _ => if proposes then .update e.table key values else .read e.table key

/-- DB 操作が効果の宣言の範囲内にあるか。種類とテーブルが一致し、更新では変更する列が宣言された列に収まる。
    一覧の効果の範囲内にあるのは、そのテーブルの行の読み取りだけ。 -/
def Operation.withinEffect (op : Operation) (e : Effect) : Bool :=
  match op, e.kind with
  | .read t _, .read => t == e.table
  | .read t _, .list => t == e.table
  | .insert t _ _, .insert => t == e.table
  | .update t _ changes, .update cols =>
    t == e.table && changes.toList.all (fun kv => cols.contains kv.1)
  | .delete t _, .delete => t == e.table
  | _, _ => false

/-! ## 添付のオブジェクトのパス

署名付き URL の発行の対象になる Supabase Storage のオブジェクトのパスは、nyxis が `テーブル/<主キー>/<オブジェクトの名>`
の形で決める。オブジェクトの名は、アップロードでは要求のサーバー生成値の一意 ID、ダウンロードでは正本が
`@attachment("列")` で名指しした String 列の現在の値。主キーと名はいずれも英数字・`-`・`_` だけ(1〜128 文字。
パスの区切りや `..` を含まない)でなければならず、そうでなければパスは決まらない(ハンドラには `Outcome.notFound`)。
ハンドラはパスもバケットも名指しできない。 -/

/-- オブジェクトのパスの要素として使える文字列か(ASCII の英数字・`-`・`_`、1〜128 文字)。 -/
def isObjectToken (s : String) : Bool :=
  s.length > 0 && s.length ≤ 128 &&
    s.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')

/-- オブジェクトのパス `テーブル/<主キー>/<名>`。主キーか名が要素として使えなければ `none`。 -/
def objectPath (table : Table) (key : Key) (token : String) : Option String :=
  if isObjectToken key && isObjectToken token then some (table.id ++ "/" ++ key ++ "/" ++ token) else none

/-! ## 外部 API 呼び出しの URL

送り先の URL は、ベース URL(正本の `@external` の `base`)に正本が書いた固定のパスを続けたもの、または対象行の
String 列の値(`url: 列`)である。パスの `{key}` だけを対象行の主キーで埋め、主キーはパスの要素として使える文字列
(`isObjectToken`)でなければならない。`url: 列` の値は `https://` で始まる印字可能な ASCII でなければならない。
どちらも決まらなければ呼び出しの内容は決まらない(ハンドラには `Outcome.notFound`)。 -/

/-- 送り先の URL として使える文字列か: `https://` で始まり、印字可能な ASCII で、`"`・`\`・`#`・空白を含まない
    (〜2048 文字)。 -/
def isHttpsUrl (url : String) : Bool :=
  url.startsWith "https://" && url.length > 8 && url.length ≤ 2048 &&
    url.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\' && c != '#'

/-- パスの `{key}` を主キーで埋める。`{key}` があれば主キーはパスの要素として使える文字列でなければならない
    (そうでなければ `none`)。他の埋め込みは無い(正本の検査が `{key}` 以外のプレースホルダを拒む)。 -/
def fillPath (path : String) (key : Key) : Option String :=
  match path.splitOn "{key}" with
  | [_] => some path
  | parts => if isObjectToken key then some (key.intercalate parts) else none

/-- 呼び出しの URL: 固定のパスなら送り先のベース URL に埋めたパスを続け、`url: 列` なら対象行のその列の値
    (`isHttpsUrl` に限る)。送り先の形と宣言の形が合わなければ `none`(正本の検査が拒むので正本からは生じない)。 -/
def callUrl (destination : Destination) (target : CallTarget) (key : Key) (row : Row) : Option String :=
  match target, destination.base with
  | .path p, some base => (fillPath p key).map (base ++ ·)
  | .column c, none =>
    match row.find? c with
    | some (.prim (.string url)) => if isHttpsUrl url then some url else none
    | _ => none
  | .path _, none | .column _, some _ => none

/-! ## 一覧の問い合わせ

ハンドラは一覧に、列の値と定数の比較による絞り込み(等値・大小)、並べ替え、ページ(位置と上限)を指定できる。
絞り込みは判定の前に(実 DB では SELECT の WHERE 句で)行い、並べ替えとページは permit された行に対して行う。
件数(`Outcome.list` の `total`)は、絞り込みに合い permit された行の数で、ページを切る前のもの。 -/

/-- 絞り込みの比較。 -/
inductive Comparison where
  | eq
  | lt
  | le
  | gt
  | ge
  deriving Repr, DecidableEq

/-- 比較が順序を受け入れるか(`lt` は `.lt` だけ、`le` は `.lt` と `.eq`、…)。 -/
def Comparison.accepts : Comparison → Ordering → Bool
  | .eq, .eq | .lt, .lt | .le, .lt | .le, .eq | .gt, .gt | .ge, .gt | .ge, .eq => true
  | _, _ => false

/-- 一覧の絞り込み: 列 `column` の値と定数 `value` の比較。 -/
structure Filter where
  column : Column
  comparison : Comparison
  value : Cell
  deriving Repr, DecidableEq

/-- 並べ替えの向き。 -/
inductive Direction where
  | asc
  | desc
  deriving Repr, DecidableEq

/-- 並べ替えの 1 段: 列と向き。 -/
structure OrderBy where
  column : Column
  direction : Direction := .asc
  deriving Repr

/-- ハンドラが一覧に指定する問い合わせ。絞り込みはすべての条件を満たす行(AND)、並べ替えは先頭の段から順に
    (同じなら次の段、すべて同じなら主キーの順)、ページは並べ替えた permit 済みの行列の `offset` 番目から
    `limit` 件(`none` なら最後まで)。 -/
structure ListQuery where
  filters : List Filter := []
  orderBy : List OrderBy := []
  offset : Nat := 0
  limit : Option Nat := none
  deriving Repr

/-- スカラーの値の順序。同じ種類の整数・文字列・真偽値・日時・期間・decimal だけを比べ、種類が違う値と集合・
    レコードは比べられない(`none`)。文字列はコードポイントの順(実 DB の "C" 照合と同じ)。 -/
def Cell.compare? : Cell → Cell → Option Ordering
  | .prim (.int a), .prim (.int b) => some (compareOfLessAndEq a b)
  | .prim (.string a), .prim (.string b) => some (compareOfLessAndEq a b)
  | .prim (.bool a), .prim (.bool b) => some (compareOfLessAndEq a b)
  | .ext (.datetime a), .ext (.datetime b) => some (compareOfLessAndEq a.val b.val)
  | .ext (.duration a), .ext (.duration b) => some (compareOfLessAndEq a.val b.val)
  | .ext (.decimal a), .ext (.decimal b) => some (compareOfLessAndEq a b)
  | _, _ => none

/-- 行が絞り込みに合うか。列が無ければ合わない。等値は値そのものの一致、大小は `Cell.compare?` の順序
    (比べられなければ合わない)。 -/
def Filter.matches (f : Filter) (row : Row) : Bool :=
  match row.find? f.column with
  | none => false
  | some v =>
    match f.comparison with
    | .eq => v == f.value
    | c =>
      match Cell.compare? v f.value with
      | some o => c.accepts o
      | none => false

/-- 行がすべての絞り込みに合うか。 -/
def ListQuery.matches (q : ListQuery) (row : Row) : Bool :=
  q.filters.all (·.matches row)

/-- 1 段の並べ替えで 2 行を比べる。列の無い行は先に来る。比べられない値は同じとみなす。 -/
def OrderBy.compare (o : OrderBy) (a b : Row) : Ordering :=
  let r := match a.find? o.column, b.find? o.column with
    | some x, some y => (Cell.compare? x y).getD .eq
    | some _, none => .gt
    | none, some _ => .lt
    | none, none => .eq
  match o.direction with
  | .asc => r
  | .desc => r.swap

/-- 並べ替えの順序(`a` が `b` より前か同じ)。すべての段で同じなら主キーの順。 -/
def ListQuery.le (q : ListQuery) (a b : Key × Row) : Bool :=
  go q.orderBy
where
  go : List OrderBy → Bool
    | [] => decide (a.1 < b.1) || a.1 == b.1
    | o :: rest =>
      match o.compare a.2 b.2 with
      | .lt => true
      | .gt => false
      | .eq => go rest

/-- permit 済みの行列から返す行を選ぶ: 並べ替えて(`List.mergeSort`。安定)、`offset` 番目から `limit` 件。 -/
def ListQuery.select (q : ListQuery) (rows : List (Key × Row)) : List (Key × Row) :=
  let sorted := rows.mergeSort q.le
  (sorted.drop q.offset).take (q.limit.getD sorted.length)

/-- 返す行はすべて、選ぶ前の行列にある(並べ替えとページは行を増やさない)。 -/
theorem ListQuery.mem_select (q : ListQuery) (rows : List (Key × Row)) (kv : Key × Row)
    (h : kv ∈ q.select rows) : kv ∈ rows :=
  List.mem_mergeSort.mp (List.mem_of_mem_drop (List.mem_of_mem_take h))

/-- 行がすべての絞り込みに合うか(`ListQuery.matches` と同じ規則。絞り込みの列だけで決まる)。 -/
def Filter.matchesAll (filters : List Filter) (row : Row) : Bool :=
  filters.all (·.matches row)

/-! ## 一意性と参照整合の宣言

正本が宣言する DB の制約。`@unique("列, …")` は列の組の一意性(組のどれかの列が無い行は比べない。PostgreSQL の
`UNIQUE` の NULL と同じ)、`@references("列 restrict, 列 cascade アクション, …")` は実体参照の列の参照整合
(参照先の行が無い挿入・更新は競合。参照される行の削除は、`restrict` なら参照する行があれば競合、`cascade` なら
参照する行も消える — その各行はそのテーブルの削除効果を持つ宣言済みアクションで判定され、1 行でも permit され
なければ要求全体が拒否される)。nyxis は同じ制約を DB にも設定し(`PostgresSql.createTable`)、判定はモデル
(`Nyxis.Authz.step`)が先に行う(違反は `Outcome.conflict`)。DB 側の制約は判定が外れたときの裏付けで、
そのときは要求全体が閉じる。 -/

/-- 列の組の一意性の宣言。 -/
structure Unique where
  table : Table
  columns : List Column
  deriving Repr, DecidableEq

/-- 参照される行を削除するときの振る舞い。`cascade` は参照する行を判定するアクション(そのテーブルの削除効果)。 -/
inductive OnDelete where
  | restrict
  | cascade (action : EntityUID)
  deriving Repr, DecidableEq

/-- 実体参照の列の参照整合の宣言: 参照する側のテーブルと列、参照される側のテーブル、削除時の振る舞い。 -/
structure Reference where
  table : Table
  column : Column
  target : Table
  onDelete : OnDelete
  deriving Repr, DecidableEq

/-- スキーマが宣言する制約。 -/
structure Constraints where
  uniques : List Unique := []
  references : List Reference := []
  deriving Repr, DecidableEq

/-- 一意性の組の絞り込み: 行 `new` の列の値との等値。`new` に組の列が 1 つでも無ければ比べない(`none`)。 -/
def Unique.filtersOf (u : Unique) (new : Row) : Option (List Filter) :=
  u.columns.mapM fun c => (new.find? c).map fun v => ⟨c, .eq, v⟩

/-- 実体 `uid` を列 `column` で参照する行の絞り込み。 -/
def Reference.filterOf (column : Column) (uid : EntityUID) : List Filter :=
  [⟨column, .eq, .prim (.entityUID uid)⟩]

end Db

/-- アクション呼び出しの結果。`denied` は認可層が、`notFound` / `conflict` / `ok` は DB 層が決める。 -/
inductive Outcome where
  /-- 認可層が拒否した(効果の宣言が無い・操作が効果の範囲外・Cedar が deny)。DB 操作は発行されていない。 -/
  | denied
  /-- 行が無い(読み取り・更新・削除)。 -/
  | notFound
  /-- 行が既にある(挿入)。 -/
  | conflict
  /-- 成功。読み取りではその行、書き込み(挿入・更新・削除)では `none`。
      書き込みの効果で行を返すと、宣言された効果(更新では列)を超えた読み取りになるので返さない。 -/
  | ok (row : Option Db.Row)
  /-- 一覧の成功。対象テーブルの行のうち絞り込みに合い、その主体にそのアクションが permit された行(`total` はその数)
      を並べ替えてページを切ったものを、主キーと共に返す。 -/
  | list (rows : List (Db.Key × Db.Row)) (total : Nat)
  /-- 外部効果(添付の署名付き URL の発行)の成功。Supabase Storage が発行した署名付き URL。行は渡らない。
      純粋モデルではこの値は要求の外部効果の結果の列(`Nyxis.Runtime.Externals`)から来る任意の文字列で、定理は
      その発行の記録(`Nyxis.Authz.External`)が認可済みであることを述べる(主定理の (6)(7))。
      メール送信と `async` の呼び出しの成功は `ok none`(送信の結果は値を持たず、DB も変えない)。 -/
  | signed (url : String)
  /-- `sync` の外部 API 呼び出しの 2xx の応答を、正本で宣言したレコード型に(宣言したキーの欠落と型違いだけを
      拒み、余分なキーは捨てて)復号した値。行は渡らない。純粋モデルではこの値は要求の外部効果の結果の列から来る
      任意の値で、定理はその呼び出しの記録が認可済みであること(主定理の (6)(8))と、値がその呼び出しの記録に由来し
      判定を変えないこと((9))を述べる。 -/
  | called (value : Value)
  /-- `sync` の外部 API 呼び出しの 2xx 以外の応答。状態コードと生の本文(ハンドラが業務上の失敗として扱う)。 -/
  | calledError (status : Nat) (body : String)

/-- 結果がハンドラに渡す(主キー, 行)の組。読み取りの成功では呼び出しの主キー `key` とその行、一覧では返す
    各組、それ以外は無い。定理はこの組の出所について述べる(`Nyxis.Runtime.authorization_safety` の (3))。 -/
def Outcome.entries (key : Db.Key) : Outcome → List (Db.Key × Db.Row)
  | .ok (some row) => [(key, row)]
  | .list rows _ => rows
  | .ok none | .denied | .notFound | .conflict | .signed _ | .called _ | .calledError _ _ => []

/-- 外部効果の結果の値を持つ結果か(署名付き URL、呼び出しの応答)。こうした結果は外部効果の処理でだけ生じる
    (主定理の (7)(9))。 -/
def Outcome.isExternal : Outcome → Bool
  | .signed _ | .called _ | .calledError _ _ => true
  | .ok _ | .denied | .notFound | .conflict | .list _ _ => false

/-- 外部 API 呼び出しの応答か(`called` / `calledError`)。 -/
def Outcome.isCalled : Outcome → Bool
  | .called _ | .calledError _ _ => true
  | .ok _ | .denied | .notFound | .conflict | .list _ _ | .signed _ => false

namespace Db

/-- DB の状態の純粋モデル。(テーブル, 主キー) = エンティティ UID から行への有限写像。 -/
abbrev Store := Cedar.Data.Map EntityUID Row

namespace Store

/-- テーブル `table` の主キー `key` の行。 -/
def find? (s : Store) (table : Table) (key : Key) : Option Row :=
  Cedar.Data.Map.find? s ⟨table, key⟩

/-- 行を置く。既にあれば置き換える。 -/
def put (s : Store) (table : Table) (key : Key) (row : Row) : Store :=
  Cedar.Data.Map.make
    (((⟨table, key⟩ : EntityUID), row) :: s.toList.filter (fun kv => kv.1 != (⟨table, key⟩ : EntityUID)))

/-- 行を消す。 -/
def remove (s : Store) (table : Table) (key : Key) : Store :=
  Cedar.Data.Map.filter (fun uid _ => uid != (⟨table, key⟩ : EntityUID)) s

/-- テーブル `table` の現在の全行(主キーと行)。主キーは現在の状態にある行のものを順に取り、行はその主キーで
    `find?` を引く(読み取りの操作 `apply (.read …)` と同じ経路)。一覧はこの各行について判定する。 -/
def rows (s : Store) (table : Table) : List (Key × Row) :=
  (s.toList.filterMap fun kv => if kv.1.ty == table then some kv.1.eid else none).filterMap
    fun key => (s.find? table key).map (key, ·)

/-- `rows` が返す各行は、その主キーで `find?` を引いた現在の行である。 -/
theorem rows_find? (s : Store) (table : Table) (key : Key) (row : Row)
    (h : (key, row) ∈ s.rows table) : s.find? table key = some row := by
  simp only [rows, List.mem_filterMap] at h
  obtain ⟨k, _, hk⟩ := h
  cases hf : s.find? table k <;> simp only [hf, Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact hf

/-- DB 操作を適用する。新しい状態と、ハンドラに返す結果。 -/
def apply (s : Store) : Operation → Store × Outcome
  | .read t k =>
    match s.find? t k with
    | some row => (s, .ok (some row))
    | none => (s, .notFound)
  | .insert t k row =>
    match s.find? t k with
    | some _ => (s, .conflict)
    | none => (s.put t k row, .ok none)
  | .update t k changes =>
    match s.find? t k with
    | some row => (s.put t k (row.patch changes), .ok none)
    | none => (s, .notFound)
  | .delete t k =>
    match s.find? t k with
    | some _ => (s.remove t k, .ok none)
    | none => (s, .notFound)

/-- 読み取りは DB の状態を変えない。 -/
theorem apply_read_fst (s : Store) (table : Table) (key : Key) :
    (s.apply (.read table key)).1 = s := by
  simp only [apply]
  split <;> rfl

/-- 行の操作の結果は一覧の結果ではない(一覧の結果は `Nyxis.Authz.step` が一覧の効果でだけ作る)。 -/
theorem apply_snd_ne_list (s : Store) (op : Operation) (rows : List (Key × Row)) (total : Nat) :
    (s.apply op).2 ≠ .list rows total := by
  cases op <;> simp only [apply] <;> split <;> simp

/-- 行の操作の結果は外部効果の結果ではない(署名付き URL と呼び出しの応答は `Nyxis.Authz.step` が外部効果でだけ
    渡す)。 -/
theorem apply_snd_isExternal (s : Store) (op : Operation) :
    (s.apply op).2.isExternal = false := by
  cases op <;> simp only [apply] <;> split <;> rfl

/-- 行を含む結果は、同じ直前状態の主キー読み取りだけから生じる: 結果が渡す行は、操作が読み取りで、
    その主キーで `find?` を引いた現在の行である。書き込みに渡した値や既存行が結果として返ることはない。 -/
theorem apply_row (s : Store) (op : Operation) (row : Row)
    (h : (s.apply op).2 = .ok (some row)) :
    ∃ table key, op = .read table key ∧ s.find? table key = some row := by
  cases op <;> simp only [apply] at h
  all_goals split at h <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, by assumption⟩

/-- 結果が渡す(主キー, 行)の組は、操作が読み取りのときだけ生じ、主キーは `entries` に渡した呼び出しの主キー、
    行はその読み取りの主キーで `find?` を引いた現在の行である(一覧の結果は `apply` からは生じない)。 -/
theorem apply_entries (s : Store) (op : Operation) (key : Key) (kv : Key × Row)
    (h : kv ∈ (s.apply op).2.entries key) :
    ∃ table readKey, op = .read table readKey ∧ kv.1 = key ∧ s.find? table readKey = some kv.2 := by
  cases op <;> simp only [apply] at h
  all_goals split at h <;> simp only [Outcome.entries, List.mem_singleton, List.not_mem_nil] at h
  subst h
  exact ⟨_, _, rfl, rfl, by assumption⟩

end Store

end Db

end Nyxis
