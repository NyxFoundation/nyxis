import Nyxis.Authz
import Nyxis.Internal.PostgresValue

/-! アプリケーションのための内部の SQL の計画(A4。定理の外)。ここでは SQL を実行しない。
識別子はスキーマから、値はパラメータからだけ来る。エンティティ型は名前空間の無いものを使う。
名前空間つきの型は、その DB の配置が定まるまで拒む。
NULL を許す JSONB の列が属性の欠落を表す。SQL の NULL は Cedar のセルではない。
-/
namespace Nyxis.Internal.PostgresSql
open Nyxis Db Cedar.Spec

structure Command where
  sql : String
  parameters : Array String
  deriving BEq, Repr

private def invalid : Except String α := .error "Unsupported PostgreSQL schema or operation"

/-- PostgreSQL は 63 バイトを超える識別子を切り詰める。2 つの名前が同じになるより拒む。 -/
private def identifier (s : String) : Except String String :=
  if s.isEmpty || s.contains '\x00' || s.utf8ByteSize > 63 then invalid
  else .ok ("\"" ++ s.replace "\"" "\"\"" ++ "\"")

private def keyColumn := "_nyxis_id"

/-- nyxis の予約テーブルの名前(アウトボックス)。正本のテーブルにはこの名前を使えない。 -/
def outboxTable : String := "_nyxis_outbox"

private def layout (schema : Authz.Schema) (table : Table) :
    Except String (String × List Column) := do
  if !table.path.isEmpty || table.id == outboxTable then invalid else do
    let entries := schema.tables.filter (fun entry => entry.1 == table)
    let [(_, columns)] := entries | invalid
    if columns.contains keyColumn || columns.eraseDups != columns then invalid else do
      let _ ← columns.mapM identifier
      let name ← identifier table.id
      -- 明示的に修飾して、接続の search_path に依存しない。
      return ("\"public\"." ++ name, columns)

private def keyParam (key : Key) : Except String String :=
  if key.contains '\x00' then invalid else .ok key

private def cells (columns : List Column) (row : Row) :
    Except String (List (String × String)) :=
  row.toList.mapM fun (column, value) => do
    if !columns.contains column then invalid else do
      return (← identifier column, ← PostgresValue.encode value)

private def join (parts : List String) := String.intercalate ", " parts
private def keySql := "\"_nyxis_id\""

/-- 参照の列の保存形式の ID を持つ生成列の名前。 -/
def refColumn (column : Column) : String := "_nyxis_ref_" ++ column

/-- 用意のための計画だけ。IF NOT EXISTS は使わず、一致しない既存のテーブルを黙って受け入れない。
制約: 一意性の組は `UNIQUE (列, …)`(NULL = 属性の欠落は比べない。モデル `Authz.uniqueViolation` と同じ)。
参照整合の列には保存形式 `["entity", 名前空間, 型, ID]` の ID(`列 ->> 3`)を持つ生成列を置き、外部キーは
`foreignKeys` が全テーブルの後に付ける。これらは判定(モデル)の裏付けで、判定が外れていれば SQL が失敗して要求全体が閉じる。 -/
def createTable (schema : Authz.Schema) (table : Table) : Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM fun c => return (← identifier c) ++ " jsonb"
  let refs ← (schema.constraints.references.filter (·.table == table)).mapM fun r => do
    if !columns.contains r.column then invalid else
    return (← identifier (refColumn r.column)) ++ " text COLLATE \"C\" GENERATED ALWAYS AS (" ++
      (← identifier r.column) ++ " ->> 3) STORED"
  let uniques ← (schema.constraints.uniques.filter (·.table == table)).mapM fun u => do
    if u.columns.isEmpty || u.columns.eraseDups != u.columns then invalid else
    let cols ← u.columns.mapM fun c => if !columns.contains c then invalid else identifier c
    return "UNIQUE (" ++ join cols ++ ")"
  return ⟨"CREATE TABLE " ++ name ++ " (" ++
    join ((keySql ++ " text COLLATE \"C\" PRIMARY KEY") :: fields ++ refs ++ uniques) ++ ")", #[]⟩

/-- 参照整合の外部キー: 生成列から参照先の主キーへ、削除は RESTRICT(連鎖はモデルが判定して明示的に発行する。
DB の制約はその裏付け)。参照する側の生成列には索引を作る(参照する行の取得 — 削除の restrict / cascade の判定材料 — が
参照する側のテーブル全体の大きさに依存しないため)。全テーブルの `createTable` の後に発行する。
各コマンドに期待するコマンドタグを添える。 -/
def foreignKeys (schema : Authz.Schema) : Except String (List (Command × String)) := do
  let commands ← schema.constraints.references.mapM fun r => do
    let (name, columns) ← layout schema r.table
    let (target, _) ← layout schema r.target
    if !columns.contains r.column then invalid else
    let constraint ← identifier (r.table.id ++ "_" ++ r.column ++ "_fkey")
    let index ← identifier (r.table.id ++ "_" ++ r.column ++ "_ref_idx")
    let ref ← identifier (refColumn r.column)
    return [ (⟨"ALTER TABLE " ++ name ++ " ADD CONSTRAINT " ++ constraint ++ " FOREIGN KEY (" ++ ref ++
        ") REFERENCES " ++ target ++ " (" ++ keySql ++ ") ON DELETE RESTRICT", #[]⟩, "ALTER TABLE")
      , (⟨"CREATE INDEX " ++ index ++ " ON " ++ name ++ " (" ++ ref ++ ")", #[]⟩, "CREATE INDEX") ]
  return commands.flatten

/-- 予約テーブル `_nyxis_outbox` の修飾名。 -/
def outboxName : String := "\"public\".\"" ++ outboxTable ++ "\""

/-- nyxis の予約テーブル `_nyxis_outbox`(アウトボックス)の用意。形は `docs/external-calls.md` §4.3 に固定
(列と状態 `pending` / `sent` / `failed`)。正本のテーブルではなく、`Authz.Schema.tables`
に無いのでアプリのハンドラ・ポリシーからは到達できない。`async` の呼び出しの記録(`Nyxis.Internal.Outbox.enqueue`)が要求の
トランザクションで 1 行書き、内部ループ(`Outbox.loop`)が `pending` の行を送る。期限の来た `pending` の行だけを引く部分索引で、
ループの各回のコストは送信済み・失敗の行の数に依存しない。全テーブルの後に、各コマンドに期待するタグを添えて出す。 -/
def outbox : List (Command × String) :=
  [ (⟨"CREATE TABLE " ++ outboxName ++ " (" ++ join
        [ keySql ++ " text COLLATE \"C\" PRIMARY KEY"
        , "\"principal\" text NOT NULL", "\"action\" text NOT NULL", "\"target\" text NOT NULL"
        , "\"destination\" text NOT NULL", "\"method\" text NOT NULL", "\"url\" text NOT NULL", "\"body\" jsonb"
        , "\"state\" text NOT NULL CHECK (\"state\" IN ('pending', 'sent', 'failed'))"
        , "\"attempts\" integer NOT NULL DEFAULT 0", "\"next_at\" timestamptz NOT NULL"
        , "\"last_status\" integer", "\"last_error\" text"
        , "\"created_at\" timestamptz NOT NULL", "\"sent_at\" timestamptz" ] ++ ")", #[]⟩, "CREATE TABLE")
  , (⟨"CREATE INDEX \"" ++ outboxTable ++ "_pending_idx\" ON " ++ outboxName ++
        " (\"next_at\") WHERE \"state\" = 'pending'", #[]⟩, "CREATE INDEX") ]

/-- SERIALIZABLE トランザクションの中で現在の Cedar の実体を構成するための、スナップショットの計画。
これは内部の認可の材料であり、ハンドラへの未選別の応答ではない。 -/
def selectTable (schema : Authz.Schema) (table : Table) : Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM identifier
  return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name, #[]⟩

/-- 一覧の絞り込み 1 つの SQL の条件。モデル `Nyxis.Db.Filter.matches` と同じ規則:
- 等値は保存形式(正規形の JSONB)の値そのものの一致 `列 = $n::jsonb`。
- 大小は、保存形式のタグ(`列->>0`)が問い合わせの値の種類と一致するときだけ本文(`列->>1`)を比べる(`CASE` で
  タグを先に見るので、種類の違う列の本文を数値に変換しない)。整数・decimal・日時・期間は数値、文字列は "C" 照合
  (コードポイントの順)、真偽値は boolean。集合・レコード・実体参照の大小は拒む。
- 列が NULL(属性の欠落)なら合わない(どちらの条件も NULL / false になる)。
- 等値の定数が保存形式にできない値(NUL を含む文字列、`ipaddr`、入れ子の集合、正規形でない集合・レコードなど)
  なら、保存された行がその値に等しいことはない(保存形式は nyxis の符号化を通った値だけ。A3)ので、条件は定数
  `false`(モデルの `v == f.value` も偽)。大小の定数が NUL を含めば拒む(モデルでは比べられるので、閉じる側に倒す)。
識別子は正本の列から、値はパラメータからだけ来る。`index` は次に使うパラメータの番号。 -/
private def filterSql (columns : List Column) (index : Nat) (f : Filter) :
    Except String (String × List String) := do
  if !columns.contains f.column then invalid
  let column ← identifier f.column
  match f.comparison with
  | .eq =>
    match PostgresValue.encode f.value with
    | .ok stored => return (column ++ " = $" ++ toString index ++ "::jsonb", [stored])
    | .error _ => return ("false", [])
  | comparison =>
    let op := match comparison with
      | .lt => "<"
      | .le => "<="
      | .gt => ">"
      | .ge => ">="
      | .eq => "="
    let (tag, text, cast) : String × String × String ← match f.value with
      | .prim (.int i) => pure ("int", toString i.toInt, "::numeric")
      | .ext (.decimal d) => pure ("decimal", toString d.toInt, "::numeric")
      | .ext (.datetime d) => pure ("datetime", toString d.val.toInt, "::numeric")
      | .ext (.duration d) => pure ("duration", toString d.val.toInt, "::numeric")
      | .prim (.bool b) => pure ("bool", toString b, "::boolean")
      | .prim (.string s) => if s.contains '\x00' then invalid else pure ("string", s, "")
      | _ => invalid
    let body := column ++ "->>1"
    let (lhs, rhs) :=
      if cast.isEmpty then ("(" ++ body ++ ") COLLATE \"C\"", "$" ++ toString (index + 1) ++ "::text")
      else ("(" ++ body ++ ")" ++ cast, "$" ++ toString (index + 1) ++ cast)
    return ("CASE WHEN " ++ column ++ "->>0 = $" ++ toString index ++ "::text THEN " ++
      lhs ++ " " ++ op ++ " " ++ rhs ++ " ELSE false END", [tag, text])

/-- 一覧の対象テーブルの行のうち、問い合わせの絞り込みに合う行の取得(絞り込みは DB 側で行う)。
絞り込みが無ければ `selectTable` と同じ全行。これも内部の認可の材料であり、permit の判定・並べ替え・ページは
取得した後に Lean で行う。 -/
def selectFiltered (schema : Authz.Schema) (table : Table) (filters : List Filter) :
    Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM identifier
  let (conditions, parameters) ← filters.foldlM (init := (([] : List String), ([] : List String)))
    fun (conditions, parameters) f => do
      let (condition, ps) ← filterSql columns (parameters.length + 1) f
      return (conditions ++ [condition], parameters ++ ps)
  let predicate := if conditions.isEmpty then "" else " WHERE " ++ " AND ".intercalate conditions
  return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name ++ predicate, parameters.toArray⟩

/-- 既に認可されたモデルの操作だけを SQL にする。これを呼ぶことは認可ではない。
ランタイムは操作を Authz/Runtime から得て、すべての処理を 1 つのトランザクションに収めなければならない。
空の更新は今のところ拒む。無制限の書き込みになってはならない。
-/
def operation (schema : Authz.Schema) (op : Operation) : Except String Command := do
  let (name, columns) ← layout schema op.target.ty
  let key ← keyParam op.target.eid
  let predicate := " WHERE " ++ keySql ++ " = $1::text"
  match op with
  | .read _ _ =>
    let fields ← columns.mapM identifier
    return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name ++ predicate, #[key]⟩
  | .delete _ _ => return ⟨"DELETE FROM " ++ name ++ predicate, #[key]⟩
  | .insert _ _ row =>
    let values ← cells columns row
    let placeholders := values.zipIdx |>.map fun (_, i) => "$" ++ toString (i + 2) ++ "::jsonb"
    return ⟨"INSERT INTO " ++ name ++ " (" ++ join (keySql :: values.map Prod.fst) ++
      ") VALUES (" ++ join ("$1::text" :: placeholders) ++ ") ON CONFLICT (" ++
      keySql ++ ") DO NOTHING", #[key] ++ (values.map Prod.snd).toArray⟩
  | .update _ _ row =>
    let values ← cells columns row
    if values.isEmpty then invalid else do
      let assignments := values.zipIdx |>.map fun ((column, _), i) =>
        column ++ " = $" ++ toString (i + 2) ++ "::jsonb"
      return ⟨"UPDATE " ++ name ++ " SET " ++ join assignments ++ predicate,
        #[key] ++ (values.map Prod.snd).toArray⟩

end Nyxis.Internal.PostgresSql
