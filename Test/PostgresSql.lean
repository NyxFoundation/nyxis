import Nyxis.Internal.PostgresSql
import Test.Fixture

open Nyxis Nyxis.Db Cedar.Spec Nyxis.Internal.PostgresSql

/-- 型環境が要らない検査用の空の型環境。 -/
private def noTypes : Cedar.Validation.Schema := ⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩

private def post : Table := ⟨"Post", []⟩
private def user : Table := ⟨"User", []⟩
private def str (s : String) : Value := .prim (.string s)
private def row : Row := Cedar.Data.Map.make [("title", str "new"), ("body", str "text")]
private def sql (result : Except String Command) := result.toOption.map (·.sql)
private def params (result : Except String Command) := result.toOption.map (·.parameters)

#guard sql (createTable Test.Fixture.schema user) ==
  some "CREATE TABLE \"public\".\"User\" (\"_nyxis_id\" text COLLATE \"C\" PRIMARY KEY, \"admin\" jsonb)"
-- 予約テーブル `_nyxis_outbox`: 正本のテーブルにはこの名前を使えず、形は docs/external-calls.md §4.3 に固定。
#guard (createTable { Test.Fixture.schema with tables := [(⟨"_nyxis_outbox", []⟩, ["x"])] } ⟨"_nyxis_outbox", []⟩).toOption.isNone
#guard (operation { Test.Fixture.schema with tables := [(⟨"_nyxis_outbox", []⟩, ["x"])] } (.read ⟨"_nyxis_outbox", []⟩ "k")).toOption.isNone
#guard outbox.map (·.2) == ["CREATE TABLE", "CREATE INDEX"]
#guard (outbox.map (·.1.sql))[0]? == some ("CREATE TABLE \"public\".\"_nyxis_outbox\" (\"_nyxis_id\" text COLLATE \"C\" PRIMARY KEY, " ++
  "\"principal\" text NOT NULL, \"action\" text NOT NULL, \"target\" text NOT NULL, \"destination\" text NOT NULL, " ++
  "\"method\" text NOT NULL, \"url\" text NOT NULL, \"body\" jsonb, " ++
  "\"state\" text NOT NULL CHECK (\"state\" IN ('pending', 'sent', 'failed')), \"attempts\" integer NOT NULL DEFAULT 0, " ++
  "\"next_at\" timestamptz NOT NULL, \"last_status\" integer, \"last_error\" text, \"created_at\" timestamptz NOT NULL, " ++
  "\"sent_at\" timestamptz)")
#guard (outbox.map (·.1.sql))[1]? == some
  "CREATE INDEX \"_nyxis_outbox_pending_idx\" ON \"public\".\"_nyxis_outbox\" (\"next_at\") WHERE \"state\" = 'pending'"
#guard sql (selectTable Test.Fixture.schema user) ==
  some "SELECT \"_nyxis_id\", \"admin\" FROM \"public\".\"User\""
#guard sql (operation Test.Fixture.schema (.read user "u")) ==
  some "SELECT \"_nyxis_id\", \"admin\" FROM \"public\".\"User\" WHERE \"_nyxis_id\" = $1::text"
-- 一覧の絞り込み: 絞り込みが無ければ全行、等値は JSONB の一致、大小はタグを CASE で見てから本文を比べる。
#guard sql (selectFiltered Test.Fixture.schema user []) == sql (selectTable Test.Fixture.schema user)
#guard sql (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str "new"⟩, ⟨"published", .eq, .prim (.bool true)⟩]) ==
  some "SELECT \"_nyxis_id\", \"author\", \"title\", \"body\", \"published\" FROM \"public\".\"Post\" WHERE \"title\" = $1::jsonb AND \"published\" = $2::jsonb"
#guard params (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str "new"⟩, ⟨"published", .eq, .prim (.bool true)⟩]) ==
  some #["[\"string\",\"new\"]", "[\"bool\",true]"]
#guard sql (selectFiltered Test.Fixture.schema post [⟨"title", .lt, str "m"⟩]) ==
  some "SELECT \"_nyxis_id\", \"author\", \"title\", \"body\", \"published\" FROM \"public\".\"Post\" WHERE CASE WHEN \"title\"->>0 = $1::text THEN (\"title\"->>1) COLLATE \"C\" < $2::text ELSE false END"
#guard params (selectFiltered Test.Fixture.schema post [⟨"title", .lt, str "m"⟩]) == some #["string", "m"]
#guard sql (selectFiltered Test.Fixture.schema post [⟨"title", .ge, .ext (.datetime ⟨1700000000000⟩)⟩, ⟨"title", .eq, str "x"⟩]) ==
  some "SELECT \"_nyxis_id\", \"author\", \"title\", \"body\", \"published\" FROM \"public\".\"Post\" WHERE CASE WHEN \"title\"->>0 = $1::text THEN (\"title\"->>1)::numeric >= $2::numeric ELSE false END AND \"title\" = $3::jsonb"
#guard params (selectFiltered Test.Fixture.schema post [⟨"title", .ge, .ext (.datetime ⟨1700000000000⟩)⟩, ⟨"title", .eq, str "x"⟩]) ==
  some #["datetime", "1700000000000", "[\"string\",\"x\"]"]
#guard params (selectFiltered Test.Fixture.schema post [⟨"published", .le, .prim (.bool false)⟩]) == some #["bool", "false"]
#guard params (selectFiltered Test.Fixture.schema post [⟨"title", .gt, .prim (.int (-5))⟩]) == some #["int", "-5"]
-- 無い列・集合や実体参照の大小・NUL 入りの文字列は拒む。絞り込みの定数は SQL の文字列に入らない。
#guard (selectFiltered Test.Fixture.schema post [⟨"nope", .eq, str "x"⟩]).toOption.isNone
#guard (selectFiltered Test.Fixture.schema post [⟨"author", .lt, .prim (.entityUID ⟨user, "u"⟩)⟩]).toOption.isNone
#guard (selectFiltered Test.Fixture.schema post [⟨"title", .lt, .set Cedar.Data.Set.empty⟩]).toOption.isNone
#guard (selectFiltered Test.Fixture.schema post [⟨"title", .lt, str "a\x00b"⟩]).toOption.isNone
-- 保存形式にできない定数との等値は定数 false の条件(保存された行がその値に等しいことはない)。
#guard sql (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str "a\x00b"⟩, ⟨"title", .eq, str "x"⟩]) ==
  some "SELECT \"_nyxis_id\", \"author\", \"title\", \"body\", \"published\" FROM \"public\".\"Post\" WHERE false AND \"title\" = $1::jsonb"
#guard params (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str "a\x00b"⟩, ⟨"title", .eq, str "x"⟩]) ==
  some #["[\"string\",\"x\"]"]
#guard sql (operation Test.Fixture.schema (.delete post "p")) ==
  some "DELETE FROM \"public\".\"Post\" WHERE \"_nyxis_id\" = $1::text"
#guard sql (operation Test.Fixture.schema (.insert post "p" row)) ==
  some "INSERT INTO \"public\".\"Post\" (\"_nyxis_id\", \"body\", \"title\") VALUES ($1::text, $2::jsonb, $3::jsonb) ON CONFLICT (\"_nyxis_id\") DO NOTHING"
#guard sql (operation Test.Fixture.schema (.update post "p" row)) ==
  some "UPDATE \"public\".\"Post\" SET \"body\" = $2::jsonb, \"title\" = $3::jsonb WHERE \"_nyxis_id\" = $1::text"
#guard params (operation Test.Fixture.schema (.update post "p" row)) ==
  some #["p", "[\"string\",\"text\"]", "[\"string\",\"new\"]"]

-- Request values, even SQL-looking values, never change the query text.
private def attack := "'; DROP TABLE Post;--日本語\n\\\""
#guard sql (operation Test.Fixture.schema (.delete post attack)) ==
  sql (operation Test.Fixture.schema (.delete post "p"))
#guard params (operation Test.Fixture.schema (.delete post attack)) == some #[attack]
#guard sql (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str attack⟩]) ==
  sql (selectFiltered Test.Fixture.schema post [⟨"title", .eq, str "p"⟩])
#guard sql (operation Test.Fixture.schema (.update post attack (Cedar.Data.Map.make [("title", str attack)]))) ==
  some "UPDATE \"public\".\"Post\" SET \"title\" = $2::jsonb WHERE \"_nyxis_id\" = $1::text"
#guard (params (operation Test.Fixture.schema (.update post attack (Cedar.Data.Map.make [("title", str attack)])))) ==
  some #[attack, (Nyxis.Internal.PostgresValue.encode (str attack)).toOption.getD ""]
-- Fixture rows compile and retain every cell parameter after decoding.
#guard Test.Fixture.store.toList.all fun (uid, r) =>
  match operation Test.Fixture.schema (.insert uid.ty uid.eid r) with
  | .error _ => false
  | .ok cmd => cmd.parameters.size == r.toList.length + 1 &&
    ((cmd.parameters.toList.drop 1).zip r.toList).all fun (p, (_, v)) =>
      Nyxis.Internal.PostgresValue.decode p == .ok v

private def schema (name : String) (cols : List String) : Nyxis.Authz.Schema :=
  ⟨[(⟨name, []⟩, cols)], [], noTypes, [], [], {}, [], []⟩
#guard sql (createTable (schema "a\";--" ["x\";--"]) ⟨"a\";--", []⟩) ==
  some "CREATE TABLE \"public\".\"a\"\";--\" (\"_nyxis_id\" text COLLATE \"C\" PRIMARY KEY, \"x\"\";--\" jsonb)"
#guard !(createTable (schema "Post" ["_nyxis_id"]) post).isOk
#guard !(createTable (schema "Post" ["title", "title"]) post).isOk
#guard !(createTable ⟨[(post, []), (post, [])], [], noTypes, [], [], {}, [], []⟩ post).isOk
#guard !(createTable Test.Fixture.schema ⟨"Missing", []⟩).isOk
#guard !(createTable ⟨[(⟨"Post", ["ns"]⟩, [])], [], noTypes, [], [], {}, [], []⟩ ⟨"Post", ["ns"]⟩).isOk
#guard !(createTable (schema "" []) ⟨"", []⟩).isOk
#guard !(createTable (schema "Post" [String.singleton '\x00']) post).isOk
#guard !(createTable (schema "Post" [String.ofList (List.replicate 22 '語')]) post).isOk
#guard (createTable (schema "Post" [String.ofList (List.replicate 21 '語')]) post).isOk
#guard !(operation Test.Fixture.schema (.delete post (String.singleton '\x00'))).isOk
#guard !(operation Test.Fixture.schema (.update post "p" Cedar.Data.Map.empty)).isOk
#guard !(operation Test.Fixture.schema (.insert post "p" (Cedar.Data.Map.make [("admin", .prim (.bool true))]))).isOk
-- 保存形式に無い値(集合の集合)は SQL にならない。集合・レコード自体は保存形式にある(型の検査は PostgresShape)。
#guard !(operation Test.Fixture.schema (.insert post "p" (Cedar.Data.Map.make
  [("title", .set (Cedar.Data.Set.make [.set Cedar.Data.Set.empty]))]))).isOk
#guard (operation Test.Fixture.schema (.insert post "p" (Cedar.Data.Map.make [("title", .record Cedar.Data.Map.empty)]))).isOk
#guard sql (operation Test.Fixture.schema (.insert user "u" Cedar.Data.Map.empty)) ==
  some "INSERT INTO \"public\".\"User\" (\"_nyxis_id\") VALUES ($1::text) ON CONFLICT (\"_nyxis_id\") DO NOTHING"
#guard sql (operation (schema "Empty" []) (.read ⟨"Empty", []⟩ "k")) ==
  some "SELECT \"_nyxis_id\" FROM \"public\".\"Empty\" WHERE \"_nyxis_id\" = $1::text"

/-! ## 一意性と参照整合の DDL -/

private def org : Table := ⟨"Org", []⟩
private def doc : Table := ⟨"Doc", []⟩
private def c35 : Nyxis.Authz.Schema :=
  { tables := [(org, ["name"]), (doc, ["org", "title", "createdBy"]), (user, ["admin"])], actions := [], types := noTypes,
    constraints :=
      { uniques := [⟨org, ["name"]⟩, ⟨doc, ["org", "title"]⟩]
      , references := [⟨doc, "org", org, .cascade ⟨⟨"Action", []⟩, "deleteDoc"⟩⟩, ⟨doc, "createdBy", user, .restrict⟩] } }
-- 一意性の組は UNIQUE、参照の列には保存形式の ID を持つ生成列。外部キーは全テーブルの後の ALTER TABLE(削除は RESTRICT)。
#guard sql (createTable c35 org) ==
  some "CREATE TABLE \"public\".\"Org\" (\"_nyxis_id\" text COLLATE \"C\" PRIMARY KEY, \"name\" jsonb, UNIQUE (\"name\"))"
#guard sql (createTable c35 doc) ==
  some ("CREATE TABLE \"public\".\"Doc\" (\"_nyxis_id\" text COLLATE \"C\" PRIMARY KEY, \"org\" jsonb, \"title\" jsonb, " ++
    "\"createdBy\" jsonb, \"_nyxis_ref_org\" text COLLATE \"C\" GENERATED ALWAYS AS (\"org\" ->> 3) STORED, " ++
    "\"_nyxis_ref_createdBy\" text COLLATE \"C\" GENERATED ALWAYS AS (\"createdBy\" ->> 3) STORED, UNIQUE (\"org\", \"title\"))")
#guard sql (createTable c35 user) == sql (createTable Test.Fixture.schema user)
#guard (foreignKeys c35).toOption.map (·.map fun (c, tag) => (c.sql, tag)) == some
  [ ("ALTER TABLE \"public\".\"Doc\" ADD CONSTRAINT \"Doc_org_fkey\" FOREIGN KEY (\"_nyxis_ref_org\") REFERENCES \"public\".\"Org\" (\"_nyxis_id\") ON DELETE RESTRICT", "ALTER TABLE")
  , ("CREATE INDEX \"Doc_org_ref_idx\" ON \"public\".\"Doc\" (\"_nyxis_ref_org\")", "CREATE INDEX")
  , ("ALTER TABLE \"public\".\"Doc\" ADD CONSTRAINT \"Doc_createdBy_fkey\" FOREIGN KEY (\"_nyxis_ref_createdBy\") REFERENCES \"public\".\"User\" (\"_nyxis_id\") ON DELETE RESTRICT", "ALTER TABLE")
  , ("CREATE INDEX \"Doc_createdBy_ref_idx\" ON \"public\".\"Doc\" (\"_nyxis_ref_createdBy\")", "CREATE INDEX") ]
#guard (foreignKeys Test.Fixture.schema) == .ok []
-- 読み取り・一覧・挿入・更新の SQL は生成列を含まない(列は正本の宣言だけ)
#guard sql (operation c35 (.read doc "d")) ==
  some "SELECT \"_nyxis_id\", \"org\", \"title\", \"createdBy\" FROM \"public\".\"Doc\" WHERE \"_nyxis_id\" = $1::text"
#guard sql (operation c35 (.insert doc "d" (Cedar.Data.Map.make [("title", str "t")]))) ==
  some "INSERT INTO \"public\".\"Doc\" (\"_nyxis_id\", \"title\") VALUES ($1::text, $2::jsonb) ON CONFLICT (\"_nyxis_id\") DO NOTHING"
#guard sql (selectFiltered c35 doc (Reference.filterOf "org" ⟨org, "o1"⟩)) ==
  some "SELECT \"_nyxis_id\", \"org\", \"title\", \"createdBy\" FROM \"public\".\"Doc\" WHERE \"org\" = $1::jsonb"
#guard params (selectFiltered c35 doc (Reference.filterOf "org" ⟨org, "o1"⟩)) == some #["[\"entity\",[],\"Org\",\"o1\"]"]
-- 無い列・空の組・重複の組・無い参照先は拒む
#guard !(createTable { c35 with constraints := { uniques := [⟨org, ["nope"]⟩] } } org).isOk
#guard !(createTable { c35 with constraints := { uniques := [⟨org, []⟩] } } org).isOk
#guard !(createTable { c35 with constraints := { uniques := [⟨doc, ["title", "title"]⟩] } } doc).isOk
#guard !(createTable { c35 with constraints := { references := [⟨doc, "nope", org, .restrict⟩] } } doc).isOk
#guard !(foreignKeys { c35 with constraints := { references := [⟨doc, "org", ⟨"Missing", []⟩, .restrict⟩] } }).isOk
#guard !(foreignKeys { c35 with constraints := { references := [⟨doc, "nope", org, .restrict⟩] } }).isOk
