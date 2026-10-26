import Nyxis.Internal.PostgresSnapshot
import Test.Fixture

open Nyxis Db Cedar.Spec Nyxis.Internal.PostgresSnapshot

/-- 型環境が要らない検査用の空の型環境。 -/
private def noTypes : Cedar.Validation.Schema := ⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩

private def user : Table := ⟨"User", []⟩
private def post : Table := ⟨"Post", []⟩
private def boolCell := some "[\"bool\",true]"
private def users (rows : List (List (Option String))) : Result :=
  ⟨["_nyxis_id", "admin"], rows⟩
private def decoded (rows : List (List (Option String))) := tableRows Test.Fixture.schema user (users rows)

#guard decoded [] == .ok []
#guard decoded [[some "root", boolCell]] ==
  .ok [(⟨user, "root"⟩, Cedar.Data.Map.make [("admin", .prim (.bool true))])]
#guard decoded [[some "root", none]] == .ok [(⟨user, "root"⟩, Cedar.Data.Map.empty)]
-- Empty string key is valid in the model, distinct from SQL NULL.
#guard (decoded [[some "", boolCell]]).isOk
#guard !(decoded [[none, boolCell]]).isOk
#guard !(decoded [[]]).isOk
#guard !(decoded [[some "root"]]).isOk
#guard !(decoded [[some "root", boolCell, none]]).isOk
#guard !(decoded [[some "root", some ""]]).isOk
#guard !(decoded [[some "root", some "null"]]).isOk
#guard !(decoded [[some "root", some "[\"bool\",\"true\"]"]]).isOk
#guard !(decoded [[some "root", boolCell], [some "root", none]]).isOk
#guard !(decoded [[some "a", boolCell], [some "b", none], [some "a", boolCell]]).isOk
#guard !(decoded [[some (String.singleton '\x00'), boolCell]]).isOk
#guard !(tableRows Test.Fixture.schema user ⟨["admin", "_nyxis_id"], []⟩).isOk
#guard !(tableRows Test.Fixture.schema user ⟨["_nyxis_id", "admin", "extra"], []⟩).isOk
#guard !(tableRows Test.Fixture.schema user ⟨["_nyxis_id"], []⟩).isOk
#guard !(tableRows Test.Fixture.schema user ⟨["_nyxis_id", "admin", "admin"], []⟩).isOk
#guard !(tableRows Test.Fixture.schema ⟨"Missing", []⟩ (users [])).isOk
#guard !(tableRows ⟨[(user, ["_nyxis_id"])], [], noTypes, [], [], {}, [], []⟩ user (users [])).isOk
#guard !(tableRows ⟨[(user, ["admin", "admin"])], [], noTypes, [], [], {}, [], []⟩ user (users [])).isOk
#guard !(tableRows ⟨[(⟨"User", ["ns"]⟩, ["admin"])], [], noTypes, [], [], {}, [], []⟩ ⟨"User", ["ns"]⟩ (users [])).isOk

-- Reconstruct all five fixture rows and eleven cells through the storage format.
private def fixture : List (Table × Result) := Test.Fixture.schema.tables.map fun (table, columns) =>
  (table, ⟨"_nyxis_id" :: columns,
    Test.Fixture.store.toList.filterMap fun (uid, row) =>
      if uid.ty != table then none else some (some uid.eid :: columns.map fun column =>
        (row.find? column).bind (fun cell => (Nyxis.Internal.PostgresValue.encode cell).toOption))⟩)
#guard restore Test.Fixture.schema fixture == .ok Test.Fixture.store
#guard restore Test.Fixture.schema fixture.reverse == .ok Test.Fixture.store
#guard restore ⟨[], [], noTypes, [], [], {}, [], []⟩ [] == .ok Cedar.Data.Map.empty
#guard !(restore Test.Fixture.schema []).isOk
#guard !(restore Test.Fixture.schema [(user, users [])]).isOk
#guard !(restore Test.Fixture.schema (fixture ++ [(user, users [])])).isOk
#guard !(restore Test.Fixture.schema [(user, users []), (user, users [])]).isOk
#guard !(restore Test.Fixture.schema [(user, users []), (⟨"Other", []⟩, users [])]).isOk
#guard !(restore ⟨[(user, ["admin"]), (user, ["admin"])], [], noTypes, [], [], {}, [], []⟩ [(user, users [])]).isOk
#guard !(restore Test.Fixture.schema (fixture.map fun (t, r) =>
  (t, if t == user then users [[some "bad", some "null"]] else r))).isOk
-- Same ID in distinct tables does not alias an entity; NULL omits every attribute.
private def emptyRows := Test.Fixture.schema.tables.map fun (t, cols) =>
  (t, (⟨"_nyxis_id" :: cols, [some "same" :: cols.map (fun _ => none)]⟩ : Result))
#guard (restore Test.Fixture.schema emptyRows).toOption.map (·.toList.length) == some 2
#guard (restore Test.Fixture.schema emptyRows).toOption.map (fun s =>
  s.find? post "same" == some Cedar.Data.Map.empty &&
  s.find? user "same" == some Cedar.Data.Map.empty) == some true
-- Quoting/escaping is decoded as data; JSONB whitespace is accepted.
#guard (decoded [[some "';日本語", some " [ \"string\", \"a\\n\\\"b\" ] "]]).isOk
