import Nyxis.Internal.PostgresResult
import Nyxis.Internal.IOTrace

/-! Internal fetching of decision materials (Assumption 1; unproved). This unfiltered Store must never be exposed to handlers. All
SELECTs and the authorized processing after them share one SERIALIZABLE transaction, and results are exposed only after
a checked COMMIT.
-/
namespace Nyxis.Internal.PostgresLoad
open Nyxis
open Nyxis.Internal.IOTrace (MapSuccess mapM_success)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL snapshot acquisition")

/-- Only core-generated commands reach this injectable execution boundary. -/
structure Driver where
  select : PostgresSql.Command → IO PostgresResult.Reader

/-- Checks the whole schema up front before issuing any SQL. Extraction and restoration are all-or-nothing, including
empty tables. A partially fetched Store is never returned. The caller must already be inside the transaction used for
the subsequent model/SQL processing.
-/
def collect (schema : Authz.Schema) (driver : Driver) : IO Db.Store := do
  let tables := schema.tables.map Prod.fst
  unless tables.eraseDups == tables do invalid
  let commands ← tables.mapM fun table => do
    let .ok command := PostgresSql.selectTable schema table | invalid
    return (table, command)
  let results ← commands.mapM fun (table, command) => do
    let reader ← driver.select command
    return (table, ← PostgresResult.extract schema table reader)
  let .ok store := PostgresSnapshot.restore schema results | invalid
  return store

/-- The successful SELECT/extraction pairs in command order, sharing adjacent IO states. This is a statement about Lean
return values and claims nothing about the meaning of the external SQL. -/
inductive Selects (schema : Authz.Schema) (driver : Driver) :
    List (Db.Table × PostgresSql.Command) → List (Db.Table × PostgresSnapshot.Result) →
      Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Selects schema driver [] [] w w
  | cons {table command commands result results reader w wm wn w'} :
      driver.select command w = .ok reader wm →
      PostgresResult.extract schema table reader wm = .ok result wn →
      Selects schema driver commands results wn w' →
      Selects schema driver ((table, command) :: commands) ((table, result) :: results) w w'

private theorem selects_of_map (schema : Authz.Schema) (driver : Driver)
    (commands : List (Db.Table × PostgresSql.Command)) (results)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (fun (table, command) => do
      let reader ← driver.select command
      return (table, ← PostgresResult.extract schema table reader)) commands results w w') :
    Selects schema driver commands results w w' := by
  induction h with
  | nil => exact .nil _
  | @cons entry entries value values w wm w' hs ht ih =>
    rcases entry with ⟨table, command⟩
    change EST.bind (driver.select command) _ w = .ok value wm at hs
    unfold EST.bind at hs
    split at hs
    · rename_i reader wr hr
      change EST.bind (PostgresResult.extract schema table reader) (fun result => EST.pure (table, result)) wr = .ok value wm at hs
      unfold EST.bind at hs
      split at hs
      · rename_i result we he
        change EST.Out.ok (table, result) we = EST.Out.ok value wm at hs
        cases hs
        exact .cons hr he ih
      · cases hs
    · cases hs

private theorem compiled_of_map (schema : Authz.Schema) (tables : List Db.Table) (commands)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (fun table => do
      let .ok command := PostgresSql.selectTable schema table | invalid
      return (table, command)) tables commands w w') :
    w' = w ∧ List.Forall₂ (fun table entry => entry.1 = table ∧
      PostgresSql.selectTable schema table = .ok entry.2) tables commands := by
  induction h with
  | nil => exact ⟨rfl, .nil⟩
  | @cons table tables entry entries w wm w' hs ht ih =>
    cases hc : PostgresSql.selectTable schema table with
    | error e => simp only [hc] at hs; cases hs
    | ok command =>
      simp only [hc] at hs
      change EST.Out.ok (table, command) w = EST.Out.ok entry wm at hs
      cases hs
      exact ⟨ih.1, .cons ⟨rfl, hc⟩ ih.2⟩

/-- If the real collect terminates normally, the duplicate table-name check and the up-front generation of all SELECTs
succeeded, and restore rebuilt the returned Store from the results of each SELECT and result extraction succeeding in
the same order. The IO states of the stages are shared, and a partial fetch never terminates normally. Nothing is
claimed about agreement between the external DB's actual state and the extracted results, or about SQL semantics. -/
theorem collect_success (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        Selects schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store := by
  unfold collect at h
  split at h
  · rename_i hd
    refine ⟨by simpa using hd, ?_⟩
    change EST.bind _ _ w = .ok store w' at h
    unfold EST.bind at h
    split at h
    · rename_i commands wm hc
      change EST.bind _ _ wm = .ok store w' at h
      unfold EST.bind at h
      split at h
      · rename_i results wn hr
        cases hs : PostgresSnapshot.restore schema results with
        | error e => simp only [hs] at h; cases h
        | ok restored =>
          simp only [hs] at h
          change EST.Out.ok restored wn = EST.Out.ok store w' at h
          cases h
          obtain ⟨hw, hcompiled⟩ := compiled_of_map schema _ _ w wm (mapM_success _ _ w wm commands hc)
          subst wm
          exact ⟨commands, results, hcompiled,
            selects_of_map schema driver _ _ w w' (mapM_success _ _ w w' results hr), hs⟩
      · cases h
    · cases h
  · change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h

/-- If the real collect terminates normally, table names are not duplicated, and the up-front generation of all SELECTs
and the SELECT/extraction in input order succeed in consecutive IO states. restore succeeds on those extraction results,
and every table, row and attribute satisfies the per-tag JSON decoding relation ValueRow/ValueCell. Map.make over the
decoded rows concatenated in result order is exactly the returned Store. NULL attributes are absent, and non-NULL
attributes have a successful JSON parse and the Decoded relation. Preservation of integer values is obtained from
Decoded.int_value. The JSON parser internals, Map lookup, SQL semantics, and agreement with the external DB's actual
state or FFI behavior are not included. -/
theorem collect_values (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results rows,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        Selects schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store ∧
        List.Forall₂ (fun entry decoded => ∃ columns,
          (schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
          entry.2.columns = "_nyxis_id" :: columns ∧
          List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
          results rows ∧
        store = Cedar.Data.Map.make rows.flatten := by
  obtain ⟨distinct, commands, results, compiled, selected, restored⟩ :=
    collect_success schema driver w w' store h
  obtain ⟨rows, related, constructed⟩ :=
    PostgresSnapshot.restore_values schema results store restored
  exact ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩

/-- Successful SELECT/extraction plus the sequence of the actual Reader's metadata and cell fetches. Every state is
shared with the corresponding SELECT and the next table. -/
inductive SelectCells (schema : Authz.Schema) (driver : Driver) :
    List (Db.Table × PostgresSql.Command) → List (Db.Table × PostgresSnapshot.Result) →
      Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : SelectCells schema driver [] [] w w
  | cons {table command commands result results reader w wm wn w' count w1 w2 w3 wc} :
      driver.select command w = .ok reader wm →
      PostgresResult.extract schema table reader wm = .ok result wn →
      reader.status wm = .ok .tuplesOk w1 →
      reader.rowCount w1 = .ok count w2 →
      reader.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 →
      0 ≤ count →
      PostgresResult.Metadata reader result.columns.zipIdx w3 wc →
      PostgresResult.Rows reader (List.range result.columns.length)
        (List.range count.toNat) result.rows wc wn →
      result.rows.length = count.toNat →
      (∀ row ∈ result.rows, row.length = result.columns.length) →
      SelectCells schema driver commands results wn w' →
      SelectCells schema driver ((table, command) :: commands) ((table, result) :: results) w w'

/-- For every element of the list of successful SELECT/extractions, extracts the real Reader's status, row and column
counts, metadata in projection order, and NULL/value/byte-length fetches in row-column order. The IO state is shared
between a SELECT and the next table, and the returned row and column counts are preserved. -/
theorem Selects.cells (schema : Authz.Schema) (driver : Driver)
    (commands results w w') (h : Selects schema driver commands results w w') :
    SelectCells schema driver commands results w w' := by
  induction h with
  | nil => exact .nil _
  | cons hs he ht ih =>
    obtain ⟨count, w1, w2, w3, wc, status, rows, columns, nonneg, metadata,
      cells, height, width⟩ := PostgresResult.extract_cells _ _ _ _ _ _ he
    exact .cons hs he status rows columns nonneg metadata cells height width ih

/-- From normal termination of the real collect, ties into a single chain of evidence the up-front generation of all
SELECTs, the consecutive IO states of each SELECT and the real Reader's metadata and NULL/value/byte-length fetches, and
the per-tag JSON decoding of every table, row and attribute of the same extraction results together with the Map.make
construction of the returned Store. NULL attributes are absent, and non-NULL attributes have a successful JSON parse and
the Decoded relation. The JSON parser internals, Map lookup, SQL semantics, and agreement with the external DB's actual
state/FFI are not included. -/
theorem collect_cells_values (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results rows,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        SelectCells schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store ∧
        List.Forall₂ (fun entry decoded => ∃ columns,
          (schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
          entry.2.columns = "_nyxis_id" :: columns ∧
          List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
          results rows ∧
        store = Cedar.Data.Map.make rows.flatten := by
  obtain ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩ :=
    collect_values schema driver w w' store h
  exact ⟨distinct, commands, results, rows, compiled, selected.cells schema driver,
    restored, related, constructed⟩

/-- Uses the fixed lean-pq connection, text-format results and the checked SELECT status. -/
def driver (conn : LeanPq.Handle) : Driver where
  select := fun command => do
    let result ← Postgres.exec conn command.sql command.parameters .tuplesOk
    return PostgresResult.reader result

/-- A new connection, a checked SERIALIZABLE transaction, and a snapshot and continuation on the same connection. The
continuation's value is returned only after COMMIT succeeds. Failures are propagated without reusing the connection. The
continuation is trusted core code, not an application handler: it must execute only operations the model has authorized.
-/
def withSnapshot (conninfo : String) (schema : Authz.Schema)
    (body : LeanPq.Handle → Db.Store → IO α) : IO α :=
  Postgres.withTransaction conninfo fun conn => do
    let store ← collect schema (driver conn)
    body conn store

/-- If the real withSnapshot terminates normally, the new connection, idle, the BEGIN tag and inTransaction, collect on
the same connection, the continuation given the resulting Store, the health check, and the COMMIT tag and idle succeed
in order, and the continuation's value is returned unchanged. This is a claim about the real IO definitions; agreement
between the fetched rows and the external DB's actual state is not included. -/
theorem withSnapshot_success (conninfo : String) (schema : Authz.Schema)
    (body : LeanPq.Handle → Db.Store → IO α)
    (w w' : Void IO.RealWorld) (value : α)
    (h : withSnapshot conninfo schema body w = .ok value w') :
    ∃ conn store wc w₀ w₁ w₂ w₃ w₄ w₅ w₆,
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      collect schema (driver conn) w₂ = .ok store w₃ ∧
      body conn store w₃ = .ok value w₄ ∧
      (Postgres.driver conn).status w₄ = .ok .inTransaction w₅ ∧
      (Postgres.driver conn).command "COMMIT" w₅ = .ok "COMMIT" w₆ ∧
      (Postgres.driver conn).status w₆ = .ok .idle w' := by
  obtain ⟨conn, wc, hc, ht⟩ := Postgres.withTransaction_success conninfo _ w w' value h
  obtain ⟨w₀, w₁, w₂, w₄, w₅, w₆, hi, hb, hs, hbody, hh, hm, he⟩ :=
    Postgres.transaction_success _ _ wc w' value ht
  change EST.bind (collect schema (driver conn)) (body conn) w₂ = .ok value w₄ at hbody
  unfold EST.bind at hbody
  split at hbody
  · rename_i store w₃ hcollect
    exact ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆,
      hc, hi, hb, hs, hcollect, hbody, hh, hm, he⟩
  · cases hbody

end Nyxis.Internal.PostgresLoad
