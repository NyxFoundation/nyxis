import Nyxis.Internal.PostgresLoad
import Nyxis.Internal.PostgresMaterials
import Nyxis.Internal.PostgresWrite
import Nyxis.ReadSafety
import Nyxis.Internal.PostgresShape
import Nyxis.Internal.ExternalSend
import Nyxis.Internal.Outbox

/-! The internal boundary from the model to SQL (Assumption 1; unproved). There is no handler-facing API. Only the model generates
operations. The snapshot, replay and checked COMMIT share one SERIALIZABLE transaction. A disagreement with SQL aborts
without returning a response.

There are two paths. `handleStaged` (the path used by the real startup `PostgresHttp.handleVerified`) fetches, per
handler action call, only the entities needed for the decision by point lookups (`PostgresMaterials.load`), checks that
the fetch covers the decision materials, then decides, replays and matches, and continues with the result (the "Staged
execution" section). `handle` is a reference path that fetches all tables (`PostgresLoad.collect`), then computes
`Runtime.handleRequest` purely, and replays the issued operations to SQL and matches them; the real startup does not use
it (the check `scripts/check-postgres-values.py` verifies both paths, each against a separate real DB, against the same
expected values).
-/
namespace Nyxis.Internal.PostgresRun
open Nyxis Db Nyxis.Runtime

private def invalid : IO α := throw (IO.userError "PostgreSQL/model disagreement")

structure Driver where
  read : PostgresSql.Command → IO PostgresResult.Reader
  write : PostgresSql.Command → IO PostgresWrite.Reader
  /-- External effects (issuing signed URLs for attachments, sending mail, external API calls): called only for records
      from the authorization layer (`Authz.External`: principal, generated values, action, target, content
      `Authz.Payload`). For signed-URL issuance, `signed url` is the issued URL and `none` means the object does not
      exist. Mail is sent and returns `none`. A `sync` call is sent and returns the response (`called` / `calledError`).
      An `async` call is not sent; instead it writes one record row to the outbox on the same connection (the request's
      transaction) and returns `none` (`Nyxis.Internal.Outbox.enqueue`; the internal loop sends it after COMMIT).
      Failure is an exception (the whole request becomes 503). Kinds with no configuration cannot be executed
      (exception). -/
  external : Authz.External → IO Authz.ExternalResult := fun _ => throw (IO.userError "external effects are not configured")

/-- Exact match of a primary-key read, including row absence. Extra or wrong primary keys and changed attributes are
rejected. Extraction also checks status, metadata, NULL and encoding.
-/
def verifyRead (schema : Authz.Schema) (op : Operation) (expected : Outcome)
    (reader : PostgresResult.Reader) : IO Unit := do
  let .read table key := op | invalid
  let result ← PostgresResult.extract schema table reader
  let .ok rows := PostgresSnapshot.tableRows schema table result | invalid
  match rows, expected with
  | [], .notFound => pure ()
  | [(uid, row)], .ok (some expectedRow) =>
    unless uid == op.target && uid.eid == key && row == expectedRow do invalid
  | _, _ => invalid

/-- Normal termination of read matching requires successful result extraction from the same starting state and
successful restoration; the restored rows are empty if absent, and if present exactly one expected row whose primary key
is the requested target. The matching itself does not change the IO state after extraction. The correctness of the
extract/tableRows internals and of the external DB's actual state is not included in this theorem. -/
theorem verifyRead_success (schema : Authz.Schema) (op : Operation) (expected : Outcome)
    (reader : PostgresResult.Reader) (w w' : Void IO.RealWorld)
    (h : verifyRead schema op expected reader w = .ok () w') :
    ∃ table key result rows, op = .read table key ∧
      PostgresResult.extract schema table reader w = .ok result w' ∧
      PostgresSnapshot.tableRows schema table result = .ok rows ∧
      ((rows = [] ∧ expected = .notFound) ∨
        ∃ row, rows = [(op.target, row)] ∧ expected = .ok (some row)) := by
  cases op with
  | insert _ _ _ | update _ _ _ | delete _ _ =>
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | read table key =>
    unfold verifyRead at h
    change EST.bind _ _ w = .ok () w' at h
    unfold EST.bind at h
    split at h
    · rename_i result wm he
      cases ht : PostgresSnapshot.tableRows schema table result with
      | error e =>
        simp only [ht] at h
        change EST.Out.error _ _ = EST.Out.ok _ _ at h
        cases h
      | ok rows =>
        simp only [ht] at h
        cases rows with
        | nil =>
          cases expected <;> try simp only at h
          all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
          cases h
          exact ⟨table, key, result, [], rfl, he, ht, Or.inl ⟨rfl, rfl⟩⟩
        | cons entry rest =>
          cases rest with
          | cons _ _ =>
            change EST.Out.error _ _ = EST.Out.ok _ _ at h
            cases h
          | nil =>
            rcases entry with ⟨uid, row⟩
            cases expected <;> try simp only at h
            all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
            rename_i expectedRow
            cases expectedRow with
            | none =>
              change EST.Out.error _ _ = EST.Out.ok _ _ at h
              cases h
            | some expectedRow =>
              change (if uid == (Operation.read table key).target && uid.eid == key &&
                row == expectedRow then (pure () : IO Unit) else invalid) wm = .ok () w' at h
              split at h
              · rename_i hc
                simp only [Bool.and_eq_true, beq_iff_eq] at hc
                obtain ⟨⟨hu, _⟩, hr⟩ := hc
                subst uid
                subst row
                cases h
                exact ⟨table, key, result, [((Operation.read table key).target, expectedRow)],
                  rfl, he, ht, Or.inr ⟨expectedRow, rfl, rfl⟩⟩
              · change EST.Out.error _ _ = EST.Out.ok _ _ at h
                cases h
    · cases h

/-- The pure plan before SQL execution. The Store and SQL results are not added to the response. -/
structure Plan where
  commands : List (Authz.Issued × PostgresSql.Command)
  response : Http.Response

/-- Pre-checks all operations, preserving the order of issued. -/
def planCommands (schema : Authz.Schema) (shape : PostgresShape.Shape) :
    List Authz.Issued → Except String (List (Authz.Issued × PostgresSql.Command))
  | [] => .ok []
  | issued :: rest => do
    PostgresShape.validateOperation shape issued.store issued.op
    let command ← PostgresSql.operation schema issued.op
    let tail ← planCommands schema shape rest
    return (issued, command) :: tail

/-- The planner used by the real connection. No SQL is issued until all checks succeed. -/
def prepare (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) : Except String Plan := do
  PostgresShape.validateSchema shape app.schema
  PostgresShape.validateStore shape store
  let run := handleRequest app store request
  let commands ← planCommands app.schema shape run.issued
  return ⟨commands, run.result⟩

/-- A successful SQL plan keeps the model's issued list without dropping, adding or reordering. -/
theorem planCommands_issued (schema : Authz.Schema) (shape : PostgresShape.Shape)
    (issued : List Authz.Issued) (commands : List (Authz.Issued × PostgresSql.Command))
    (h : planCommands schema shape issued = .ok commands) :
    commands.map Prod.fst = issued := by
  induction issued generalizing commands with
  | nil => simp [planCommands] at h; subst commands; rfl
  | cons i rest ih =>
    simp only [planCommands] at h
    cases hv : PostgresShape.validateOperation shape i.store i.op <;> simp [hv, bind, Except.bind, pure, Except.pure] at h
    cases hc : PostgresSql.operation schema i.op <;> simp [hc] at h
    cases ht : planCommands schema shape rest <;> simp [ht] at h
    subst commands
    simp [ih _ ht]

/-- Each SQL command of a successful plan is the successful SQL-generation value of the corresponding operation, and it
has also passed the shape check against the Store just before that operation. Nothing is said about the semantics of the
SQL strings. -/
theorem planCommands_compiled (schema : Authz.Schema) (shape : PostgresShape.Shape)
    (issued : List Authz.Issued) (commands : List (Authz.Issued × PostgresSql.Command))
    (h : planCommands schema shape issued = .ok commands) :
    ∀ i command, (i, command) ∈ commands →
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation schema i.op = .ok command := by
  induction issued generalizing commands with
  | nil => simp [planCommands] at h; subst commands; simp
  | cons i rest ih =>
    simp only [planCommands] at h
    cases hv : PostgresShape.validateOperation shape i.store i.op <;>
      simp [hv, bind, Except.bind, pure, Except.pure] at h
    cases hc : PostgresSql.operation schema i.op <;> simp [hc] at h
    cases ht : planCommands schema shape rest <;> simp [ht] at h
    subst commands
    intro j command hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact ⟨hv, hc⟩
    · exact ih _ ht j command hm

/-- When planning on the real connection succeeds, the response is exactly the model response, and the list of
operations passed to SQL is exactly the model's issued list. The snapshot used for the authorization decision and the
SQL results are never put directly into the response. -/
theorem prepare_model (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    plan.response = (handleRequest app store request).result ∧
    plan.commands.map Prod.fst = (handleRequest app store request).issued := by
  simp only [prepare] at h
  cases hs : PostgresShape.validateSchema shape app.schema <;> simp [hs, bind, Except.bind, pure, Except.pure] at h
  cases hv : PostgresShape.validateStore shape store <;> simp [hv] at h
  cases hc : planCommands app.schema shape (handleRequest app store request).issued <;> simp [hc] at h
  subst plan
  exact ⟨rfl, planCommands_issued _ _ _ _ hc⟩

/-- In a successful real-connection plan, what SQL executes is authorized for the principal of the same request, and the
response can be reproduced by a replayer that does not receive the Store. Each row passed to the continuation is the
target row, in the Store just before it, of an authorized read in this plan. The correctness of SQL/FFI/COMMIT/HTTP
transport is not included. -/
theorem prepare_read_safety (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some plan.response ∧
    (∀ i ∈ plan.commands.map Prod.fst,
      i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
    (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
      ∃ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  obtain ⟨hr, hi⟩ := prepare_model app shape store request plan h
  rw [hr, hi]
  exact ⟨(ReadSafety.handleRequest_read_safety app store request).1,
    fun i hi => let ⟨hp, _, ha⟩ := handleRequest_authorized app store request i hi; ⟨hp, ha⟩,
    (ReadSafety.handleRequest_read_safety app store request).2⟩

/-- Each SQL command of a successful real-connection plan corresponds to a model operation authorized for the principal
of the same request, and SQL generation and the shape check for that operation succeeded. The semantics of the SQL
generator and the correctness of external execution, COMMIT and HTTP transport are not included. -/
theorem prepare_sql_authorized (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    ∀ i command, (i, command) ∈ plan.commands →
      i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
  have compiled : ∀ i command, (i, command) ∈ plan.commands →
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
    simp only [prepare] at h
    cases hs : PostgresShape.validateSchema shape app.schema <;>
      simp [hs, bind, Except.bind, pure, Except.pure] at h
    cases hv : PostgresShape.validateStore shape store <;> simp [hv] at h
    cases hc : planCommands app.schema shape (handleRequest app store request).issued <;>
      simp [hc] at h
    subst plan
    exact planCommands_compiled _ _ _ _ hc
  intro i command hm
  have hi : i ∈ plan.commands.map Prod.fst := List.mem_map.mpr ⟨(i, command), hm, rfl⟩
  obtain ⟨hp, ha⟩ := (prepare_read_safety app shape store request plan h).2.1 i hi
  exact ⟨hp, ha, compiled i command hm⟩

/-- Runs only inside the snapshot's transaction. The checked SQL results are discarded; the response is the planned
model response, exposed after the outer COMMIT. -/
def process (app : App) (shape : PostgresShape.Shape) (store : Store) (request : AuthenticatedRequest)
    (driver : Driver) : IO Http.Response := do
  let .ok plan := prepare app shape store request | invalid
  for (issued, command) in plan.commands do
    let expected := (issued.store.apply issued.op).2
    match issued.op with
    | .read _ _ => verifyRead app.schema issued.op expected (← driver.read command)
    | _ => PostgresWrite.verify issued.op expected (← driver.write command)
  return plan.response

/-- One SQL call and the matching of its result, with consecutive IO states. This states only Lean return values; the
meaning of the external SQL remains under Assumption 1. -/
def Checked (schema : Authz.Schema) (driver : Driver) (issued : Authz.Issued)
    (command : PostgresSql.Command) (w w' : Void IO.RealWorld) : Prop :=
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read _ _ => ∃ reader wm,
      driver.read command w = .ok reader wm ∧
      verifyRead schema issued.op expected reader wm = .ok () w'
  | _ => ∃ reader wm,
      driver.write command w = .ok reader wm ∧
      PostgresWrite.verify issued.op expected reader wm = .ok () w'

/-- Every planned command is executed in list order and passes matching. -/
inductive Executes (schema : Authz.Schema) (driver : Driver) :
    List (Authz.Issued × PostgresSql.Command) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Executes schema driver [] w w
  | cons {issued command commands w wm w'} :
      Checked schema driver issued command w wm →
      Executes schema driver commands wm w' →
      Executes schema driver ((issued, command) :: commands) w w'

/-- One SQL call followed by an extraction that exactly matches Store.apply. For read matching, extracts the Reader
calls and the per-tag decoding of either row absence or exactly one expected target row. For write matching, returns the
expected Outcome containing no row and extracts the successful Reader calls. The final state is the extraction's state.
-/
def Extracted (schema : Authz.Schema) (driver : Driver) (issued : Authz.Issued)
    (command : PostgresSql.Command) (w w' : Void IO.RealWorld) : Prop :=
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read table _ => ∃ reader wm result rows,
      driver.read command w = .ok reader wm ∧
      PostgresResult.extract schema table reader wm = .ok result w' ∧
      PostgresSnapshot.tableRows schema table result = .ok rows ∧
      ((rows = [] ∧ expected = .notFound) ∨
        ∃ row, rows = [(issued.op.target, row)] ∧ expected = .ok (some row)) ∧
      (∃ count w1 w2 w3 wc,
        reader.status wm = .ok .tuplesOk w1 ∧
        reader.rowCount w1 = .ok count w2 ∧
        reader.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 ∧
        0 ≤ count ∧ PostgresResult.Metadata reader result.columns.zipIdx w3 wc ∧
        PostgresResult.Rows reader (List.range result.columns.length)
          (List.range count.toNat) result.rows wc w' ∧
        result.rows.length = count.toNat ∧
        (∀ row ∈ result.rows, row.length = result.columns.length)) ∧
      (∃ columns,
        (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
        result.columns = "_nyxis_id" :: columns ∧
        List.Forall₂ (PostgresSnapshot.ValueRow table columns) result.rows rows)
  | _ => ∃ reader wm,
      driver.write command w = .ok reader wm ∧
      PostgresWrite.extract issued.op reader wm = .ok expected w' ∧
      (expected = .ok none ∨ expected = .conflict ∨ expected = .notFound) ∧
      ∃ tagStart count w1 w2 w3 w4,
        (match issued.op with
          | .insert _ _ _ => tagStart = "INSERT 0 "
          | .update _ _ _ => tagStart = "UPDATE "
          | .delete _ _ => tagStart = "DELETE "
          | .read _ _ => False) ∧
        reader.status wm = .ok .commandOk w1 ∧
        reader.rows w1 = .ok 0 w2 ∧ reader.columns w2 = .ok 0 w3 ∧
        reader.affected w3 = .ok count w4 ∧
        reader.tag w4 = .ok (tagStart ++ count) w' ∧
        (count = "0" ∨ count = "1") ∧
        expected = (if count = "1" then .ok none else
          match issued.op with
          | .insert _ _ _ => .conflict
          | .update _ _ _ | .delete _ _ | .read _ _ => .notFound)

/-- The result of each Driver call has an extraction result matching the expected value of Store.apply just before it.
For a read, the same Reader's status → row count → column count → projection metadata → NULL/value/UTF-8 byte-length
fetches of all cells are consecutive, preserving the row and column counts. All rows of the same result satisfy
ValueRow's per-tag JSON decoding relation, and are either absent or exactly one expected row with the target primary
key. A write is one of: success without rows, conflict, or absent. The write's status → row count → column count →
affected count → tag fetches are consecutive, and commandOk, zero rows and columns, a canonical count of 0/1, the
per-operation tag and the expected Outcome correspond. The state after matching remains the state at the end of
extraction. The external DB's actual state and SQL semantics are not included. -/
theorem Checked.extracted (schema : Authz.Schema) (driver : Driver)
    (issued : Authz.Issued) (command : PostgresSql.Command) (w w' : Void IO.RealWorld)
    (h : Checked schema driver issued command w w') :
    Extracted schema driver issued command w w' := by
  cases hop : issued.op <;> simp only [Checked, hop] at h
  all_goals obtain ⟨reader, wm, hr, hv⟩ := h
  all_goals simp only [Extracted, hop]
  case read table key =>
    obtain ⟨t, k, result, rows, he, hx, ht, ha⟩ :=
      verifyRead_success schema (.read table key) _ reader wm w' hv
    cases he
    exact ⟨reader, wm, result, rows, hr, hx, ht, ha,
      PostgresResult.extract_cells schema table reader result wm w' hx,
      PostgresSnapshot.tableRows_values schema table result rows ht⟩
  all_goals
    obtain ⟨hx, ha⟩ := PostgresWrite.verify_success _ _ reader wm w' hv
    exact ⟨reader, wm, hr, hx, ha, PostgresWrite.extract_success _ _ _ _ _ hx⟩

/-- For every command, extraction in execution order and an exact match with the model. -/
inductive Extracts (schema : Authz.Schema) (driver : Driver) :
    List (Authz.Issued × PostgresSql.Command) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Extracts schema driver [] w w
  | cons {issued command commands w wm w'} :
      Extracted schema driver issued command w wm →
      Extracts schema driver commands wm w' →
      Extracts schema driver ((issued, command) :: commands) w w'

/-- From the successful execution/matching sequence in plan order, obtains the extraction-match sequence with the same
SQL list and the same start/end IO states. The IO states of adjacent SQL statements are also consecutive, and no
operation is dropped or added. -/
theorem Executes.extracts (schema : Authz.Schema) (driver : Driver)
    (commands : List (Authz.Issued × PostgresSql.Command)) (w w' : Void IO.RealWorld)
    (h : Executes schema driver commands w w') :
    Extracts schema driver commands w w' := by
  induction h with
  | nil w => exact .nil w
  | cons hc _ ih => exact .cons (Checked.extracted schema driver _ _ _ _ hc) ih

private def commandStep (schema : Authz.Schema) (driver : Driver)
    (entry : Authz.Issued × PostgresSql.Command) (_ : PUnit) : IO (ForInStep PUnit) := do
  let (issued, command) := entry
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read _ _ => verifyRead schema issued.op expected (← driver.read command)
  | _ => PostgresWrite.verify issued.op expected (← driver.write command)
  return .yield ()

private theorem commandStep_success (schema : Authz.Schema) (driver : Driver)
    (issued : Authz.Issued) (command : PostgresSql.Command)
    (w w' : Void IO.RealWorld) (step : ForInStep PUnit)
    (h : commandStep schema driver (issued, command) () w = .ok step w') :
    step = .yield () ∧ Checked schema driver issued command w w' := by
  unfold commandStep at h
  cases hop : issued.op <;> simp only [hop] at h <;>
    change EST.bind _ _ w = .ok step w' at h <;>
    unfold EST.bind at h <;> split at h
  all_goals try { cases h }
  all_goals
    rename_i reader wm hr
    change EST.bind _ (fun _ => EST.pure (ForInStep.yield ())) wm = .ok step w' at h
    unfold EST.bind at h
    split at h
    · rename_i u wn hv
      cases u
      change EST.Out.ok (ForInStep.yield ()) wn = EST.Out.ok step w' at h
      cases h
      refine ⟨rfl, ?_⟩
      simp only [Checked, hop]
      exact ⟨reader, wm, hr, hv⟩
    · cases h

private theorem commands_success (schema : Authz.Schema) (driver : Driver)
    (commands : List (Authz.Issued × PostgresSql.Command))
    (w w' : Void IO.RealWorld)
    (h : forIn commands () (commandStep schema driver) w = .ok () w') :
    Executes schema driver commands w w' := by
  induction commands generalizing w with
  | nil =>
    change EST.Out.ok () w = EST.Out.ok () w' at h
    cases h
    exact .nil _
  | cons entry rest ih =>
    rw [List.forIn_cons] at h
    change EST.bind _ _ w = .ok () w' at h
    unfold EST.bind at h
    split at h
    · rename_i step wm hs
      obtain ⟨he, hc⟩ := commandStep_success schema driver entry.1 entry.2 w wm step hs
      subst step
      exact .cons hc (ih wm h)
    · cases h

/-- If the real process terminates normally, the up-front plan of all SQL succeeded, and in plan order each Driver call
and the matching of its result against the Outcome of Store.apply just before it succeeded. The first call starts from
the state at the start of process, and the IO states of adjacent stages agree. The returned response is the plan's
response, and SQL results are not added to it. The matcher internals, SQL semantics, external effects, COMMIT and HTTP
transport are not included. -/
theorem process_success (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver w = .ok response w') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      Executes app.schema driver plan.commands w w' ∧ response = plan.response := by
  unfold process at h
  cases hp : prepare app shape store request with
  | error e =>
    simp only [hp] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok plan =>
    simp only [hp] at h
    change EST.bind (forIn plan.commands () (commandStep app.schema driver))
      (fun _ => EST.pure plan.response) w = .ok response w' at h
    unfold EST.bind EST.pure at h
    split at h
    · rename_i u wm hs
      cases u
      cases h
      exact ⟨plan, rfl, commands_success app.schema driver plan.commands w w' hs, rfl⟩
    · cases h

/-- On normal termination of the real process, every SQL statement in the successfully executed and checked plan is
generated from an operation authorized for the same request principal, and also passes the shape check against the Store
just before it. The return value is the model response for the same Store/request. The meaning of the SQL strings and
the external effects of the FFI are not included. -/
theorem process_sql_authorized (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver w = .ok response w') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      Executes app.schema driver plan.commands w w' ∧
      response = (handleRequest app store request).result ∧
      ∀ i command, (i, command) ∈ plan.commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command := by
  obtain ⟨plan, hp, he, hr⟩ := process_success app shape store request driver w w' response h
  exact ⟨plan, hp, he, hr.trans (prepare_model app shape store request plan hp).1,
    prepare_sql_authorized app shape store request plan hp⟩

/-- For any Driver and starting IO state, if the actual process terminates normally, planning succeeded and the returned
response is exactly the model response for the same request. This works directly with the definitions of IO
bind/exceptions. FFI and SQL semantics, COMMIT and HTTP transport are not included. -/
theorem process_model (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (world world' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver world = .ok response world') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      response = plan.response ∧ response = (handleRequest app store request).result := by
  unfold process at h
  cases hp : prepare app shape store request with
  | error e =>
    simp only [hp] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok plan =>
    simp only [hp] at h
    change (EST.bind _ (fun _ => EST.pure plan.response)) world = .ok response world' at h
    unfold EST.bind EST.pure at h
    split at h
    · cases h
      exact ⟨plan, rfl, rfl, (prepare_model app shape store request plan hp).1⟩
    · cases h

/-- For the same App/authenticated request, if the model result lists passed to the continuation are equal and two
actual process runs terminate normally, their whole responses (status/body) are equal. The internal Store, shape, Driver
and IO states may each differ. Normal termination and equality of the result lists are hypotheses; availability on SQL
failure and permit/deny invariance are not claimed. -/
theorem process_response_eq_of_outcomes_eq (app : App) (request : AuthenticatedRequest)
    (s₁ s₂ : Store) (shape₁ shape₂ : PostgresShape.Shape) (driver₁ driver₂ : Driver)
    (w₁ w₁' w₂ w₂' : Void IO.RealWorld) (r₁ r₂ : Http.Response)
    (h₁ : process app shape₁ s₁ request driver₁ w₁ = .ok r₁ w₁')
    (h₂ : process app shape₂ s₂ request driver₂ w₂ = .ok r₂ w₂')
    (ho : ReadSafety.requestOutcomes app s₁ request = ReadSafety.requestOutcomes app s₂ request) :
    r₁ = r₂ := by
  obtain ⟨_, _, _, hr₁⟩ := process_model app shape₁ s₁ request driver₁ w₁ w₁' r₁ h₁
  obtain ⟨_, _, _, hr₂⟩ := process_model app shape₂ s₂ request driver₂ w₂ w₂' r₂ h₂
  exact hr₁.trans ((ReadSafety.response_eq_of_outcomes_eq app request s₁ s₂ ho).trans hr₂.symm)

/-- The real DB driver. External effects are dispatched by the record's content: an `async` call is written to the
    outbox on the same connection (the request's transaction) (`Outbox.enqueue`); everything else is sent or issued
    (`ExternalSend.send`). -/
def driver (conn : LeanPq.Handle) (external : ExternalSend.Config := {}) : Driver where
  read := fun command => do
    return PostgresResult.reader (← Postgres.exec conn command.sql command.parameters .tuplesOk)
  write := fun command => do
    return PostgresWrite.reader (← Postgres.exec conn command.sql command.parameters .commandOk)
  external := fun e =>
    match e.payload with
    | .call _ _ _ _ .async => do
      Outbox.enqueue conn e
      pure .none
    | payload => ExternalSend.send external payload

/-- A new connection. Returns only the filtered handler response, after a checked COMMIT. Authentication is the
responsibility of a separate part of the core; a principal chosen by the handler is not accepted.
-/
def handle (conninfo : String) (app : App) (shape : PostgresShape.Shape) (request : AuthenticatedRequest) : IO Http.Response := do
  let .ok () := PostgresShape.validateSchema shape app.schema | invalid
  PostgresLoad.withSnapshot conninfo app.schema fun conn store =>
    process app shape store request (driver conn)

/-- If the real handle terminates normally, the real process terminates normally from the Store obtained by collect on
the same connection, and the returned response is exactly the model response on that Store. The response can be
reproduced by a result-list replayer that does not receive the Store, each operation in the plan is authorized for the
request principal, and each row passed to the continuation comes from the target row of an authorized read in the plan.
The order BEGIN/collect/process/COMMIT is shown separately by withSnapshot_success. Nothing is claimed about the
external effects of SQL/FFI, agreement between the fetched Store and the real DB, or HTTP transport. -/
theorem handle_read_safety (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (request : AuthenticatedRequest) (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : handle conninfo app shape request w = .ok response w') :
    ∃ conn store wa wb wc plan,
      PostgresLoad.collect app.schema (PostgresLoad.driver conn) wa = .ok store wb ∧
      process app shape store request (driver conn) wb = .ok response wc ∧
      prepare app shape store request = .ok plan ∧
      response = (handleRequest app store request).result ∧
      ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some response ∧
      (∀ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
      (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
        ∃ i ∈ plan.commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  unfold handle at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    obtain ⟨conn, store, _, _, _, wa, wb, wc, _, _, _, _, _, _, hcollect, hp, _, _, _⟩ :=
      PostgresLoad.withSnapshot_success conninfo app.schema _ w w' response h
    obtain ⟨plan, hplan, hr, hmodel⟩ := process_model app shape store request (driver conn) wb wc response hp
    obtain ⟨hreplay, ha, hrow⟩ := prepare_read_safety app shape store request plan hplan
    exact ⟨conn, store, wa, wb, wc, plan, hcollect, hp, hplan, hmodel,
      by simpa [← hr] using hreplay, ha, hrow⟩

/-- If the real handle terminates normally, everything from the new connection through idle, BEGIN/inTransaction,
up-front generation of all SELECTs and the real Reader's metadata and NULL/value/byte-length fetches, Store restoration,
process on the same Store, the health check, and COMMIT/idle succeeds in consecutive IO states. All rows of the same
extraction results satisfy the per-tag JSON decoding relation, and their Map.make is the model's input Store. The
response equals the model response on that Store and can be reproduced by a result-list replayer without the Store. Each
Driver call in plan order and its matching against the expected result of Store.apply just before it succeed in
consecutive IO states from the start to the end of process. Each SQL statement's extraction result is, for a read,
either absent or exactly one expected row with the target primary key, and for a write, exactly the expected Outcome.
The state after matching remains the state at the end of extraction, and this extraction-match sequence also has the
same order and IO states. For each read, the same Reader's status → row count → column count → projection metadata → all
cell fetches are consecutive, and NULL/value/UTF-8 byte length and the row and column counts correspond. All rows of the
same result have ValueRow's per-tag JSON decoding relation, tied all the way to the match with the expected row above.
For each write, the same Reader's status → row count → column count → affected count → tag fetches are consecutive, and
commandOk, zero rows and columns, a canonical count of 0/1 and the per-operation tag correspond to the expected Outcome.
Each SQL statement of the same plan is generated from an operation authorized for the request principal, and the
operation's shape check also succeeds. Each row appearing in the result list comes from the row that an authorized read
in that plan points to in the model Store just before it. Agreement with the JSON parser internals, Map lookup, SQL
semantics, the external DB's actual state/persistence, FFI and HTTP transport is not included. Determining the request
principal from the JWT is the responsibility of a separate connection boundary. -/
theorem handle_cells_read_safety (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (request : AuthenticatedRequest) (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : handle conninfo app shape request w = .ok response w') :
    ∃ conn store wc w₀ w₁ w₂ w₃ w₄ w₅ w₆ commands results rows plan,
      PostgresShape.validateSchema shape app.schema = .ok () ∧
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      PostgresLoad.collect app.schema (PostgresLoad.driver conn) w₂ = .ok store w₃ ∧
      (app.schema.tables.map Prod.fst).eraseDups = app.schema.tables.map Prod.fst ∧
      List.Forall₂ (fun table entry => entry.1 = table ∧
        PostgresSql.selectTable app.schema table = .ok entry.2)
        (app.schema.tables.map Prod.fst) commands ∧
      PostgresLoad.SelectCells app.schema (PostgresLoad.driver conn) commands results w₂ w₃ ∧
      PostgresSnapshot.restore app.schema results = .ok store ∧
      List.Forall₂ (fun entry decoded => ∃ columns,
        (app.schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
        entry.2.columns = "_nyxis_id" :: columns ∧
        List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
        results rows ∧
      store = Cedar.Data.Map.make rows.flatten ∧
      process app shape store request (driver conn) w₃ = .ok response w₄ ∧
      (Postgres.driver conn).status w₄ = .ok .inTransaction w₅ ∧
      (Postgres.driver conn).command "COMMIT" w₅ = .ok "COMMIT" w₆ ∧
      (Postgres.driver conn).status w₆ = .ok .idle w' ∧
      prepare app shape store request = .ok plan ∧
      Executes app.schema (driver conn) plan.commands w₃ w₄ ∧
      Extracts app.schema (driver conn) plan.commands w₃ w₄ ∧
      (∀ i command, (i, command) ∈ plan.commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command) ∧
      response = (handleRequest app store request).result ∧
      ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some response ∧
      (∀ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
      (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
        ∃ i ∈ plan.commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  unfold handle at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    obtain ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆,
      hc, hi, hb, hs, hcollect, hp, hh, hm, he⟩ :=
      PostgresLoad.withSnapshot_success conninfo app.schema _ w w' response h
    obtain ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩ :=
      PostgresLoad.collect_cells_values app.schema (PostgresLoad.driver conn) w₂ w₃ store hcollect
    obtain ⟨plan, hplan, hexec, hmodel, hsql⟩ :=
      process_sql_authorized app shape store request (driver conn) w₃ w₄ response hp
    have hr := (prepare_model app shape store request plan hplan).1
    obtain ⟨hreplay, ha, hrow⟩ := prepare_read_safety app shape store request plan hplan
    exact ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆, commands, results, rows, plan,
      rfl, hc, hi, hb, hs, hcollect, distinct, compiled, selected, restored, related, constructed,
      hp, hh, hm, he, hplan, hexec, Executes.extracts _ _ _ _ _ hexec, hsql, hmodel, by simpa only [hr, ← hmodel] using hreplay, ha, hrow⟩

/-! ## Staged execution (point lookups)

`handle` fetches all tables, then computes `handleRequest` purely and replays the issued operations to SQL. The
per-request cost is proportional to the size of the whole DB. `handleStaged`, for each handler action call:

1. Fetches only the entities needed for the decision by point lookups and assembles the partial fetch `Known`
   (`PostgresMaterials.load`; for a list, the rows of the target table that match the query filters; also the rows seen
   by constraint decisions — rows with the same values for a uniqueness tuple, referenced rows, and rows referencing the
   rows removed by a delete).
2. Checks the shape of the fetched rows (`PostgresShape.validateStore`), and checks with the executable check
   `Authz.coversStep` that the fetch covers the decision materials (if it fails, the whole request is closed).
3. Makes the authorization layer's decision `Authz.step` using only the fetched rows, pre-checks the issued operations
   (`planCommands`), replays them to SQL, and matches them against the expected values from the preceding state (the
   fetched rows) (the same `verifyRead` / `PostgresWrite.verify` as `handle`).
4. If the decision recorded an external effect (issuing a signed URL for an attachment, sending mail, an external API
   call), then for that record only, asks Storage to issue, sends the mail, calls the external API, or writes an `async`
   call to the outbox in the same transaction (`Driver.external`; failure is an exception and the whole request becomes
   503, and the transaction is rolled back).
5. Continues the handler with the decision's result (for an external effect, together with the issuance result).

No `Store` of all tables exists in Lean. `StagedRun` is the record of normal termination (each stage's fetch, checks,
decision, execution and issuance), and `Chain` states that each stage's fetch is consistent with the whole state at that
point (the state after applying the operations of the preceding stages) (at the connection layer, the Assumption 1 trust that "the
results of point lookups are the DB's current rows"); from both, `StagedRun.model` derives with
`Authz.step_eq_of_covers` that the response, the issued list (principal, action, operation) and the external-effect
records (principal, generated values, action, kind, target, path) match `runHandler` (and hence `handleRequest`).
`StagedRun.sql` and `StagedRun.external` state, without trust, that each executed SQL statement (`commands`; this
excludes the INSERT written to the outbox inside `Driver.external`) and each requested issuance, send and outbox record
is authorized on the fetched materials. Starting a scheduled job (`AuthenticatedRequest.job`) also flows through the
same path (`App.handlerOf` selects the scheduled job). -/

open Nyxis.Materials (Known)

/-- If there is an external-effect record, performs the issuance/send (for an `async` call, the write to the outbox) for
    that record only (one call has at most one record). If there is no record, does nothing and has no result. -/
def sendExternal (driver : Driver) : List Authz.External → IO Authz.ExternalResult
  | [] => pure .none
  | e :: _ => driver.external e

/-- Interprets the handler in stages. For each call: point lookups → shape check → closure check → decision → SQL replay
    and matching → external-effect issuance → continuation. The value of an external effect's result does not change the
    decision (the issued operations and records) (`Authz.step_external_indep`), so SQL and issuance are performed with
    the decision's records from before the result is obtained, and after obtaining the result the same call proceeds
    with the result. -/
def runStaged (app : App) (shape : PostgresShape.Shape) (driver : Driver) (principal : Authz.Principal)
    (generated : Authz.Generated) : Handler Http.Response → IO Http.Response
  | .pure a => pure a
  | .call action key values query k => do
    let known ← PostgresMaterials.load app.schema app.policies driver.read principal generated action key values
      query
    let .ok () := PostgresShape.validateStore shape known.rows | invalid
    unless Authz.coversStep app.schema app.policies known principal generated action key values query do invalid
    let pre := Authz.step app.schema app.policies principal generated known.rows action key values query .none
    let .ok commands := planCommands app.schema shape pre.issued | invalid
    for (issued, command) in commands do
      let expected := (issued.store.apply issued.op).2
      match issued.op with
      | .read _ _ => verifyRead app.schema issued.op expected (← driver.read command)
      | _ => PostgresWrite.verify issued.op expected (← driver.write command)
    let ext ← sendExternal driver pre.external
    runStaged app shape driver principal generated
      (k (Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome)

/-- The record of normal termination of staged execution: the partial fetch used by each call (`knowns`), the executed
    SQL and its operations (`commands`, in execution order), the recorded external effects (`externals`, in order of
    occurrence), and the external-effect results obtained from outside (`exts`, one per call: Storage's signed URLs
    and external API responses). Each stage consists of a
    successful fetch, the shape check of the fetched rows, the closure check, the pre-check of `step`'s issuance using
    only the fetched rows, execution and matching in plan order (`Executes`), successful issuance/send for the recorded
    external effects (`sendExternal`), and the record of the continuation advanced with `step`'s result (together with
    the issuance result), with consecutive IO states. -/
inductive StagedRun (app : App) (shape : PostgresShape.Shape) (driver : Driver) (principal : Authz.Principal)
    (generated : Authz.Generated) :
    Handler Http.Response → List Known → List (Authz.Issued × PostgresSql.Command) → List Authz.External →
      List Authz.ExternalResult → Http.Response → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | pure (a : Http.Response) (w : Void IO.RealWorld) :
      StagedRun app shape driver principal generated (.pure a) [] [] [] [] a w w
  | call {action : Cedar.Spec.EntityUID} {key : Key} {values : Row} {query : ListQuery}
      {k : Outcome → Handler Http.Response}
      {known : Known} {commands rest : List (Authz.Issued × PostgresSql.Command)} {knowns : List Known}
      {externals : List Authz.External} {ext : Authz.ExternalResult} {exts : List Authz.ExternalResult}
      {response : Http.Response} {w w₁ w₂ w₃ w' : Void IO.RealWorld} :
      PostgresMaterials.load app.schema app.policies driver.read principal generated action key values query w
        = .ok known w₁ →
      PostgresShape.validateStore shape known.rows = .ok () →
      Authz.coversStep app.schema app.policies known principal generated action key values query = true →
      planCommands app.schema shape
        (Authz.step app.schema app.policies principal generated known.rows action key values query ext).issued
        = .ok commands →
      Executes app.schema driver commands w₁ w₂ →
      sendExternal driver
        (Authz.step app.schema app.policies principal generated known.rows action key values query ext).external w₂
        = .ok ext w₃ →
      StagedRun app shape driver principal generated
        (k (Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome)
        knowns rest externals exts response w₃ w' →
      StagedRun app shape driver principal generated (.call action key values query k) (known :: knowns)
        (commands ++ rest)
        ((Authz.step app.schema app.policies principal generated known.rows action key values query ext).external
          ++ externals)
        (ext :: exts) response w w'

/-- If the real runStaged terminates normally, then for each call, successful point lookups, the shape check of the
fetched rows, the closure check, the pre-check of step's issuance using only the fetched rows, SQL execution in plan
order and matching against the expected values from the preceding state, and successful issuance/send for the
recorded external effects succeed in consecutive IO states, and the continuation advances with step's result (together
with the issuance result) (`StagedRun`). Agreement between the fetch and the external DB, SQL semantics, Storage
behavior, COMMIT and HTTP transport are not included. -/
theorem runStaged_success (app : App) (shape : PostgresShape.Shape) (driver : Driver)
    (principal : Authz.Principal) (generated : Authz.Generated) (h : Handler Http.Response) :
    ∀ (w w' : Void IO.RealWorld) (response : Http.Response),
      runStaged app shape driver principal generated h w = .ok response w' →
      ∃ knowns commands externals exts,
        StagedRun app shape driver principal generated h knowns commands externals exts response w w' := by
  induction h with
  | pure a =>
    intro w w' response hr
    change EST.Out.ok a w = EST.Out.ok response w' at hr
    cases hr
    exact ⟨[], [], [], [], .pure a w⟩
  | call action key values query k ih =>
    intro w w' response hr
    rw [runStaged] at hr
    obtain ⟨known, w₁, hload, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
    cases hv : PostgresShape.validateStore shape known.rows with
    | error e =>
      simp only [hv] at hr
      change EST.Out.error _ _ = EST.Out.ok _ _ at hr
      cases hr
    | ok u =>
      cases u
      simp only [hv] at hr
      cases hc : Authz.coversStep app.schema app.policies known principal generated action key values query with
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨_, _, hf, _⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
        change EST.Out.error _ _ = EST.Out.ok _ _ at hf
        cases hf
      | true =>
        simp only [hc, ↓reduceIte] at hr
        cases hp : planCommands app.schema shape
            (Authz.step app.schema app.policies principal generated known.rows action key values query .none).issued with
        | error e =>
          simp only [hp] at hr
          change EST.Out.error _ _ = EST.Out.ok _ _ at hr
          cases hr
        | ok commands =>
          simp only [hp] at hr
          obtain ⟨u, w₂, hs, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
          cases u
          obtain ⟨ext, w₃, hsign, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
          obtain ⟨knowns, rest, externals, exts, hrest⟩ := ih _ w₃ w' response hr
          obtain ⟨hi, he, _⟩ :=
            Authz.step_external_indep app.schema app.policies principal generated known.rows action key values query .none ext
          refine ⟨known :: knowns, commands ++ rest, _, ext :: exts,
            .call hload hv hc ?_ (commands_success app.schema driver commands w₁ w₂ hs) ?_ hrest⟩
          · rw [← hi]; exact hp
          · rw [← he]; exact hsign

/-- Each stage's fetch is consistent with the whole state at that point: the fetch is consistent with the whole state
    (`Known.Consistent`), it has fetched all rows the decision sees through filters (list candidates, rows with the same
    values for a uniqueness tuple, rows referencing the rows removed by a delete; `Authz.rowFilters`) (the filtered row
    lists agree), and the same holds for the continuation with respect to the result decided on the whole state (if
    consistent, the same as the result on the fetched rows; the external-effect result is the same value `ext`) and the
    state after applying its operations. At the connection layer this corresponds to the trust that "the results of
    point lookups (for filters, the SELECT with a WHERE clause) are the DB's current rows" (`ASSUMPTIONS.md` Assumption 1), which
    cannot be checked in Lean. -/
inductive Chain (schema : Authz.Schema) (policies : Cedar.Spec.Policies) (principal : Authz.Principal)
    (generated : Authz.Generated) : Store → Handler α → List Known → List Authz.ExternalResult → Prop where
  | pure (full : Store) (a : α) : Chain schema policies principal generated full (.pure a) [] []
  | call {full : Store} {action : Cedar.Spec.EntityUID} {key : Key} {values : Row} {query : ListQuery}
      {k : Outcome → Handler α} {known : Known} {knowns : List Known} {ext : Authz.ExternalResult}
      {exts : List Authz.ExternalResult} :
      known.Consistent full →
      (∀ tf ∈ Authz.rowFilters schema known.rows action key values query,
        Authz.matchingRows known.rows tf.1 tf.2 = Authz.matchingRows full tf.1 tf.2) →
      Chain schema policies principal generated
        (Authz.step schema policies principal generated full action key values query ext).store
        (k (Authz.step schema policies principal generated full action key values query ext).outcome) knowns exts →
      Chain schema policies principal generated full (.call action key values query k) (known :: knowns) (ext :: exts)

/-- If each stage's fetch in the staged-execution record is consistent with the whole state at that point (`Chain`), the
response is exactly the return value of the pure runHandler from the same initial state and the same list of
external-effect results, and the list of operations corresponding to each executed SQL statement (principal, generated
values, action, operation) and the list of recorded external effects (principal, generated values, action, kind, target,
path) also match runHandler's issued list and record list, including order (`Authz.step_eq_of_covers`). Only the store
of each recorded operation and external effect is the state of the fetched rows, which differs from the whole state. -/
theorem StagedRun.model {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ full : Store, Chain app.schema app.policies principal generated full h knowns exts →
      response = (runHandler app.schema app.policies principal generated full exts h).result ∧
      (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
        = (runHandler app.schema app.policies principal generated full exts h).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
      externals.map Authz.External.view
        = (runHandler app.schema app.policies principal generated full exts h).external.map Authz.External.view := by
  induction hs with
  | pure a w =>
    intro full hc
    cases hc
    exact ⟨rfl, rfl, rfl⟩
  | call hload hshape hcov hplan hexec hsign hrest ih =>
    intro full hc
    cases hc with
    | call hcons hlist hchain =>
      obtain ⟨ho, hi, he⟩ :=
        Authz.step_eq_of_covers app.schema app.policies _ full principal generated _ _ _ _ _ hcons hcov hlist
      rw [ho] at ih
      obtain ⟨hr, hissued, hext⟩ := ih _ hchain
      simp only [runHandler, List.map_append, planCommands_issued _ _ _ _ hplan, List.headD_cons, List.tail_cons]
      exact ⟨hr, by rw [hi, hissued], by rw [he, hext]⟩

/-- The SQL of the operations issued in the staged-execution record (`commands`; the point-lookup SELECTs for decision
materials are outside the record, inside `PostgresMaterials.load`) is generated from operations authorized for the
principal of the same request on the materials fetched at that stage, and those operations also pass the shape check
against the state of the fetched rows. This is a claim that does not trust agreement between the fetch and the external
DB (authorization on the whole state is connected by `StagedRun.model` and `Authz.step_eq_of_covers`). SQL string
semantics are not included. -/
theorem StagedRun.sql {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ i command, (i, command) ∈ commands →
      i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
  induction hs with
  | pure a w => intro i command hm; simp at hm
  | @call action key values query k known commands rest knowns externals ext exts response w w₁ w₂ w₃ w' hload hshape
      hcov hplan hexec hsign hrest ih =>
    intro i command hm
    rcases List.mem_append.mp hm with hm | hm
    · have hi : i ∈ (Authz.step app.schema app.policies principal generated known.rows action key values
          query ext).issued := by
        rw [← planCommands_issued _ _ _ _ hplan]
        exact List.mem_map.mpr ⟨(i, command), hm, rfl⟩
      obtain ⟨hp, _, ha, _⟩ := Authz.step_authorized _ _ _ _ _ _ _ _ _ _ i hi
      exact ⟨hp, ha, planCommands_compiled _ _ _ _ hplan i command hm⟩
    · exact ih i command hm

/-- The external effects recorded in the staged-execution record (issuing signed URLs for attachments, sending mail,
external API calls) are authorized for the principal and server-generated values of the same request on the materials
fetched at that stage (`Authz.ExternalAuthorized`: a declared effect, a permit on the target row, content determined by
nyxis). Issuance to Storage, sending mail, calling the external API, and recording an `async` call in the outbox
(`Driver.external`) were performed at each stage for this record only (`sendExternal`). This is a claim that does not
trust agreement between the fetch and the external DB. The behavior of Storage, the relay and the destination, and the
internals of `Driver.external` (that the sent content and the outbox INSERT match the record), are not included. -/
theorem StagedRun.external {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
      Authz.ExternalAuthorized app.schema app.policies e := by
  induction hs with
  | pure a w => intro e he; simp at he
  | call hload hshape hcov hplan hexec hsign hrest ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hp, hg, _, _, _, _, ha⟩ := Authz.step_external _ _ _ _ _ _ _ _ _ _ e he
      exact ⟨hp, hg, ha⟩
    · exact ih e he

/-- The staged-execution record has the list of results that each stage's step (the decision using only the fetched
rows) passed to the continuation, and the response can be reproduced by a replayer that does not receive the Store
(`ReadSafety.replay`) from only the handler and that result list. Each row appearing in that result list is the row that
an authorized read for the same principal, among the operations issued in the same record (corresponding to SQL), points
to in the rows fetched at that stage (the operation's `store`). This is a claim that does not trust agreement between
the fetch and the external DB, and there is no other input through which rows fetched for the authorization decision
reach the response (the same property as `replayRequest`/row provenance on the `handle` path). Observation of result
tags, handler constants, request-derived values and the content of signed URLs are not restricted. -/
theorem StagedRun.replay {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∃ os : List Outcome, ReadSafety.replay h os = some response ∧
      ∀ row, Outcome.ok (some row) ∈ os →
        ∃ i ∈ commands.map Prod.fst,
          i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  induction hs with
  | pure a w => exact ⟨[], rfl, by intro row hm; simp at hm⟩
  | @call action key values query k known commands rest knowns externals ext exts response w w₁ w₂ w₃ w' hload hshape
      hcov hplan hexec hsign hrest ih =>
    obtain ⟨os, hr, hrow⟩ := ih
    refine ⟨(Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome
      :: os, hr, ?_⟩
    intro row hm
    rcases List.mem_cons.mp hm with ho | ho
    · obtain ⟨i, hi, hp, _, ha, hstore, _, table, hop, hfind⟩ :=
        step_entries app.schema app.policies principal generated known.rows action key values query ext (key, row)
          (by rw [← ho]; simp [Outcome.entries])
      refine ⟨i, ?_, hp, ha, table, key, hop, by rw [hstore]; exact hfind⟩
      rw [List.map_append]
      apply List.mem_append_left
      rw [planCommands_issued _ _ _ _ hplan]
      exact hi
    · obtain ⟨i, hi, hrest'⟩ := hrow row ho
      exact ⟨i, by rw [List.map_append]; exact List.mem_append_right _ hi, hrest'⟩

/-- The fixed response when a 2xx response of an external API call (`sync`) did not match its declared type. It contains
    no diagnostics or response body. The transaction has been rolled back (the failure path of `Postgres.transaction`).
    -/
def gatewayResponse : Http.Response := { status := .badGateway, body := "external response invalid" }

/-- The body of the transaction on one connection: selects the handler by routing (for a scheduled-job start, that
    selection; `App.handlerOf`) and interprets it in stages. -/
def stagedBody (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (request : AuthenticatedRequest) (conn : LeanPq.Handle) : IO Http.Response :=
  match app.handlerOf request with
  | none => pure { status := .notFound, body := "not found" }
  | some handler => runStaged app shape (driver conn external) request.principal request.generated handler

/-- A new connection. Selects the handler by routing (for a scheduled-job start, that selection; `App.handlerOf`),
    interprets it in stages, and returns only the filtered response after a checked COMMIT. Authentication is the
    responsibility of a separate part of the core; a principal chosen by the handler is not accepted. An effect of a
    kind with no external-effect configuration fails (exception; the whole request becomes 503), and other effects are
    unaffected. Only the failure where an external API call's response did not match its declared type
    (`CallSend.invalidResponse`) is mapped, after rolling back the transaction, to the fixed 502 (`gatewayResponse`).
    Other exceptions propagate unchanged (the fixed 503 at the entry point). -/
def handleStaged (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (request : AuthenticatedRequest) : IO Http.Response := do
  let .ok () := PostgresShape.validateSchema shape app.schema | invalid
  try Postgres.withTransaction conninfo (stagedBody app shape external request)
  catch e => if CallSend.isInvalidResponse e then pure gatewayResponse else throw e

/-- The staged-execution record of one request. If routing has no match, there is no fetch, no SQL and no issuance, and
    the response is 404. -/
def StagedRequest (app : App) (shape : PostgresShape.Shape) (driver : Driver) (request : AuthenticatedRequest)
    (knowns : List Known) (commands : List (Authz.Issued × PostgresSql.Command)) (externals : List Authz.External)
    (exts : List Authz.ExternalResult) (response : Http.Response) (w w' : Void IO.RealWorld) : Prop :=
  match app.handlerOf request with
  | none =>
    knowns = [] ∧ commands = [] ∧ externals = [] ∧ exts = [] ∧
      response = { status := .notFound, body := "not found" } ∧ w' = w
  | some handler =>
    StagedRun app shape driver request.principal request.generated handler knowns commands externals exts response w w'

/-- For one request, each stage's fetch is consistent with the whole state at that point (`Chain`). -/
def ChainRequest (app : App) (full : Store) (request : AuthenticatedRequest) (knowns : List Known)
    (exts : List Authz.ExternalResult) : Prop :=
  match app.handlerOf request with
  | none => knowns = [] ∧ exts = []
  | some handler => Chain app.schema app.policies request.principal request.generated full handler knowns exts

/-- If each stage's fetch in the staged-execution record of one request is consistent with the whole state, the response
is exactly the response of the pure handleRequest on the same initial state together with the list of external-effect
results obtained from outside, and the list of operations corresponding to each executed SQL statement (principal,
generated values, action, operation) and the list of recorded external effects (principal, generated values, action,
kind, target, path) match handleRequest's issued list and record list. -/
theorem StagedRequest.model {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∀ full : Store, ChainRequest app full request knowns exts →
      response = (handleRequest app full { request with externals := exts }).result ∧
      (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
        = (handleRequest app full { request with externals := exts }).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
      externals.map Authz.External.view
        = (handleRequest app full { request with externals := exts }).external.map Authz.External.view := by
  intro full hc
  unfold StagedRequest at hs
  unfold ChainRequest at hc
  simp only [handleRequest, App.handlerOf_externals]
  split at hs
  · rename_i hr
    obtain ⟨_, rfl, rfl, rfl, rfl, _⟩ := hs
    simp [hr]
  · rename_i handler hr
    simp only [hr] at hc ⊢
    exact hs.model full hc

/-- For the staged-execution record of one request, the response can be reproduced by a replayer that does not receive
the Store (`ReadSafety.replayRequest`) from only the request and each stage's result list, and each row in the result
list is the row that an authorized read for the same principal, issued in the same record, points to in the rows fetched
at that stage (if routing has no match, the result list is empty). -/
theorem StagedRequest.replay {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
      ∀ row, Outcome.ok (some row) ∈ os →
        ∃ i ∈ commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  unfold StagedRequest at hs
  split at hs
  · rename_i hr
    obtain ⟨_, rfl, _, _, rfl, _⟩ := hs
    exact ⟨[], by simp [ReadSafety.replayRequest, hr], by intro row hm; simp at hm⟩
  · rename_i handler hr
    obtain ⟨os, hreplay, hrow⟩ := hs.replay
    exact ⟨os, by simp only [ReadSafety.replayRequest, hr]; exact hreplay, hrow⟩

/-- The external effects recorded in the staged-execution record of one request are authorized for the principal and
server-generated values of the same request on the materials fetched at that stage (no trust). -/
theorem StagedRequest.external {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∀ e ∈ externals, e.principal = request.principal ∧ e.generated = request.generated ∧
      Authz.ExternalAuthorized app.schema app.policies e := by
  unfold StagedRequest at hs
  split at hs
  · obtain ⟨_, _, rfl, _, _, _⟩ := hs
    intro e he; simp at he
  · exact hs.external

/-- If the real handleStaged terminates normally, the model/shape consistency check succeeds, and everything from the
new connection through idle, BEGIN/inTransaction, the staged-execution record of the routed request (for each call:
point lookups, shape check, closure check, decision using only the fetched rows, pre-check of issuance, SQL execution in
plan order and matching, issuance/send of the recorded external effects), the health check, and COMMIT/idle succeeds in
consecutive IO states. The SQL of the issued operations (`commands`; the point-lookup SELECTs for decision materials are
inside each stage's `load`) is generated from operations authorized for the principal of the same request on the
materials fetched at that stage, and also passes the shape check. The recorded external effects (`externals`) are
authorized for the principal and generated values of the same request on the materials fetched at that stage, and
issuance to Storage, sending mail and calling the external API were performed only for that content. The response can be
reproduced by a replayer that does not receive the Store from only the request and each stage's result list, and each
row in the result list is the row that an authorized read for the same principal points to in the rows fetched at that
stage (no trust). If each stage's fetch is consistent with the whole state at that point (trusted as Assumption 1 at the
connection layer), the response is exactly the response of handleRequest on the same initial state and the list of
results obtained from outside, and the list of operations corresponding to the SQL (principal, generated values, action,
operation) and the list of external-effect records match handleRequest's issued list and record list. Agreement between
the fetch and the external DB's actual state, SQL semantics, Storage behavior, persistence and HTTP transport are not
included. Determining the request principal from the JWT is the responsibility of a separate connection boundary. The
other normal termination is the fixed 502 (`gatewayResponse`) that maps only the failure where an external API call's
response did not match its declared type (`CallSend.invalidResponse`); in that case the transaction of the same body has
failed with that exception (there is no COMMIT, and the response is a fixed value containing no internally fetched rows
or diagnostics). -/
theorem handleStaged_success (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (request : AuthenticatedRequest) (w w' : Void IO.RealWorld)
    (response : Http.Response)
    (h : handleStaged conninfo app shape external request w = .ok response w') :
    PostgresShape.validateSchema shape app.schema = .ok () ∧
    ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      StagedRequest app shape (driver conn external) request knowns commands externals exts response w₂ w₃ ∧
      (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
      (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
      (Postgres.driver conn).status w₅ = .ok .idle w' ∧
      (∀ i command, (i, command) ∈ commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command) ∧
      (∀ e ∈ externals, e.principal = request.principal ∧ e.generated = request.generated ∧
        Authz.ExternalAuthorized app.schema app.policies e) ∧
      (∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
        ∀ row, Outcome.ok (some row) ∈ os →
          ∃ i ∈ commands.map Prod.fst,
            i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
            ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
      (∀ full : Store, ChainRequest app full request knowns exts →
        response = (handleRequest app full { request with externals := exts }).result ∧
        (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
          = (handleRequest app full { request with externals := exts }).issued.map
              (fun i => (i.principal, i.generated, i.action, i.op)) ∧
        externals.map Authz.External.view
          = (handleRequest app full { request with externals := exts }).external.map Authz.External.view)) ∨
     (response = gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
      Postgres.withTransaction conninfo (stagedBody app shape external request) w = .error e w')) := by
  unfold handleStaged at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    refine ⟨rfl, ?_⟩
    change EST.tryCatch (Postgres.withTransaction conninfo (stagedBody app shape external request))
      (fun e => if CallSend.isInvalidResponse e then pure gatewayResponse else throw e) w = .ok response w' at h
    unfold EST.tryCatch at h
    cases ht : Postgres.withTransaction conninfo (stagedBody app shape external request) w with
    | error e wt =>
      simp only [ht] at h
      by_cases hinv : CallSend.isInvalidResponse e = true
      · simp only [hinv, ↓reduceIte] at h
        change EST.Out.ok gatewayResponse wt = EST.Out.ok response w' at h
        cases h
        exact Or.inr ⟨rfl, e, hinv, rfl⟩
      · simp only [hinv] at h
        change EST.Out.error e wt = EST.Out.ok response w' at h
        cases h
    | ok value wt =>
      simp only [ht] at h
      change EST.Out.ok value wt = EST.Out.ok response w' at h
      cases h
      left
      obtain ⟨conn, wc, hc, ht⟩ := Postgres.withTransaction_success conninfo _ w w' response ht
      obtain ⟨w₀, w₁, w₂, w₃, w₄, w₅, hi, hb, hs, hbody, hh, hm, he⟩ :=
        Postgres.transaction_success _ _ wc w' response ht
      unfold stagedBody at hbody
      cases hr : app.handlerOf request with
      | none =>
        simp only [hr] at hbody
        change EST.Out.ok _ w₂ = EST.Out.ok response w₃ at hbody
        cases hbody
        refine ⟨conn, wc, w₀, w₁, w₂, w₂, w₄, w₅, [], [], [], [], hc, hi, hb, hs, ?_, hh, hm, he, ?_, ?_, ?_, ?_⟩
        · simp [StagedRequest, hr]
        · intro i command hm; simp at hm
        · intro e he; simp at he
        · exact ⟨[], by simp [ReadSafety.replayRequest, hr], by intro row hm; simp at hm⟩
        · intro full _
          simp [handleRequest, App.handlerOf_externals, hr]
      | some handler =>
        simp only [hr] at hbody
        obtain ⟨knowns, commands, externals, exts, hstaged⟩ :=
          runStaged_success app shape (driver conn external) request.principal request.generated _ w₂ w₃ response hbody
        have hreq : StagedRequest app shape (driver conn external) request knowns commands externals exts response w₂ w₃ := by
          unfold StagedRequest
          simp only [hr]
          exact hstaged
        exact ⟨conn, wc, w₀, w₁, w₂, w₃, w₄, w₅, knowns, commands, externals, exts, hc, hi, hb, hs, hreq, hh, hm, he,
          hstaged.sql, hreq.external, hreq.replay, hreq.model⟩

end Nyxis.Internal.PostgresRun
