import Std.Sync.Mutex
import Nyxis.Internal.PostgresHttp
import BulletinBoard.App
import BulletinBoardTest.Fixture

/-!
# BulletinBoardTest.ServeFixture — a test executable that starts with an in-process DB

Puts `BulletinBoard.app` behind the same HTTP entry point as the real server (`PostgresHttp.handleAuthenticatedWith`),
on top of an in-process `Store` whose initial state is `BulletinBoardTest.Fixture.store` (users alice, bob, root
(admin), and alice's published post pub1 and draft draft1). The principal is always anonymous. `scripts/check-http.sh`
starts it and confirms the HTTP wiring (method, path, and body reach the model, and the handler's response is returned
unchanged). It uses neither PostgreSQL nor JWT and is not for deployment.
-/

def main (args : List String) : IO Unit := do
  let port : UInt16 ← match args.head? with
    | none => pure 8081
    | some s => match s.toNat? with
      | some n => if 0 < n && n ≤ 65535 then pure n.toUInt16 else throw (IO.userError s!"port out of range: {s}")
      | none => throw (IO.userError s!"port is not a number: {s}")
  let store ← Std.Mutex.new BulletinBoardTest.Fixture.store
  -- Requests advance the model one at a time under a Mutex, so the processed sequence has the same shape as
  -- `Runtime.trace`.
  let backend : Nyxis.Runtime.AuthenticatedRequest → IO Nyxis.Http.Response := fun r =>
    store.atomically do
      let run := Nyxis.Runtime.handleRequest BulletinBoard.app (← get) r
      set run.store
      pure run.result
  IO.println s!"nyxis fixture: listening on port {port}"
  Nyxis.Http.serve port (Std.Http.Server.Handler.ofFn
    (Nyxis.Internal.PostgresHttp.handleAuthenticatedWith (fun _ => pure .anonymous) Nyxis.Internal.Generated.fresh backend))
