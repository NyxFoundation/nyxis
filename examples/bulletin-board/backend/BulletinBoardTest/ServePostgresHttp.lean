import Nyxis.Internal.PostgresHttp
import BulletinBoard.App
import BulletinBoardTest.Fixture
import Nyxis.Internal.PostgresShapeBuild

nyxis_postgres_shape testPostgresShape from "../schema.cedarschema"

/-! Test-only HTTP backends: injected response/failure, or real libpq connection failure.
Neither mode is a deployment target or evidence of local Supabase integration. -/
def main (args : List String) : IO Unit := do
  let some port := (args.head?.getD "18112").toNat?.filter (fun n => 0 < n && n ≤ 65535) |>.map Nat.toUInt16
    | throw (IO.userError "port out of range")
  if args[1]? == some "connection" then
    Nyxis.Internal.PostgresHttp.serveVerifiedApp port
      "host=127.0.0.1 port=1 connect_timeout=1" BulletinBoard.app testPostgresShape
      BulletinBoardTest.Fixture.userT (fun _ => pure none)
  else
    let calls ← IO.mkRef (0 : Nat)
    let authCalls ← IO.mkRef (0 : Nat)
    let backend : Nyxis.Runtime.AuthenticatedRequest → IO Nyxis.Http.Response := fun r => do
      let count ← calls.get
      calls.set (count + 1)
      if r.request.path == "/authcalls" then return { status := .ok, body := toString (← authCalls.get) }
      if r.request.path == "/calls" then return { status := .ok, body := toString count }
      if r.request.path == "/failure" || r.request.path == "/health" then
        throw (IO.userError "secret connection string and uncommitted response")
      if r.request.path == "/probe" then
        unless r.principal == .anonymous do throw (IO.userError "principal changed")
        return { status := .created, body := s!"{r.request.method}|{r.request.path}|{r.request.body}|anonymous" }
      return (Nyxis.Runtime.handleRequest BulletinBoard.app BulletinBoardTest.Fixture.store r).result
    if args[1]? == some "auth" then
      -- Test-only opaque credentials, never a deployed verifier or a JWT implementation.
      let verify : String → IO (Option String) := fun token => do
        authCalls.modify (· + 1)
        match token with
        | "test-alice" => pure (some "alice")
        | "test-bob" => pure (some "bob")
        | "test-root" => pure (some "root")
        | "empty-subject" => pure (some "")
        | "verifier-error" => throw (IO.userError "secret verifier details")
        | _ => pure none
      Nyxis.Http.serve port (Std.Http.Server.Handler.ofFn
        (Nyxis.Internal.PostgresHttp.handleAuthenticatedWith
          (Nyxis.Internal.HttpAuth.principalOf BulletinBoardTest.Fixture.userT verify)
          Nyxis.Internal.Generated.fresh backend))
    else
      Nyxis.Http.serve port (Std.Http.Server.Handler.ofFn
        (Nyxis.Internal.PostgresHttp.handleAuthenticatedWith (fun _ => pure .anonymous) Nyxis.Internal.Generated.fresh backend))
