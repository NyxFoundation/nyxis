import Nyxis.Internal.SupabaseJwt
import Nyxis.Internal.PostgresHttp
import BulletinBoard.App
import BulletinBoardTest.Fixture
import Nyxis.Internal.PostgresShape

/-! Test-only actual ES256/JWKS verification at the existing HTTP seam.
The default backend uses the sample fixture store; connection mode uses real libpq
with an unreachable address, or a newly created local test database. Fixed clock and local fixture JWKS must never be used
by the production startup. -/
def main (args : List String) : IO Unit := do
  let dir :: port :: mode := args | throw <| IO.userError "expected fixture directory and port"
  unless mode == [] || mode == ["connection"] || mode == ["clock"] || mode == ["local-db"] || mode == ["local-auth"] do
    throw <| IO.userError "invalid test mode"
  let realAuth := mode == ["local-auth"]
  let issuer ← if realAuth then do
      let some value ← IO.getEnv "NYXIS_TEST_AUTH_ISSUER"
        | throw <| IO.userError "local Auth issuer required"
      unless value == "http://127.0.0.1:55321/auth/v1" ||
          value == "https://localhost:55325/auth/v1" do
        throw <| IO.userError "only local Auth is allowed in this test"
      pure value
    else pure "https://test.supabase.co/auth/v1"
  let jwksFile := if realAuth then "/local-auth-jwks.json" else "/test-jwks.json"
  let some _ ← Nyxis.Internal.SupabaseJwt.prepare issuer
      (← IO.FS.readFile (dir ++ jwksFile))
    | throw <| IO.userError "invalid fixture verifier"
  -- Test-only file transport. Production must fetch the configured HTTPS endpoint.
  let fetch := do pure (some (← IO.FS.readFile (dir ++ jwksFile)))
  let verify := if mode == ["clock"] || realAuth then
      Nyxis.Internal.SupabaseJwt.verifyFresh issuer fetch
    else Nyxis.Internal.SupabaseJwt.verifyFreshWithClock issuer fetch
      (pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt 1000)))
  if mode == ["connection"] || mode == ["local-db"] || realAuth then
    let .ok shape := Nyxis.Internal.PostgresShape.compile
        (← IO.FS.readFile (dir ++ "/schema.cedarschema"))
      | throw <| IO.userError "invalid fixture schema"
    -- All DB modes reach real libpq and never fall back to the fixture backend.
    -- local-db/local-auth are invoked only by the local endpoint/isolated DB test harness.
    let conninfo ← if mode == ["local-db"] || realAuth then do
        let some value ← IO.getEnv "NYXIS_DATABASE_URL"
          | throw <| IO.userError "test database required"
        pure value
      else pure "host=127.0.0.1 port=1 connect_timeout=1 password=test-secret"
    Nyxis.Internal.PostgresHttp.serveVerifiedApp port.toNat!.toUInt16
      conninfo
      BulletinBoard.app shape BulletinBoardTest.Fixture.userT verify
    return
  let backend : Nyxis.Runtime.AuthenticatedRequest → IO Nyxis.Http.Response := fun r => do
    if r.request.path == "/principal" then
      return ⟨.ok, match r.principal with
        | .anonymous => "anonymous"
        | .user uid => uid.eid⟩
    return (Nyxis.Runtime.handleRequest BulletinBoard.app BulletinBoardTest.Fixture.store r).result
  Nyxis.Http.serve port.toNat!.toUInt16 (Std.Http.Server.Handler.ofFn
    (Nyxis.Internal.PostgresHttp.handleAuthenticatedWith
      (Nyxis.Internal.HttpAuth.principalOf BulletinBoardTest.Fixture.userT verify) backend))
