import LeanPq

/-! Dependency smoke check, not a PostgreSQL integration test.
`lake exe checkPostgresDependency` exercises the libpq FFI without opening a connection.
Import the full library so Lean/toolchain incompatibilities are caught by the default build.
-/

private def payload := "Robert'; DROP TABLE users;--"
private def rendered := (LeanPq.Expr.litStr (columns := []) payload).render {}
#guard rendered.1 == "$1"
#guard rendered.2.params == #[payload]

def main : IO Unit := do
  -- PQunescapeBytea works locally and does not need credentials or a running server.
  match ← (LeanPq.Extern.PqUnescapeBytea "\\x6e79786973").toBaseIO with
  | .ok decoded =>
    unless decoded == "nyxis" do
      throw <| IO.userError "lean-pq/libpq: unexpected bytea decoding result"
    IO.println "lean-pq: import, parameter rendering, native link and libpq call passed"
  | .error e => throw <| IO.userError s!"lean-pq/libpq: {e}"
