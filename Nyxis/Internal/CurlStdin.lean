/-! Shared helper that launches the approved curl with its configuration passed on standard input (`--config -`) (core
only, unproven; the curl of Assumptions 1 and 2). Used by `StorageSign`, `MailSend` and `CallSend`. Credentials and request values are
placed only inside the configuration and never appear in the process arguments. Diagnostics (stderr) are discarded, and
the child process is always reaped. -/
namespace Nyxis.Internal.CurlStdin

/-- Write the configuration to standard input. Takes ownership of the handle, which is closed when the last reference is
    dropped on return (this tells curl the configuration has ended; if it is not closed, curl keeps waiting for more).
    -/
private def feed (stdin : IO.FS.Handle) (input : String) : IO Bool := do
  try
    stdin.putStr input
    stdin.flush
    pure true
  catch _ => pure false

/-- Launch `curl <args>`, pass `input` on standard input, and return the exit code and standard output. -/
def run (args : Array String) (input : String) : IO (UInt32 × String) := do
  let spawned ← IO.Process.spawn {
    cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .null }
  -- Do not refer to the original child-process value afterwards (a remaining reference to its stdin keeps the handle
  -- open).
  let (stdin, child) ← spawned.takeStdin
  let fed ← feed stdin input
  try
    let output ← child.stdout.readToEnd
    let code ← child.wait
    return (if fed then code else 1, output)
  catch _ =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    return (1, "")

/-- Turn a string into a quoted value for curl's configuration (escaping `\`, `"` and newlines). -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n" else if c == '\r' then "\\r"
    else c.toString) ++ "\""

end Nyxis.Internal.CurlStdin
