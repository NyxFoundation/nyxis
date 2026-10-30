import LeanPq.Extern

/-! Turn a lean-pq FFI failure into an IO exception with a fixed message that contains no SQL, parameters, connection
string or server diagnostics. Each module of the connection layer uses this single conversion with its own message. -/
namespace Nyxis.Internal

def native (failure : String) (action : EIO LeanPq.Error α) : IO α := do
  match ← action.toBaseIO with
  | .ok value => pure value
  | .error _ => throw (IO.userError failure)

end Nyxis.Internal
