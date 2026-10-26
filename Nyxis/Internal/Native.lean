import LeanPq.Extern

/-! lean-pq の FFI の失敗を、SQL・パラメータ・接続文字列・サーバの診断を含まない固定文言の IO 例外にする。
接続層の各モジュールはこの 1 つの変換を自分の文言で使う。 -/
namespace Nyxis.Internal

def native (failure : String) (action : EIO LeanPq.Error α) : IO α := do
  match ← action.toBaseIO with
  | .ok value => pure value
  | .error _ => throw (IO.userError failure)

end Nyxis.Internal
