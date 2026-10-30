import Std.Time
import Nyxis.Authz

/-! Implementation of the server-generated values (corresponding to the A2 clock and the A4 runtime randomness; outside
the theorem). Determines the current time and a new unique ID per request. The connection code (`PostgresHttp.dispatch`)
calls it exactly once right after authentication and passes the values to the handler and the authorization layer as
`Runtime.AuthenticatedRequest.generated`. The values are not derived from any field of the request. The pure model and
the theorem hold for arbitrary values and make no claim about uniqueness or clock correctness. -/
namespace Nyxis.Internal.Generated

/-- Formats one byte as two lowercase hex digits. -/
def hex2 (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b / 16).toNat '0', digits.getD (b % 16).toNat '0']

/-- Builds a UUID string (RFC 9562 version 4, variant 1) from 16 random bytes. Missing bytes are filled with 0 (`fresh`
    requires 16 bytes). -/
def uuidOf (bytes : ByteArray) : String :=
  let at_ := fun (i : Nat) => bytes.data.getD i 0
  let byte := fun (i : Nat) =>
    if i == 6 then (at_ 6 &&& 0x0f) ||| 0x40
    else if i == 8 then (at_ 8 &&& 0x3f) ||| 0x80
    else at_ i
  let hex := fun (is : List Nat) => String.join (is.map fun i => hex2 (byte i))
  s!"{hex [0, 1, 2, 3]}-{hex [4, 5]}-{hex [6, 7]}-{hex [8, 9]}-{hex [10, 11, 12, 13, 14, 15]}"

/-- The current time (milliseconds; fails if outside Cedar's `datetime` range) and a UUID from 16 bytes of runtime
    randomness. -/
def fresh : IO Authz.Generated := do
  let now ← Std.Time.Timestamp.now
  let some dt := Cedar.Spec.Ext.Datetime.datetime? now.toMillisecondsSinceUnixEpoch.toInt
    | throw (IO.userError "clock out of datetime range")
  let bytes ← IO.getRandomBytes 16
  unless bytes.size == 16 do throw (IO.userError "random source failure")
  return { now := dt, id := uuidOf bytes }

end Nyxis.Internal.Generated
