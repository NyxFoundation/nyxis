import Nyxis.Internal.HttpAuth
import Nyxis.Internal.Generated

open Nyxis Nyxis.Internal

private def headers (values : List String) : Std.Http.Headers :=
  Std.Http.Headers.ofList (values.map fun value =>
    (Std.Http.Header.Name.ofString! "aUtHoRiZaTiOn", Std.Http.Header.Value.ofString! value))

private def check (values : List String) (expected : Option String) : IO Unit := do
  unless HttpAuth.bearer (headers values) == expected do
    throw (IO.userError "Bearer extraction mismatch")
  let calls ← IO.mkRef ([] : List String)
  let principal ← HttpAuth.principalOf ⟨"User", []⟩ (fun token => do
    calls.modify (· ++ [token])
    pure (some "verified-user")) (headers values)
  unless (← calls.get) == expected.toList && principal ==
      (if expected.isSome then .user ⟨⟨"User", []⟩, "verified-user"⟩ else .anonymous) do
    throw (IO.userError "Verifier call or principal mismatch")

def main : IO Unit := do
  for values in [[], [""], ["Bearer"], ["Basic alice"], ["Bearer a b"],
      ["Bearer a,b"], ["Bearer a\tb"], ["Bearer\ta"], ["Bearer a", "Bearer b"],
      ["Bearer a", "Bearer a"], ["Bearer a, Bearer b"]] do
    check values none
  for value in ["Bearer opaque-token", "bEaReR opaque-token", "Bearer   opaque-token"] do
    check [value] (some "opaque-token")
  for subject in [none, some "", some "   ", some "bad\x00id"] do
    let p ← HttpAuth.principalOf ⟨"User", []⟩ (fun _ => pure subject) (headers ["Bearer opaque"])
    unless p == .anonymous do throw (IO.userError "Invalid subject accepted")
  let p ← HttpAuth.principalOf ⟨"User", []⟩
    (fun _ => throw (IO.userError "secret JWT verification error")) (headers ["Bearer opaque"])
  unless p == .anonymous do throw (IO.userError "Verifier exception escaped")
  let p ← HttpAuth.principalOf Authz.anonymousType (fun _ => pure (some "alice"))
    (headers ["Bearer opaque"])
  unless p == .anonymous do throw (IO.userError "Reserved anonymous type accepted")
  let p ← HttpAuth.principalOf ⟨"User", []⟩ (fun _ => pure (some "Alice-Exact"))
    ((headers ["Bearer forged-root"]).insert! "X-Principal" "root")
  unless p == .user ⟨⟨"User", []⟩, "Alice-Exact"⟩ do
    throw (IO.userError "Subject was taken from request or normalized")
  let tick ← IO.mkRef (1000 : Int)
  let calls ← IO.mkRef ([] : List Int)
  let timed := HttpAuth.withClock (do
    let n ← tick.get
    tick.modify (· + 1)
    pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (.ofInt n))) (fun token now => do
      unless token == "opaque" do throw (IO.userError "credential changed")
      calls.modify (· ++ [now.toSecondsSinceUnixEpoch.val])
      pure (some "alice"))
  for _ in [0, 1] do
    unless (← timed "opaque") == some "alice" do
      throw (IO.userError "Timed verifier rejected")
  unless (← calls.get) == [1000, 1001] do
    throw (IO.userError "Clock cached or time changed")
  let called ← IO.mkRef false
  let failedClock := HttpAuth.withClock
    (throw (IO.userError "secret clock error")) (fun _ _ => do
      called.set true
      pure (some "alice"))
  unless (← failedClock "opaque") == none && !(← called.get) do
    throw (IO.userError "Clock failure reached verifier")
  unless (← HttpAuth.principalOf ⟨"User", []⟩ failedClock (headers ["Bearer opaque"])) ==
      .anonymous do throw (IO.userError "Clock failure authenticated")
  unless (← HttpAuth.withClock Std.Time.Timestamp.now
      (fun _ _ => throw (IO.userError "secret verifier error")) "opaque") == none do
    throw (IO.userError "Timed verifier failure escaped")
  let before ← Std.Time.Timestamp.now
  let observed ← IO.mkRef before
  unless (← HttpAuth.withCurrentTime (fun _ now => do
      observed.set now
      pure (some "alice")) "opaque") == some "alice" do
    throw (IO.userError "Wall-clock verification failed")
  let after ← Std.Time.Timestamp.now
  unless before ≤ (← observed.get) && (← observed.get) ≤ after do
    throw (IO.userError "Verifier did not receive current wall clock")
  -- サーバー生成値: 実時計のミリ秒が datetime になり、ID は版 4 の UUID で呼び出しごとに異なる
  let g1 ← Generated.fresh
  let g2 ← Generated.fresh
  let afterGen ← Std.Time.Timestamp.now
  unless before.toMillisecondsSinceUnixEpoch.toInt ≤ g1.now.val.toInt &&
      g1.now.val.toInt ≤ g2.now.val.toInt &&
      g2.now.val.toInt ≤ afterGen.toMillisecondsSinceUnixEpoch.toInt do
    throw (IO.userError "Generated time is not the current wall clock")
  let uuidShape : String → Bool := fun s =>
    let cs := s.toList
    s.length == 36 && (cs.filter (· == '-')).length == 4 &&
      cs.getD 14 ' ' == '4' && ['8', '9', 'a', 'b'].contains (cs.getD 19 ' ') &&
      cs.all (fun c => c == '-' || "0123456789abcdef".toList.contains c)
  unless uuidShape g1.id && uuidShape g2.id && g1.id != g2.id do
    throw (IO.userError "Generated id is not a fresh version-4 UUID")
  IO.println "HTTP authentication boundary: 26 cases passed (injected verifier and actual clock, no cryptography/Supabase); generated values: 2 fresh"
