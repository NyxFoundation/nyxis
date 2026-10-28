import Std.Time
import Nyxis.Authz

/-! サーバー生成値の実装(Assumption 2 の時計と Assumption 1 のランタイムの乱数に当たる。定理の外)。
要求ごとに現在時刻と新しい一意 ID を決める。接続コード(`PostgresHttp.dispatch`)が認証の直後に 1 度だけ呼び、
その値を `Runtime.AuthenticatedRequest.generated` としてハンドラと認可層に渡す。要求のどの項目からも値を決めない。
純粋モデルと定理は任意の値について成り立ち、一意性や時計の正しさは主張しない。 -/
namespace Nyxis.Internal.Generated

/-- 1 バイトを小文字 2 桁の 16 進にする。 -/
def hex2 (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b / 16).toNat '0', digits.getD (b % 16).toNat '0']

/-- 16 バイトの乱数から UUID(RFC 9562 の版 4、variant 1)の文字列を作る。バイトが足りなければ 0 で埋める
    (`fresh` は 16 バイトを要求する)。 -/
def uuidOf (bytes : ByteArray) : String :=
  let at_ := fun (i : Nat) => bytes.data.getD i 0
  let byte := fun (i : Nat) =>
    if i == 6 then (at_ 6 &&& 0x0f) ||| 0x40
    else if i == 8 then (at_ 8 &&& 0x3f) ||| 0x80
    else at_ i
  let hex := fun (is : List Nat) => String.join (is.map fun i => hex2 (byte i))
  s!"{hex [0, 1, 2, 3]}-{hex [4, 5]}-{hex [6, 7]}-{hex [8, 9]}-{hex [10, 11, 12, 13, 14, 15]}"

/-- 現在時刻(ミリ秒。Cedar の `datetime` の範囲外なら失敗)と、ランタイムの乱数 16 バイトからの UUID。 -/
def fresh : IO Authz.Generated := do
  let now ← Std.Time.Timestamp.now
  let some dt := Cedar.Spec.Ext.Datetime.datetime? now.toMillisecondsSinceUnixEpoch.toInt
    | throw (IO.userError "clock out of datetime range")
  let bytes ← IO.getRandomBytes 16
  unless bytes.size == 16 do throw (IO.userError "random source failure")
  return { now := dt, id := uuidOf bytes }

end Nyxis.Internal.Generated
