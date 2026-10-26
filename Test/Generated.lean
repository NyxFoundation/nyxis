import Nyxis.Internal.Generated

/-!
# Test.Generated — サーバー生成値の純粋部分

`Nyxis.Internal.Generated.uuidOf` が 16 バイトから RFC 9562 の版 4 / variant 1 の UUID 文字列を作ることを
`#guard` で検査する。実時計と乱数を使う `fresh` の検査は実行ファイル `checkHttpAuth`(`Test/HttpAuth.lean`)。
-/

namespace Test.Generated

open Nyxis.Internal.Generated

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def zeros : ByteArray := bytes (List.replicate 16 0)
def ones : ByteArray := bytes (List.replicate 16 0xff)
def probe : ByteArray := bytes
  [0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]

-- 形: 8-4-4-4-12 の小文字 16 進、版の桁は 4、variant の桁は 8〜b
#guard uuidOf zeros == "00000000-0000-4000-8000-000000000000"
#guard uuidOf ones == "ffffffff-ffff-4fff-bfff-ffffffffffff"
#guard uuidOf probe == "12345678-9abc-4ef0-9122-334455667788"
#guard (uuidOf probe).length == 36
#guard ((uuidOf probe).toList.filter (· == '-')).length == 4
-- 足りないバイトは 0 で埋める(`fresh` は 16 バイトを要求する)
#guard uuidOf (bytes [0xab]) == "ab000000-0000-4000-8000-000000000000"
#guard hex2 0 == "00" && hex2 255 == "ff" && hex2 0x1f == "1f"

end Test.Generated
