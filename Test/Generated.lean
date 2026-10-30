import Nyxis.Internal.Generated

/-!
# Test.Generated — the pure part of the server-generated values

Checks with `#guard` that `Nyxis.Internal.Generated.uuidOf` builds an RFC 9562 version 4 / variant 1 UUID string from 16
bytes. The check of `fresh`, which uses the real clock and randomness, is in the executable `checkHttpAuth`
(`Test/HttpAuth.lean`).
-/

namespace Test.Generated

open Nyxis.Internal.Generated

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def zeros : ByteArray := bytes (List.replicate 16 0)
def ones : ByteArray := bytes (List.replicate 16 0xff)
def probe : ByteArray := bytes
  [0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]

-- Shape: 8-4-4-4-12 lowercase hex, the version digit is 4, the variant digit is 8~b
#guard uuidOf zeros == "00000000-0000-4000-8000-000000000000"
#guard uuidOf ones == "ffffffff-ffff-4fff-bfff-ffffffffffff"
#guard uuidOf probe == "12345678-9abc-4ef0-9122-334455667788"
#guard (uuidOf probe).length == 36
#guard ((uuidOf probe).toList.filter (· == '-')).length == 4
-- Missing bytes are filled with 0 (`fresh` requires 16 bytes)
#guard uuidOf (bytes [0xab]) == "ab000000-0000-4000-8000-000000000000"
#guard hex2 0 == "00" && hex2 255 == "ff" && hex2 0x1f == "1f"

end Test.Generated
