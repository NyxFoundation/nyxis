import Nyxis.Internal.PostgresValue
import Test.Fixture

open Cedar.Spec Nyxis.Internal.PostgresValue

private def roundtrip (v : Value) : Bool :=
  (encode v >>= decode) == .ok v

private def user (id : String) : Value := .prim (.entityUID ⟨⟨"User", []⟩, id⟩)

#guard roundtrip (.prim (.bool true))
#guard roundtrip (.prim (.bool false))
#guard roundtrip (.prim (.int (Int64.ofInt (-9223372036854775808))))
#guard roundtrip (.prim (.int (Int64.ofInt 9223372036854775807)))
#guard roundtrip (.prim (.int 0))
#guard roundtrip (.prim (.string "\u65E5\u672C\u8A9E🌍\n\"\\'; DROP TABLE Post;--"))
#guard roundtrip (.prim (.string ""))
#guard roundtrip (.prim (.entityUID ⟨⟨"User", ["a", "b"]⟩, "u'\"::1"⟩))
#guard encode (.prim (.string "User::\"u\"")) !=
  encode (.prim (.entityUID ⟨⟨"User", []⟩, "u"⟩))

-- Extension values: decimal (internally an Int64 scaled by 10^4), datetime / duration (an Int64 of milliseconds).
#guard roundtrip (.ext (.decimal (Int64.ofInt (-12345))))
#guard roundtrip (.ext (.decimal ((Ext.Decimal.parse "1234.5678").getD 0)))
#guard roundtrip (.ext (.datetime ⟨Int64.ofInt 1700000000000⟩))
#guard roundtrip (.ext (.datetime ((Ext.Datetime.parse "2026-10-22T05:39:36.123Z").getD ⟨0⟩)))
#guard roundtrip (.ext (.datetime ⟨Int64.ofInt (-9223372036854775808)⟩))
#guard roundtrip (.ext (.duration ⟨Int64.ofInt (-86400000)⟩))
-- The tag distinguishes types: with the same internal representation, int / decimal / datetime / duration are different
-- cells.
#guard encode (.prim (.int 1700)) != encode (.ext (.decimal (Int64.ofInt 1700)))
#guard encode (.ext (.datetime ⟨Int64.ofInt 1700⟩)) != encode (.ext (.duration ⟨Int64.ofInt 1700⟩))
#guard encode (.ext (.decimal (Int64.ofInt 1700))) != encode (.ext (.datetime ⟨Int64.ofInt 1700⟩))
#guard (encode (.ext (.datetime ⟨Int64.ofInt 1700000000000⟩))).toOption ==
  some "[\"datetime\",\"1700000000000\"]"
#guard (encode (.ext (.decimal (Int64.ofInt (-12345))))).toOption == some "[\"decimal\",\"-12345\"]"

-- Sets: a set of scalars comes back as the normalized set. The empty set also round-trips.
#guard roundtrip (.set (Cedar.Data.Set.make [user "b", user "a", user "b"]))
#guard roundtrip (.set (Cedar.Data.Set.make [.prim (.string "x"), .prim (.string "y")]))
#guard roundtrip (.set (Cedar.Data.Set.make [.ext (.datetime ⟨Int64.ofInt 1⟩), .ext (.datetime ⟨Int64.ofInt 2⟩)]))
#guard roundtrip (.set Cedar.Data.Set.empty)
#guard (encode (.set (Cedar.Data.Set.make [user "a"]))).toOption ==
  some "[\"set\",[[\"entity\",[],\"User\",\"a\"]]]"
-- Decoding element lists in a different order yields the same set.
#guard decode "[\"set\",[[\"int\",\"2\"],[\"int\",\"1\"],[\"int\",\"2\"]]]" ==
  .ok (.set (Cedar.Data.Set.make [.prim (.int 1), .prim (.int 2)]))

-- Records: records with scalar attributes. The empty record also round-trips.
#guard roundtrip (.record (Cedar.Data.Map.make
  [("title", .prim (.string "t")), ("pinned", .prim (.bool true)), ("owner", user "a"),
   ("at", .ext (.datetime ⟨Int64.ofInt 5⟩)), ("price", .ext (.decimal (Int64.ofInt 10000)))]))
#guard roundtrip (.record Cedar.Data.Map.empty)
#guard (encode (.record (Cedar.Data.Map.make [("b", .prim (.bool true)), ("a", .prim (.int 1))]))).toOption ==
  some "[\"record\",[[\"a\",[\"int\",\"1\"]],[\"b\",[\"bool\",true]]]]"

-- Every primitive value in the fixture round-trips through the storage format back to the original Cedar value.
#guard Test.Fixture.store.toList.all (fun (_, row) => row.toList.all (fun (_, v) => roundtrip v))

private def refused (s : String) : Bool := !(decode s).isOk
#guard refused "null"
#guard refused "not json"
#guard refused "[\"bool\",\"true\"]"
#guard refused "[\"bool\",true,0]"
#guard refused "[\"int\",9223372036854775807]"
#guard refused "[\"int\",\"9223372036854775808\"]"
#guard refused "[\"int\",\"-9223372036854775809\"]"
#guard refused "[\"int\",\"01\"]"
#guard refused "[\"int\",\"-0\"]"
#guard refused "[\"entity\",[1],\"User\",\"u\"]"
#guard refused "[\"entity\",[],\"User\"]"
#guard refused "[\"entity\",[],\"User\",null]"
#guard refused "[\"unknown\",true]"
#guard refused "[\"string\",\"\\u0000\"]"
#guard refused "[\"decimal\",12345]"
#guard refused "[\"decimal\",\"1.5\"]"
#guard refused "[\"datetime\",\"2026-10-22T00:00:00Z\"]"
#guard refused "[\"datetime\",\"9223372036854775808\"]"
#guard refused "[\"duration\",\"+1\"]"
#guard refused "[\"ipaddr\",\"127.0.0.1\"]"
-- Nested sets/records, element lists that are not sets, duplicate attribute names, and attribute names containing NUL
-- are rejected.
#guard refused "[\"set\",[[\"set\",[]]]]"
#guard refused "[\"set\",[[\"record\",[]]]]"
#guard refused "[\"set\",[\"int\",\"1\"]]"
#guard refused "[\"set\",[[\"int\",\"x\"]]]"
#guard refused "[\"set\",[]]" == false
#guard refused "[\"record\",[[\"a\",[\"int\",\"1\"]],[\"a\",[\"int\",\"2\"]]]]"
#guard refused "[\"record\",[[\"a\",[\"set\",[]]]]]"
#guard refused "[\"record\",[[\"\\u0000\",[\"int\",\"1\"]]]]"
#guard refused "[\"record\",[[\"a\"]]]"
#guard refused "[\"record\",[[1,[\"int\",\"1\"]]]]"
#guard refused "[\"record\",{\"a\":1}]"
#guard !(encode (.prim (.string (String.singleton '\x00')))).isOk
#guard !(encode (.prim (.entityUID ⟨⟨"User", [String.singleton '\x00']⟩, "u"⟩))).isOk
#guard !(encode (.set (Cedar.Data.Set.make [.set Cedar.Data.Set.empty]))).isOk
#guard !(encode (.set (Cedar.Data.Set.make [.record Cedar.Data.Map.empty]))).isOk
#guard !(encode (.record (Cedar.Data.Map.make [("a", .set Cedar.Data.Set.empty)]))).isOk
#guard !(encode (.record (Cedar.Data.Map.make [(String.singleton '\x00', .prim (.int 1))]))).isOk
#guard !(encode (.ext (.ipaddr ((Ext.IPAddr.ip "127.0.0.1").getD default)))).isOk
