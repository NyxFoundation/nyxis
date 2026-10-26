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
#guard roundtrip (.prim (.string "日本語🌍\n\"\\'; DROP TABLE Post;--"))
#guard roundtrip (.prim (.string ""))
#guard roundtrip (.prim (.entityUID ⟨⟨"User", ["a", "b"]⟩, "u'\"::1"⟩))
#guard encode (.prim (.string "User::\"u\"")) !=
  encode (.prim (.entityUID ⟨⟨"User", []⟩, "u"⟩))

-- 拡張値: decimal(内部表現は 10^4 倍の Int64)、datetime / duration(ミリ秒の Int64)。
#guard roundtrip (.ext (.decimal (Int64.ofInt (-12345))))
#guard roundtrip (.ext (.decimal ((Ext.Decimal.parse "1234.5678").getD 0)))
#guard roundtrip (.ext (.datetime ⟨Int64.ofInt 1700000000000⟩))
#guard roundtrip (.ext (.datetime ((Ext.Datetime.parse "2026-10-22T05:39:36.123Z").getD ⟨0⟩)))
#guard roundtrip (.ext (.datetime ⟨Int64.ofInt (-9223372036854775808)⟩))
#guard roundtrip (.ext (.duration ⟨Int64.ofInt (-86400000)⟩))
-- タグが型を区別する: 同じ内部表現でも int / decimal / datetime / duration は別のセル。
#guard encode (.prim (.int 1700)) != encode (.ext (.decimal (Int64.ofInt 1700)))
#guard encode (.ext (.datetime ⟨Int64.ofInt 1700⟩)) != encode (.ext (.duration ⟨Int64.ofInt 1700⟩))
#guard encode (.ext (.decimal (Int64.ofInt 1700))) != encode (.ext (.datetime ⟨Int64.ofInt 1700⟩))
#guard (encode (.ext (.datetime ⟨Int64.ofInt 1700000000000⟩))).toOption ==
  some "[\"datetime\",\"1700000000000\"]"
#guard (encode (.ext (.decimal (Int64.ofInt (-12345))))).toOption == some "[\"decimal\",\"-12345\"]"

-- 集合: スカラーの集合は正規化された集合に戻る。空集合も往復する。
#guard roundtrip (.set (Cedar.Data.Set.make [user "b", user "a", user "b"]))
#guard roundtrip (.set (Cedar.Data.Set.make [.prim (.string "x"), .prim (.string "y")]))
#guard roundtrip (.set (Cedar.Data.Set.make [.ext (.datetime ⟨Int64.ofInt 1⟩), .ext (.datetime ⟨Int64.ofInt 2⟩)]))
#guard roundtrip (.set Cedar.Data.Set.empty)
#guard (encode (.set (Cedar.Data.Set.make [user "a"]))).toOption ==
  some "[\"set\",[[\"entity\",[],\"User\",\"a\"]]]"
-- 順序の違う要素列を復号しても同じ集合になる。
#guard decode "[\"set\",[[\"int\",\"2\"],[\"int\",\"1\"],[\"int\",\"2\"]]]" ==
  .ok (.set (Cedar.Data.Set.make [.prim (.int 1), .prim (.int 2)]))

-- レコード: スカラーの属性を持つレコード。空のレコードも往復する。
#guard roundtrip (.record (Cedar.Data.Map.make
  [("title", .prim (.string "t")), ("pinned", .prim (.bool true)), ("owner", user "a"),
   ("at", .ext (.datetime ⟨Int64.ofInt 5⟩)), ("price", .ext (.decimal (Int64.ofInt 10000)))]))
#guard roundtrip (.record Cedar.Data.Map.empty)
#guard (encode (.record (Cedar.Data.Map.make [("b", .prim (.bool true)), ("a", .prim (.int 1))]))).toOption ==
  some "[\"record\",[[\"a\",[\"int\",\"1\"]],[\"b\",[\"bool\",true]]]]"

-- fixture の全プリミティブ値が保存形式を往復して元の Cedar 値に戻る。
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
-- 入れ子の集合・レコード、集合でない要素列、重複する属性名、NUL を含む属性名は拒む。
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
