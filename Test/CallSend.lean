import Nyxis.Internal.CallSend

/-!
# Test.CallSend — 外部 API 呼び出しの接続層の純粋部分

応答の寛容な復号(`CallSend.decode`: 宣言したキーの欠落と型違いだけを拒み、余分なキーは捨てる)、本文の JSON、curl の
設定(認証ヘッダと本文は設定の中にだけ置く)、curl の出力の分解を `#guard` で検査する。実際の送信(模擬 API への HTTPS)は
統合テスト(`Test.ExternalCalls` と `scripts/check-external-calls.py`)で行う。
-/

namespace Test.CallSend

open Cedar.Spec
open Cedar.Data
open Nyxis.Db
open Nyxis.Internal.CallSend

def strV (s : String) : Value := .prim (.string s)
def intV (n : Int) : Value := .prim (.int (Int64.ofInt n))

def chargeTy : Cedar.Validation.CedarType :=
  .record (Map.make [("id", .required .string), ("status", .required .string),
    ("meta", .optional (.record (Map.make [("n", .required .int)]))),
    ("tags", .optional (.set .string)), ("when", .optional (.ext .datetime)), ("owner", .optional (.entity ⟨"User", []⟩))])

def parse (s : String) : Lean.Json := (Lean.Json.parse s).toOption.getD .null

-- 宣言したキーだけが残り、余分なキーは捨てる
#guard decode chargeTy (parse "{\"id\":\"ch_1\",\"status\":\"ok\",\"extra\":[1,2]}")
  == some (.record (Map.make [("id", strV "ch_1"), ("status", strV "ok")]))
-- 省略可のキーは有れば復号、無ければ無い。入れ子・集合・日時・実体参照
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{\"n\":7,\"x\":1},\"tags\":[\"a\",\"b\",\"a\"],\"when\":1700000000000,\"owner\":\"alice\"}")
  == some (.record (Map.make [("id", strV "c"), ("status", strV "s"), ("meta", .record (Map.make [("n", intV 7)])),
    ("tags", .set (Set.make [strV "a", strV "b"])), ("when", .ext (.datetime ⟨1700000000000⟩)),
    ("owner", .prim (.entityUID ⟨⟨"User", []⟩, "alice"⟩))]))
-- 省略不可のキーの欠落、型違い(トップレベル・入れ子・集合の要素)は拒む
#guard decode chargeTy (parse "{\"id\":\"ch_1\"}") == none
#guard decode chargeTy (parse "{\"id\":1,\"status\":\"ok\"}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{\"n\":\"seven\"}}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{}}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"tags\":[\"a\",1]}") == none
-- オブジェクトでない応答、null は拒む
#guard decode chargeTy (parse "[1]") == none
#guard decode chargeTy (parse "null") == none
#guard decode chargeTy (parse "{\"id\":null,\"status\":\"s\"}") == none
-- 整数: 小数は拒み、Int64 の範囲外は拒む。1e2 のような整数を表す数は受ける
#guard decode .int (parse "12") == some (intV 12)
#guard decode .int (parse "1.5") == none
#guard decode .int (parse "1e2") == some (intV 100)
#guard decode .int (parse "9223372036854775808") == none
#guard decode .int (parse "-9223372036854775808") == some (.prim (.int (Int64.ofInt (-9223372036854775808))))
-- 真偽値・文字列・decimal
#guard decode (.bool .anyBool) (parse "true") == some (.prim (.bool true))
#guard decode .string (parse "\"x\"") == some (strV "x")
#guard decode (.ext .decimal) (parse "\"1.5\"") == some (.ext (.decimal (Int64.ofInt 15000)))
#guard decode (.ext .decimal) (parse "1.5") == none

-- 本文の JSON: 列の名前と値(実体参照は ID、日時はエポックミリ秒。キーの順は JSON として同じなら問わない)
#guard (Lean.Json.parse (body [("subject", strV "s"), ("n", intV 7), ("doc", .prim (.entityUID ⟨⟨"Doc", []⟩, "d1"⟩)),
  ("at", .ext (.datetime ⟨1700000000000⟩))])).toOption == some (parse "{\"subject\":\"s\",\"n\":7,\"doc\":\"d1\",\"at\":1700000000000}")

-- curl の設定: URL・メソッド・本文(Content-Type つき)・認証ヘッダは設定の中にだけ。GET では本文も Content-Type も無い
#guard configText "https://api.example/v1/charges/n1" .post (some [("n", intV 7)]) (some "Authorization: Bearer secret")
  == "url = \"https://api.example/v1/charges/n1\"\nrequest = \"POST\"\nheader = \"Content-Type: application/json\"\ndata = \"{\\\"n\\\":7}\"\nheader = \"Authorization: Bearer secret\"\n"
#guard configText "https://api.example/v1/charges/n1" .get none none
  == "url = \"https://api.example/v1/charges/n1\"\nrequest = \"GET\"\n"
-- 引数に認証ヘッダ・URL・本文は現れない(固定の輸送の方針だけ)
#guard (arguments 3 10 65536).all fun a => !(a.splitOn "Authorization").length > 1 && !(a.splitOn "https://").length > 1
#guard (arguments 3 7 1024).contains "7" && (arguments 3 7 1024).contains "1024" && (arguments 3 7 1024).contains "=https"

-- 出力の分解: 本文 + 改行 + 状態コード
#guard splitOutput "{\"id\":\"c\"}\n200" == some (200, "{\"id\":\"c\"}")
#guard splitOutput "line1\nline2\n404" == some (404, "line1\nline2")
#guard splitOutput "\n204" == some (204, "")
#guard splitOutput "no code" == none

-- 認証方式ごとのヘッダの行(設定の読み込みは環境変数を要するので、行の形だけ)
#guard (CallMethod.get.hasBody, CallMethod.delete.hasBody, CallMethod.post.hasBody, CallMethod.put.hasBody,
  CallMethod.patch.hasBody) == (false, false, true, true, true)
#guard [CallMethod.get, .post, .put, .patch, .delete].map CallMethod.name == ["GET", "POST", "PUT", "PATCH", "DELETE"]

end Test.CallSend
