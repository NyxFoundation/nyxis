import Nyxis.Internal.Cors

/-!
# Test.Cors — CORS 設定の単体検査

`Nyxis.Internal.Cors` の純粋関数(オリジンの妥当性、設定の解析、要求の Origin の照合、応答ヘッダの装飾)を
`#guard` で検査する。
実サンプルに対する統合検査は `scripts/check-cors.py`。
-/

namespace Test.Cors

open Nyxis.Internal.Cors

-- 明示的な HTTP(S) オリジンだけを受け入れる。
#guard validOrigin "http://127.0.0.1:3000"
#guard validOrigin "https://example.test"
#guard validOrigin "https://app.example.test:8443"
#guard validOrigin "http://[::1]:3000"
#guard !validOrigin ""
#guard !validOrigin "example.test"
#guard !validOrigin "HTTPS://example.test"
#guard !validOrigin "https://example.test/"
#guard !validOrigin "https://example.test/path"
#guard !validOrigin "https://example.test?x=1"
#guard !validOrigin "https://example.test:"
#guard !validOrigin "https://user@example.test"
#guard !validOrigin "https://user:pw@example.test"
#guard !validOrigin "https://"
#guard !validOrigin "https://example.test:0x1"
#guard !validOrigin "https://*.example.test"
#guard !validOrigin "null"
#guard !validOrigin "https://例.test"

-- 設定は `,` 区切り。空なら CORS 無効。空白は除き、重複は 1 つに。不正な要素が 1 つでもあれば全体を拒む。
#guard (parse "").toOption.map (·.allowedOrigins) == some []
#guard (parse "http://127.0.0.1:3000, http://localhost:3000").toOption.map (·.allowedOrigins) ==
  some ["http://127.0.0.1:3000", "http://localhost:3000"]
#guard (parse "https://a.test,https://a.test").toOption.map (·.allowedOrigins) == some ["https://a.test"]
#guard !(parse "https://a.test,").isOk
#guard !(parse ",https://a.test").isOk
#guard !(parse "https://a.test, *").isOk
#guard !(parse "https://a.test/").isOk

/-- `Origin` ヘッダを `values` の順に持つ要求ヘッダ。 -/
private def origins (values : List String) : Std.Http.Headers :=
  Std.Http.Headers.ofList (values.map fun value => (.origin, Std.Http.Header.Value.ofString! value))

private def config : Config := { allowedOrigins := ["http://127.0.0.1:3000", "https://example.test"] }

/-- 要求が許可され、その Origin がそのまま返るか。 -/
private def granted (values : List String) : Option String :=
  (allowed config (origins values)).map (·.value)

-- 許可オリジンは一致したときだけ、そのままの文字列で返す。
#guard granted ["http://127.0.0.1:3000"] == some "http://127.0.0.1:3000"
#guard granted ["https://example.test"] == some "https://example.test"
-- 非許可・不正・欠落・重複の Origin には何も返さない(正規化や接尾辞の一致はしない)。
#guard granted ["http://127.0.0.1:3001"] == none
#guard granted ["http://localhost:3000"] == none
#guard granted ["https://example.test/"] == none
#guard granted ["HTTPS://example.test"] == none
#guard granted ["https://evil.example.test"] == none
#guard granted ["null"] == none
#guard granted [] == none
#guard granted ["https://example.test", "https://example.test"] == none
#guard granted ["https://example.test", "http://127.0.0.1:3000"] == none
-- 許可一覧が空なら、どの Origin にも返さない。
#guard (allowed {} (origins ["https://example.test"])).isNone

/-- ETag と Location を設定したハンドラの応答(本文なし)。 -/
private def handlerResponse : Std.Http.Response Std.Http.Body.Any :=
  ((Nyxis.Http.responseBuilder ⟨.created, "x", [(.etag, "\"v1\""), (.location, "/docs/1")]⟩).body
    ({} : Std.Http.Body.Empty) : Std.Http.Response Std.Http.Body.Empty)

/-- `decorate` した応答の `name` ヘッダの値(すべて)。 -/
private def decorated (values : List String) (preflight : Bool) (name : String) : Option (List String) :=
  ((decorate config (origins values) preflight handlerResponse).line.headers.getAll?
    (Std.Http.Header.Name.ofString! name)).map (·.toList.map (·.value))

-- 許可したオリジンにだけ、プリフライトには固定の Allow-Methods / Allow-Headers(Authorization とハンドラに渡す
-- 要求ヘッダ)を、それ以外の応答には固定の Expose-Headers(ハンドラが設定できる ETag・Location)を 1 つずつ付ける。
#guard decorated ["https://example.test"] true "Access-Control-Allow-Headers" ==
  some ["Authorization, Content-Type, Accept, Accept-Language, If-Match, If-None-Match"]
#guard decorated ["https://example.test"] true "Access-Control-Expose-Headers" == none
#guard decorated ["https://example.test"] false "Access-Control-Expose-Headers" == some ["ETag, Location"]
#guard decorated ["https://example.test"] false "Access-Control-Allow-Headers" == none
#guard decorated ["https://example.test"] false "Access-Control-Allow-Origin" == some ["https://example.test"]
-- 許可しない・無い Origin には CORS のヘッダを付けず、Vary だけを付ける。
#guard decorated ["https://other.test"] false "Access-Control-Allow-Origin" == none
#guard decorated ["https://other.test"] false "Access-Control-Expose-Headers" == none
#guard decorated ["https://other.test"] true "Access-Control-Allow-Headers" == none
#guard decorated ["https://other.test"] false "Vary" == some ["Origin"]
#guard decorated [] false "Access-Control-Allow-Origin" == none
#guard decorated [] false "Access-Control-Expose-Headers" == none
#guard decorated [] true "Access-Control-Allow-Headers" == none
#guard decorated [] false "Vary" == some ["Origin"]

end Test.Cors
