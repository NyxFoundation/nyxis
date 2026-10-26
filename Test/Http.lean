import Nyxis.Http

/-!
# Test.Http — HTTP の要約と応答の行の純粋検査

`Nyxis.Http` の純粋関数を `#guard` で検査する: 要求ヘッダの選別(`selectHeaders`。Authorization・Cookie を含む
列挙外の名前は落ちる)、問い合わせ文字列の復号(`decodeComponent` / `parseQuery`)、応答の行の構成(`responseBuilder`。
Content-Type の既定と、妥当でない値の破棄。`ResponseHeader` に無い名前は表せない)。
実 HTTP での統合検査は `scripts/check-http-headers.py`(実行ファイル `serveHttpHeaders`)。
-/

namespace Test.Http

open Nyxis Nyxis.Http

private def hdrs (pairs : List (String × String)) : Std.Http.Headers :=
  Std.Http.Headers.ofList (pairs.map fun p =>
    (Std.Http.Header.Name.ofString! p.1, Std.Http.Header.Value.ofString! p.2))

/-! ## 要求ヘッダの選別 -/

-- 列挙した名前だけが受け取った順に残り、Authorization・Cookie・その他は落ちる。名前の大小は区別しない。
#guard selectHeaders (hdrs [("Authorization", "Bearer secret"), ("Cookie", "s=1"), ("Accept", "application/json"),
    ("X-Principal", "root"), ("CONTENT-TYPE", "text/plain"), ("If-None-Match", "\"v1\""), ("Accept", "text/html"),
    ("Accept-Language", "ja"), ("If-Match", "\"v2\""), ("Set-Cookie", "a=b"), ("Proxy-Authorization", "Basic x"),
    ("Host", "example.test")]) ==
  [(.accept, "application/json"), (.contentType, "text/plain"), (.ifNoneMatch, "\"v1\""), (.accept, "text/html"),
   (.acceptLanguage, "ja"), (.ifMatch, "\"v2\"")]
#guard selectHeaders (hdrs []) == []
#guard selectHeaders (hdrs [("Authorization", "Bearer secret"), ("Cookie", "s=1")]) == []
-- 選別の名前に Authorization・Cookie は無く、名前からの変換もそれらに対しては `none`。
#guard RequestHeader.all.all (fun h => h.name != "authorization" && h.name != "cookie")
#guard RequestHeader.ofName? "authorization" == none
#guard RequestHeader.ofName? "cookie" == none
#guard RequestHeader.ofName? "accept" == some .accept
#guard RequestHeader.ofName? "if-none-match" == some .ifNoneMatch
#guard RequestHeader.all.map (·.name) == ["accept", "accept-language", "content-type", "if-none-match", "if-match"]

/-! ## 問い合わせ文字列 -/

#guard decodeComponent "a%20b+c" == some "a b c"
#guard decodeComponent "%E3%81%82" == some "あ"
#guard decodeComponent "plain" == some "plain"
#guard decodeComponent "" == some ""
#guard decodeComponent "%zz" == none
#guard decodeComponent "%4" == none
#guard decodeComponent "%" == none
#guard decodeComponent "%FF" == none
#guard parseQuery "x=1&name=a%20b&flag&=v&y=a=b&&bad=%zz" ==
  [("x", "1"), ("name", "a b"), ("flag", ""), ("", "v"), ("y", "a=b")]
#guard parseQuery "" == []
#guard ({ method := .get, path := "/docs", body := "", query := "limit=10&after=abc" } : Request).queryParam? "limit"
  == some "10"
#guard ({ method := .get, path := "/docs", body := "", query := "limit=10&limit=20" } : Request).queryParam? "limit"
  == some "10"
#guard ({ method := .get, path := "/docs", body := "" } : Request).queryParam? "limit" == none
#guard ({ method := .get, path := "/docs", body := "" } : Request).query == ""
#guard ({ method := .get, path := "/", body := "", headers := [(.accept, "a"), (.accept, "b")] } : Request).header? .accept
  == some "a"
#guard ({ method := .get, path := "/", body := "" } : Request).header? .accept == none

-- リクエスト行からの取り出し: パスは問い合わせを含まず、問い合わせは符号化のまま。
private def targetOf (s : String) : Std.Http.RequestTarget :=
  match Std.Http.URI.parse? s with
  | some uri => .absoluteForm uri
  | none => .originForm { segments := #[], absolute := true } none
#guard pathOf (targetOf "http://h/docs/1") == "/docs/1"
#guard queryOf (targetOf "http://h/docs/1") == ""
#guard pathOf (targetOf "http://h/docs?limit=10&name=a%20b+c&flag") == "/docs"
#guard queryOf (targetOf "http://h/docs?limit=10&name=a%20b+c&flag") == "limit=10&name=a%20b+c&flag"
#guard parseQuery (queryOf (targetOf "http://h/docs?limit=10&name=a%20b+c&flag")) ==
  [("limit", "10"), ("name", "a b c"), ("flag", "")]

/-! ## 応答の行 -/

private def lineOf (r : Response) := (responseBuilder r).line

/-- 応答の行にある `name` の値(受け取った順)。 -/
private def valuesOf (r : Response) (name : String) : List String :=
  (((lineOf r).headers.getAll? (Std.Http.Header.Name.ofString! name)).map (·.toList.map (·.value))).getD []

private def allowed : Response :=
  { status := .created, body := "", headers := [(.etag, "\"v1\""), (.cacheControl, "no-store"), (.location, "/docs/1")] }

-- Content-Type の既定と設定。同じ名前は最初のもの。
#guard valuesOf { status := .ok, body := "" } "content-type" == ["text/plain; charset=utf-8"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "application/json")] } "content-type"
  == ["application/json"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "application/json"), (.contentType, "text/html")] }
  "content-type" == ["application/json"]
-- 妥当でない値(改行を含む)は捨てる。Content-Type は既定に戻り、挿入を試みた名前は現れない。
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "text/html\r\nSet-Cookie: a=b")] }
  "content-type" == ["text/plain; charset=utf-8"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "text/html\r\nSet-Cookie: a=b")] }
  "set-cookie" == []
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "bad\nvalue")] } "etag" == []
-- 許可された他のヘッダ。
#guard valuesOf allowed "etag" == ["\"v1\""]
#guard valuesOf allowed "cache-control" == ["no-store"]
#guard valuesOf allowed "location" == ["/docs/1"]
#guard (lineOf allowed).status == .created
#guard (lineOf allowed).headers.toList.map (·.1.value) == ["content-type", "cache-control", "etag", "location"]
-- 同じ名前は最初のものだけ(2 つめ以降は妥当でも使わない)。
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "\"a\""), (.etag, "\"b\"")] } "etag" == ["\"a\""]
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "bad\nvalue"), (.etag, "\"b\"")] } "etag" == []
-- Cache-Control: 共有キャッシュへの保存を許す指示は no-store に置き換える(大小・空白を問わない)。
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "private, max-age=0")] } "cache-control"
  == ["private, max-age=0"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "public, max-age=60")] } "cache-control" == ["no-store"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "max-age=60, S-MaxAge = 10")] } "cache-control" == ["no-store"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, " Public ")] } "cache-control" == ["no-store"]
-- must-revalidate も認証付き応答の共有を許す(RFC 9111 §3.5)。新鮮な応答は再認可されずに再利用されうる。
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "max-age=60, must-revalidate")] }
  "cache-control" == ["no-store"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, " MuSt-ReVaLiDaTe ")] }
  "cache-control" == ["no-store"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "must-revalidate"),
    (.cacheControl, "private, max-age=60")] } "cache-control" == ["no-store"]
#guard acceptableCacheControl "no-cache, no-store"
#guard !acceptableCacheControl "must-revalidate"
#guard !acceptableCacheControl "no-cache, no-store, must-revalidate"
-- 拒否する指示が混ざっても、元の no-store を消して保存可能にしてはならない。
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "no-cache, no-store, must-revalidate")] }
  "cache-control" == ["no-store"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "must-revalidate, \r\nSet-Cookie: a=b")] }
  "cache-control" == []
#guard !acceptableCacheControl "public"
#guard !acceptableCacheControl "s-maxage=1"
#guard acceptable .etag "public"
#guard (lineOf { status := .ok, body := "" }).headers.toList.map (·.1.value) == ["content-type"]
-- 許す名前に Set-Cookie は無い。
#guard ResponseHeader.all.all (fun h => h.name != "set-cookie")
#guard ResponseHeader.all.map (·.name) == ["content-type", "cache-control", "etag", "location"]
#guard ResponseHeader.all.all (fun h => (headerName h).value == h.name)

end Test.Http
