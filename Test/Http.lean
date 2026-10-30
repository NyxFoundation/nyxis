import Nyxis.Http

/-!
# Test.Http — pure checks of the HTTP summary and the response line

Checks the pure functions of `Nyxis.Http` with `#guard`: selecting request headers (`selectHeaders`; names outside the
enumeration, including Authorization and Cookie, are dropped), decoding the query string (`decodeComponent` /
`parseQuery`), and building the response line (`responseBuilder`; the default Content-Type and dropping invalid values;
names not in `ResponseHeader` cannot be represented). The integration check over real HTTP is
`scripts/check-http-headers.py` (executable `serveHttpHeaders`).
-/

namespace Test.Http

open Nyxis Nyxis.Http

private def hdrs (pairs : List (String × String)) : Std.Http.Headers :=
  Std.Http.Headers.ofList (pairs.map fun p =>
    (Std.Http.Header.Name.ofString! p.1, Std.Http.Header.Value.ofString! p.2))

/-! ## Selecting request headers -/

-- Only the enumerated names remain, in the order received; Authorization, Cookie and others are dropped. Names are
-- case-insensitive.
#guard selectHeaders (hdrs [("Authorization", "Bearer secret"), ("Cookie", "s=1"), ("Accept", "application/json"),
    ("X-Principal", "root"), ("CONTENT-TYPE", "text/plain"), ("If-None-Match", "\"v1\""), ("Accept", "text/html"),
    ("Accept-Language", "ja"), ("If-Match", "\"v2\""), ("Set-Cookie", "a=b"), ("Proxy-Authorization", "Basic x"),
    ("Host", "example.test")]) ==
  [(.accept, "application/json"), (.contentType, "text/plain"), (.ifNoneMatch, "\"v1\""), (.accept, "text/html"),
   (.acceptLanguage, "ja"), (.ifMatch, "\"v2\"")]
#guard selectHeaders (hdrs []) == []
#guard selectHeaders (hdrs [("Authorization", "Bearer secret"), ("Cookie", "s=1")]) == []
-- Authorization and Cookie are not among the selected names, and conversion from a name gives `none` for them.
#guard RequestHeader.all.all (fun h => h.name != "authorization" && h.name != "cookie")
#guard RequestHeader.ofName? "authorization" == none
#guard RequestHeader.ofName? "cookie" == none
#guard RequestHeader.ofName? "accept" == some .accept
#guard RequestHeader.ofName? "if-none-match" == some .ifNoneMatch
#guard RequestHeader.all.map (·.name) == ["accept", "accept-language", "content-type", "if-none-match", "if-match"]

/-! ## Query string -/

#guard decodeComponent "a%20b+c" == some "a b c"
#guard decodeComponent "%E3%81%82" == some "\u3042"
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

-- Extraction from the request line: the path does not include the query, and the query stays encoded.
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

/-! ## Response line -/

private def lineOf (r : Response) := (responseBuilder r).line

/-- The values of `name` in the response line (in the order received). -/
private def valuesOf (r : Response) (name : String) : List String :=
  (((lineOf r).headers.getAll? (Std.Http.Header.Name.ofString! name)).map (·.toList.map (·.value))).getD []

private def allowed : Response :=
  { status := .created, body := "", headers := [(.etag, "\"v1\""), (.cacheControl, "no-store"), (.location, "/docs/1")] }

-- The default Content-Type and setting it. For the same name, the first one is used.
#guard valuesOf { status := .ok, body := "" } "content-type" == ["text/plain; charset=utf-8"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "application/json")] } "content-type"
  == ["application/json"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "application/json"), (.contentType, "text/html")] }
  "content-type" == ["application/json"]
-- Invalid values (containing a newline) are dropped. Content-Type falls back to the default, and the name whose
-- insertion was attempted does not appear.
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "text/html\r\nSet-Cookie: a=b")] }
  "content-type" == ["text/plain; charset=utf-8"]
#guard valuesOf { status := .ok, body := "", headers := [(.contentType, "text/html\r\nSet-Cookie: a=b")] }
  "set-cookie" == []
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "bad\nvalue")] } "etag" == []
-- Other allowed headers.
#guard valuesOf allowed "etag" == ["\"v1\""]
#guard valuesOf allowed "cache-control" == ["no-store"]
#guard valuesOf allowed "location" == ["/docs/1"]
#guard (lineOf allowed).status == .created
#guard (lineOf allowed).headers.toList.map (·.1.value) == ["content-type", "cache-control", "etag", "location"]
-- For the same name, only the first one is used (the second and later are not used even if valid).
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "\"a\""), (.etag, "\"b\"")] } "etag" == ["\"a\""]
#guard valuesOf { status := .ok, body := "", headers := [(.etag, "bad\nvalue"), (.etag, "\"b\"")] } "etag" == []
-- Cache-Control: public / s-maxage, which allow storing in a shared cache, are dropped (regardless of case or
-- whitespace).
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "private, max-age=0")] } "cache-control"
  == ["private, max-age=0"]
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "public, max-age=60")] } "cache-control" == []
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, "max-age=60, S-MaxAge = 10")] } "cache-control" == []
#guard valuesOf { status := .ok, body := "", headers := [(.cacheControl, " Public ")] } "cache-control" == []
#guard acceptableCacheControl "no-cache, no-store, must-revalidate"
#guard !acceptableCacheControl "public"
#guard !acceptableCacheControl "s-maxage=1"
#guard acceptable .etag "public"
#guard (lineOf { status := .ok, body := "" }).headers.toList.map (·.1.value) == ["content-type"]
-- Set-Cookie is not among the allowed names.
#guard ResponseHeader.all.all (fun h => h.name != "set-cookie")
#guard ResponseHeader.all.map (·.name) == ["content-type", "cache-control", "etag", "location"]
#guard ResponseHeader.all.all (fun h => (headerName h).value == h.name)

end Test.Http
