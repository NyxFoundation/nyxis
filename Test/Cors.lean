import Nyxis.Internal.Cors

/-!
# Test.Cors — unit checks for the CORS configuration

Checks the pure functions of `Nyxis.Internal.Cors` (origin validity, parsing the setting, matching the request's Origin)
with `#guard`. The integration check against a real application is `scripts/check-cors.py`.
-/

namespace Test.Cors

open Nyxis.Internal.Cors

-- Only explicit HTTP(S) origins are accepted.
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
#guard !validOrigin "https://\u4f8b.test"

-- The setting is `,`-separated. Empty means CORS is disabled. Whitespace is trimmed and duplicates collapse to one. A
-- single invalid element rejects the whole setting.
#guard (parse "").toOption.map (·.allowedOrigins) == some []
#guard (parse "http://127.0.0.1:3000, http://localhost:3000").toOption.map (·.allowedOrigins) ==
  some ["http://127.0.0.1:3000", "http://localhost:3000"]
#guard (parse "https://a.test,https://a.test").toOption.map (·.allowedOrigins) == some ["https://a.test"]
#guard !(parse "https://a.test,").isOk
#guard !(parse ",https://a.test").isOk
#guard !(parse "https://a.test, *").isOk
#guard !(parse "https://a.test/").isOk

/-- Request headers carrying `Origin` headers in the order of `values`. -/
private def origins (values : List String) : Std.Http.Headers :=
  Std.Http.Headers.ofList (values.map fun value => (.origin, Std.Http.Header.Value.ofString! value))

private def config : Config := { allowedOrigins := ["http://127.0.0.1:3000", "https://example.test"] }

/-- Whether the request is allowed, with its Origin returned as-is. -/
private def granted (values : List String) : Option String :=
  (allowed config (origins values)).map (·.value)

-- An allowed origin is returned, as the exact same string, only when it matches.
#guard granted ["http://127.0.0.1:3000"] == some "http://127.0.0.1:3000"
#guard granted ["https://example.test"] == some "https://example.test"
-- Nothing is returned for a disallowed, invalid, missing or duplicated Origin (no normalization or suffix matching).
#guard granted ["http://127.0.0.1:3001"] == none
#guard granted ["http://localhost:3000"] == none
#guard granted ["https://example.test/"] == none
#guard granted ["HTTPS://example.test"] == none
#guard granted ["https://evil.example.test"] == none
#guard granted ["null"] == none
#guard granted [] == none
#guard granted ["https://example.test", "https://example.test"] == none
#guard granted ["https://example.test", "http://127.0.0.1:3000"] == none
-- If the allow list is empty, nothing is returned for any Origin.
#guard (allowed {} (origins ["https://example.test"])).isNone

end Test.Cors
