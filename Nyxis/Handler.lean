import Std.Http
import Nyxis.Authz

/-!
# Nyxis.Handler — the handler type

The type of the code an application on nyxis writes for each HTTP endpoint.

A handler is represented not as `IO` but as a program whose only effects are action calls to the authorization layer (in
free-monad form). This type has no constructor representing access to IO, the DB layer or the outside world, so a
handler cannot reach the DB or the outside world without going through the authorization layer. It passes only which
action to call, on which row, with which values; it cannot pass the principal, resource or effect.

## HTTP summary

The request a handler can read is `Http.Request`: the method, path, raw query string (after `?`, still percent-encoded;
`Request.queryParams` decodes it into pairs), the headers selected by nyxis (`RequestHeader`: Accept, Accept-Language,
Content-Type, If-None-Match, If-Match. The names are enumerated by the type, and Authorization and Cookie have no
constructor, so they never reach the handler. The runtime reads the JWT and turns it into the principal), and the body.

The response a handler returns is `Http.Response`: the status code, the body, and the few response headers nyxis allows
(`ResponseHeader`: Content-Type, Cache-Control, ETag, Location. The names are enumerated by the type, and Set-Cookie has
no constructor). If Content-Type is not set, it is `text/plain; charset=utf-8`. Values that are not valid HTTP header
values (newlines, control characters, non-ASCII), and the Cache-Control directives `public` / `s-maxage`, which would
let a shared cache resend a response for an authenticated principal to another principal, are dropped by the connection
layer (`Nyxis.Http.responseBuilder`).
-/

namespace Nyxis

open Cedar.Spec

/-- A handler program. Either `pure`, or an action call `call` followed by waiting for the continuation. -/
inductive Handler (α : Type) : Type where
  /-- Finish by returning a value. -/
  | pure (a : α) : Handler α
  /-- Call the action `action` on the row with primary key `key` with the proposed values `values`, and continue with
      the result. For a list effect, `key` and `values` are unused and the query `query` (filter, sort, page) is used.
      -/
  | call (action : EntityUID) (key : Db.Key) (values : Db.Row) (query : Db.ListQuery) (k : Outcome → Handler α) :
      Handler α

namespace Handler

/-- Sequential composition. -/
protected def bind {α β : Type} : Handler α → (α → Handler β) → Handler β
  | .pure a, f => f a
  | .call action key values query k, f => .call action key values query (fun o => Handler.bind (k o) f)

instance : Monad Handler where
  pure := .pure
  bind := Handler.bind

/-- Call an action. The only effect a handler can have. -/
def callAction (action : EntityUID) (key : Db.Key) (values : Db.Row := Cedar.Data.Map.empty) :
    Handler Outcome :=
  .call action key values {} .pure

/-- Call a list action with a query for filtering, sorting and paging. The primary key and values are unused. The result
    is `Outcome.list rows total` (the rows returned, and the number of rows that match the filter and are permitted). -/
def callList (action : EntityUID) (query : Db.ListQuery := {}) : Handler Outcome :=
  .call action "" Cedar.Data.Map.empty query .pure

end Handler

namespace Http

/-- Names of the request headers passed to handlers. Only the few selected by nyxis; Authorization and Cookie are
    absent. -/
inductive RequestHeader where
  | accept
  | acceptLanguage
  | contentType
  | ifNoneMatch
  | ifMatch
  deriving DecidableEq, BEq, Repr, Inhabited

namespace RequestHeader

/-- The name on the wire (lowercase). -/
def name : RequestHeader → String
  | .accept => "accept"
  | .acceptLanguage => "accept-language"
  | .contentType => "content-type"
  | .ifNoneMatch => "if-none-match"
  | .ifMatch => "if-match"

/-- All selected names. -/
def all : List RequestHeader := [.accept, .acceptLanguage, .contentType, .ifNoneMatch, .ifMatch]

/-- From a lowercase HTTP name. Names outside the selection (including Authorization and Cookie) give `none`. -/
def ofName? (name : String) : Option RequestHeader :=
  all.find? (·.name == name)

end RequestHeader

/-- Names of the response headers a handler can set. Only the few nyxis allows; Set-Cookie is absent. -/
inductive ResponseHeader where
  | contentType
  | cacheControl
  | etag
  | location
  deriving DecidableEq, BEq, Repr, Inhabited

namespace ResponseHeader

/-- The name on the wire (lowercase). -/
def name : ResponseHeader → String
  | .contentType => "content-type"
  | .cacheControl => "cache-control"
  | .etag => "etag"
  | .location => "location"

/-- All allowed names. -/
def all : List ResponseHeader := [.contentType, .cacheControl, .etag, .location]

end ResponseHeader

/-- The summary of an HTTP request passed to a handler. The runtime reads the JWT and turns it into the principal; it is
    not passed to the handler. `query` is the raw query string (after `?`; empty if absent), and `headers` are the
    request headers selected by nyxis (if the same name appears more than once, all of them in the order received). -/
structure Request where
  method : Std.Http.Method
  path : String
  body : String
  query : String := ""
  headers : List (RequestHeader × String) := []

/-- The HTTP response a handler returns. `headers` are the response headers nyxis allows (only the first of the same
    name is used, and values that are not valid HTTP header values (newlines, control characters, non-ASCII) and the
    Cache-Control directives `public` / `s-maxage`, which allow storing in a shared cache, are dropped). If Content-Type
    is not set, it is `text/plain; charset=utf-8`. -/
structure Response where
  status : Std.Http.Status
  body : String
  headers : List (ResponseHeader × String) := []

/-- Routing. From the method and path, select a handler that receives the principal, the server-generated values (the
    current time and a fresh unique ID that nyxis determines per request, used for proposing values) and the request.
    `none` means 404. -/
abbrev Router :=
  Std.Http.Method → String → Option (Authz.Principal → Authz.Generated → Request → Handler Response)

/-! ## Decoding the query string -/

/-- A single hexadecimal digit. -/
private def hexValue? (c : UInt8) : Option UInt8 :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else none

/-- Decode a component of the query string: `%XX` is that byte and `+` is a space. Returns `none` if `%` is not followed
    by two hexadecimal digits, or if the result is not UTF-8. -/
def decodeComponent (s : String) : Option String := Id.run do
  let bytes := s.toUTF8
  let mut out := ByteArray.empty
  let mut i := 0
  while i < bytes.size do
    let c := bytes[i]!
    if c == 43 then
      out := out.push 32
      i := i + 1
    else if c == 37 then
      match hexValue? (bytes[i + 1]?.getD 0), hexValue? (bytes[i + 2]?.getD 0) with
      | some hi, some lo =>
        if i + 2 < bytes.size then
          out := out.push (hi * 16 + lo)
          i := i + 3
        else return none
      | _, _ => return none
    else
      out := out.push c
      i := i + 1
  return String.fromUTF8? out

/-- Split the query string into (name, value) pairs. Split on `&`, split each piece into name and value at the first `=`
    (if there is no `=`, the value is empty), and decode each with `decodeComponent`. Pairs that cannot be decoded and
    empty pieces are dropped. -/
def parseQuery (query : String) : List (String × String) :=
  (query.splitOn "&").filterMap fun piece =>
    if piece.isEmpty then none
    else
      let (name, value) := match piece.splitOn "=" with
        | [] => (piece, "")
        | name :: rest => (name, "=".intercalate rest)
      match decodeComponent name, decodeComponent value with
      | some n, some v => some (n, v)
      | _, _ => none

/-- The decoded query pairs. -/
def Request.queryParams (r : Request) : List (String × String) := parseQuery r.query

/-- The first value of a query parameter. -/
def Request.queryParam? (r : Request) (name : String) : Option String :=
  (r.queryParams.find? (·.1 == name)).map (·.2)

/-- The first value of a selected request header. -/
def Request.header? (r : Request) (name : RequestHeader) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

end Http

end Nyxis
