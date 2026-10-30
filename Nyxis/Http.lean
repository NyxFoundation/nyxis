import Std.Http
import Nyxis.Runtime

/-!
# Nyxis.Http — shared parts of the HTTP server

Small pieces shared by the connection layer for exposing the runtime over the Lean standard library's `Std.Http` (an
HTTP/1.1 server): extracting the path and query string from the request line, selecting request headers, the body limit,
converting the model's response into an HTTP response, and starting the server. This is connection code outside the
theorem and is trusted for now (`ASSUMPTIONS.md` A4 (b)).

The main part, which turns a request into an `AuthenticatedRequest` with its principal, drives the model and authorizes
against the current PostgreSQL rows, is `Nyxis.Internal.PostgresHttp` (applications cannot import it; startup is
`Nyxis.Internal.ApprovedServer`). `import Nyxis` exposes only the pieces in this module, and there is no startup entry
point that accepts an App other than `Nyxis.Internal.ApprovedServer.serve`.
-/

namespace Nyxis.Http

open Std.Async

/-- Extract the path from the request line. The query string is not included, and path segments stay percent-encoded (so
    that decoding does not create extra segments from a `/`). Anything other than origin-form and absolute-form is a `*`
    or authority string and does not match any route. -/
def pathOf : Std.Http.RequestTarget → String
  | .originForm path _ => toString path
  | .absoluteForm uri => toString uri.path
  | other => toString other

/-- Extract the raw query string (after `?`, still percent-encoded) from the request line. Empty if absent. -/
def queryOf (target : Std.Http.RequestTarget) : String :=
  target.query.toRawString

/-- Extract, in the order received, only the request headers whose names are listed in `RequestHeader`. Std.Http has
    already normalized the names to lowercase. Other headers, including Authorization and Cookie, are dropped here and
    never reach the handler. -/
def selectHeaders (headers : Std.Http.Headers) : List (RequestHeader × String) :=
  headers.toList.filterMap fun (name, value) =>
    (RequestHeader.ofName? name.value).map fun header => (header, value.value)

/-- The limit on the body that is read (bytes). A request exceeding it gets 400, and the handler is not called. -/
def maxBodyBytes : UInt64 := 1024 * 1024

/-- The response's Content-Type. The first valid value the handler set, or `text/plain; charset=utf-8` if none. -/
def contentTypeOf (r : Response) : Std.Http.Header.Value :=
  ((r.headers.find? (·.1 == .contentType)).bind fun h => Std.Http.Header.Value.ofString? h.2).getD
    (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")

/-- The name of a response header (its HTTP name). -/
def headerName : ResponseHeader → Std.Http.Header.Name
  | .contentType => .contentType
  | .cacheControl => .mk "cache-control"
  | .etag => .mk "etag"
  | .location => .mk "location"

/-- Of the Cache-Control directives, `public` and `s-maxage`, which let a shared cache resend a response permitted for
    an authenticated principal to another principal, are not accepted (RFC 9111 §3.5: a response to a request with
    Authorization is not stored in a shared cache unless one of these is present). Directives are comma-separated, and
    names are case-insensitive. -/
def acceptableCacheControl (value : String) : Bool :=
  (value.splitOn ",").all fun directive =>
    let name := ((directive.splitOn "=").headD "").trimAscii.toString.toLower
    name != "public" && name != "s-maxage"

/-- Whether a value set by the handler may be put on the response. For anything other than `Cache-Control`, only
    validity as an HTTP header value is required (checked by `responseBuilder` with `Header.Value.ofString?`). -/
def acceptable (name : ResponseHeader) (value : String) : Bool :=
  match name with
  | .cacheControl => acceptableCacheControl value
  | _ => true

/-- The value of `name` set by the handler. The first one is used, and only when it is accepted by `acceptable` and
    valid as an HTTP header value. -/
def headerValueOf (r : Response) (name : ResponseHeader) : Option Std.Http.Header.Value :=
  (r.headers.find? (·.1 == name)).bind fun h =>
    if acceptable name h.2 then Std.Http.Header.Value.ofString? h.2 else none

/-- Build the HTTP response line from the handler's response. The status code is exactly what the handler returned.
    Content-Type comes from `contentTypeOf`; each other allowed header is added once, in the order of
    `ResponseHeader.all`, only when the first value for that name is accepted by `headerValueOf` (invalid values and
    disallowed directives are dropped, and second and later values of the same name are not used). Names not in
    `ResponseHeader` (Set-Cookie etc.) cannot be represented. -/
def responseBuilder (r : Response) : Std.Http.Response.Builder :=
  ResponseHeader.all.foldl (fun builder name =>
      if name == .contentType then builder
      else match headerValueOf r name with
        | some value => builder.header (headerName name) value
        | none => builder)
    ((Std.Http.Response.withStatus r.status).header Std.Http.Header.Name.contentType (contentTypeOf r))

/-- Turn the handler's response into an HTTP response. The status code, allowed headers and body are exactly what the
    handler returned. -/
def toHttpResponse (r : Response) : Async (Std.Http.Response Std.Http.Body.Full) := do
  let full ← Std.Http.Body.Full.ofByteArray r.body.toUTF8
  pure ((responseBuilder r).body full)

/-- Start the HTTP server on `port` on all interfaces and wait until it stops. -/
def serve (port : UInt16) (handler : Std.Http.Server.StatelessHandler) : IO Unit := do
  let addr : Std.Net.SocketAddress := .v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, port⟩
  Async.block do
    let server ← Std.Http.Server.serve addr handler
    server.waitShutdown

end Nyxis.Http
