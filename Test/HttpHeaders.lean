import Nyxis.Internal.PostgresHttp
import Test.Fixture

/-!
# Test.HttpHeaders — executable for the HTTP integration check of query strings and selected headers

A test server that mounts, on the same HTTP entry point as the main one (`PostgresHttp.handleAuthenticatedWith`), a
handler that writes out the request summary as-is and a handler that tries to insert disallowed response headers.
`scripts/check-http-headers.py` starts it and confirms over real HTTP that: the query string and the selected request
headers (Accept, Content-Type, If-None-Match, etc.) reach the handler; Authorization and Cookie do not (Authorization is
used only for authentication and becomes the principal); and the response carries only Content-Type and the few allowed
headers, with neither invalid values nor Set-Cookie. The principal is determined from an opaque test-only credential
(neither a JWT nor the deployed verifier). No DB is used.
-/

open Nyxis Nyxis.Http Nyxis.Runtime Nyxis.Internal Test.Fixture

private def principalText : Authz.Principal → String
  | .anonymous => "anonymous"
  | .user uid => uid.ty.id ++ "::" ++ uid.eid

private def showHeaders (hs : List (RequestHeader × String)) : String :=
  ";".intercalate (hs.map fun h => h.1.name ++ "=" ++ h.2)

private def showParams (ps : List (String × String)) : String :=
  ";".intercalate (ps.map fun p => p.1 ++ "=" ++ p.2)

/-- Write out the request summary (principal, raw query, decoded pairs, selected headers, body) and set the allowed
    response headers. -/
private def echo : Authz.Principal → Authz.Generated → Request → Handler Response := fun principal _ req =>
  pure { status := .ok
         body := "principal=" ++ principalText principal ++ "\nquery=" ++ req.query ++
           "\nparams=" ++ showParams req.queryParams ++ "\nheaders=" ++ showHeaders req.headers ++
           "\nbody=" ++ req.body
         headers := [(.contentType, "application/json"), (.etag, "\"v1\""), (.cacheControl, "no-store")] }

/-- Try disallowed insertions: a Content-Type containing a newline (Set-Cookie injection), an ETag containing a newline
    and a second one, a Cache-Control that allows storing in a shared cache, and a second Content-Type. Only the valid
    Location remains, and Content-Type falls back to the default. -/
private def inject : Authz.Principal → Authz.Generated → Request → Handler Response := fun _ _ _ =>
  pure { status := .created, body := "injected?"
         headers := [(.contentType, "text/html\r\nSet-Cookie: a=b"), (.etag, "bad\nvalue"), (.etag, "\"second\""),
           (.cacheControl, "public, max-age=60"), (.location, "/echo"), (.contentType, "application/json")] }

private def plain : Authz.Principal → Authz.Generated → Request → Handler Response := fun _ _ _ =>
  pure { status := .ok, body := "plain" }

/-- A read through the authorization layer (the fixture's draft). The control showing that the principal is determined
    from Authorization. -/
private def readDraft : Authz.Principal → Authz.Generated → Request → Handler Response := fun _ _ _ => do
  match ← Handler.callAction (act "readPost") "draft1" with
  | .ok (some _) => pure { status := .ok, body := "draft" }
  | .denied => pure { status := .forbidden, body := "forbidden" }
  | _ => pure { status := .notFound, body := "not found" }

private def router : Router := fun method path =>
  match method, path with
  | .get, "/echo" => some echo
  | .post, "/echo" => some echo
  | .get, "/inject" => some inject
  | .get, "/plain" => some plain
  | .get, "/posts/draft1" => some readDraft
  | _, _ => none

private def app : App := { schema := schema, policies := policies, router := router }

def main (args : List String) : IO Unit := do
  let some port := (args.head?.getD "18114").toNat?.filter (fun n => 0 < n && n ≤ 65535) |>.map Nat.toUInt16
    | throw (IO.userError "port out of range")
  -- An opaque test-only credential. Neither a JWT nor the deployed verifier.
  let verify : String → IO (Option String) := fun token =>
    match token with
    | "test-alice" => pure (some "alice")
    | "test-root" => pure (some "root")
    | _ => pure none
  let backend : AuthenticatedRequest → IO Response := fun r =>
    pure (handleRequest app store r).result
  IO.println s!"nyxis http headers check: listening on port {port}"
  Nyxis.Http.serve port (Std.Http.Server.Handler.ofFn
    (PostgresHttp.handleAuthenticatedWith (HttpAuth.principalOf userT verify) Generated.fresh backend))
