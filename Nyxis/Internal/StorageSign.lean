import Lean.Data.Json
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.CurlStdin

/-! Issuing Supabase Storage signed URLs through the approved curl (A8; core only, unproven).

The connection layer (`PostgresRun.runStaged`) calls this only for external-effect records that the authorization layer
(`Nyxis.Authz.signStep`) permitted (`Nyxis.Authz.External`: the kind and the object path). The URL reached is derived in
a fixed form from the core configuration `Config.url` (the Supabase project's HTTPS URL), the fixed bucket, and the path
nyxis determined; the request's URL, headers, and body are not used. The credential (the service_role key) is passed in
a curl configuration on standard input, not as an argument, and does not appear in the process arguments.

- Upload: `POST {url}/storage/v1/object/upload/sign/{bucket}/{object}` → `{"url": "/object/upload/sign/…?token=…"}`.
- Download: `POST {url}/storage/v1/object/sign/{bucket}/{object}` (body `{"expiresIn": 600}`) → `{"signedURL": "…"}`.

The returned URL is relative, following `{url}/storage/v1`, so it is made absolute and returned as `some`. If Storage
reports "object not found" (HTTP 404, or HTTP 400 with `error` equal to `not_found`; `isNotFound`), `none`. Any other
failure (connection, TLS, 5xx, malformed response, body over 64KiB) is an exception: the whole request becomes 503 and
the transaction is rolled back (unlike `JwksFetch`, it is never silently treated as success). The download URL's expiry
is fixed by the core configuration (`expiresIn`, 10 minutes). The upload URL's expiry is determined by Supabase Storage
(the API has no parameter for it, and Supabase fixes it at 2 hours). `sign` repeats the same checks as `Config.parse`
before using the configuration (it does not issue with a `Config` built from values that do not pass the checks). Same
transport policy as the JWKS fetch: HTTPS only, no redirect following, 3 seconds to connect and 5 seconds for the whole
transfer, 64KiB body, `--disable` first.
-/
namespace Nyxis.Internal.StorageSign

/-- Storage configuration. The URL is `https://host[:port]` (no path, query, or credentials), the bucket is a string
    usable as a Storage bucket name, and the service_role key is printable ASCII (containing no whitespace, quotes, or
    backslashes). `parse` checks them. -/
structure Config where
  url : String
  bucket : String
  serviceKey : String

/-- The expiry of signed URLs (seconds). Fixed by the core configuration. -/
def expiresIn : Nat := 600

/-- Whether the URL is just an HTTPS DNS host (with an optional numeric port) (same rule as `JwksFetch.urlOfIssuer`). -/
def validUrl (url : String) : Bool :=
  (JwksFetch.urlOfIssuer (url ++ "/auth/v1")).isSome && !url.endsWith "/"

/-- A bucket name: alphanumerics, `-`, `_`, `.` (1 to 100 characters). -/
def validBucket (bucket : String) : Bool :=
  bucket.length > 0 && bucket.length ≤ 100 &&
    bucket.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.')

/-- A service_role key: printable ASCII containing no whitespace, `"`, or `\` (so it can be placed as is as a value in
    the curl configuration). -/
def validKey (key : String) : Bool :=
  key.length > 0 && key.length ≤ 4096 &&
    key.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- Check the three settings and assemble them. `none` if any is invalid. -/
def Config.parse (url bucket key : String) : Option Config :=
  if validUrl url && validBucket bucket && validKey key then some ⟨url, bucket, key⟩ else none

/-- The API path to issue against (relative to `/storage/v1`; `upload` issues an upload, otherwise a download). The
    object path is `table/<primary key>/<name>` as determined by `Nyxis.Db.objectPath` (only alphanumerics, `-`, `_`,
    and `/`), so it can be placed as is. -/
def endpoint (upload : Bool) (bucket object : String) : String :=
  if upload then "/object/upload/sign/" ++ bucket ++ "/" ++ object
  else "/object/sign/" ++ bucket ++ "/" ++ object

/-- The configuration passed to curl on standard input (`--config -`). The credential and the request values do not
    appear in the arguments. -/
def configText (config : Config) (upload : Bool) (object : String) : String :=
  let lines := [
    "url = \"" ++ config.url ++ "/storage/v1" ++ endpoint upload config.bucket object ++ "\"",
    "request = \"POST\"",
    "header = \"Authorization: Bearer " ++ config.serviceKey ++ "\"",
    "header = \"Content-Type: application/json\""] ++
    (if upload then ["data = \"{}\""]
      else ["data = \"{\\\"expiresIn\\\":" ++ toString expiresIn ++ "}\""])
  String.intercalate "\n" lines ++ "\n"

/-- The fixed transport policy (same as `JwksFetch.arguments`). `--fail` is not given; the status code is read at the
    end of the body. -/
def arguments : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", "3", "--max-time", "5", "--max-filesize", "65536",
  "--write-out", "\n%{http_code}", "--config", "-"]

/-- Read the signed URL (relative) from the response body: `url` for uploads, `signedURL` for downloads. -/
def relativeUrlOf (upload : Bool) (body : String) : Option String := do
  let json ← (Lean.Json.parse body).toOption
  let field := if upload then "url" else "signedURL"
  let value ← (json.getObjVal? field).toOption
  let s ← value.getStr?.toOption
  if s.startsWith "/" && !s.contains '\x00' && s.length ≤ 4096 then some s else none

/-- Split curl's output (body + newline + status code) into the status code and the body. -/
def splitOutput (output : String) : Option (Nat × String) :=
  match (output.splitOn "\n").reverse with
  | code :: rest => (code.toNat?).map fun n => (n, "\n".intercalate rest.reverse)
  | [] => none

/-- Whether it is Storage's "object not found" response: HTTP 404, or HTTP 400 with the body's `error` equal to
    `not_found` (Supabase Storage returns `{"statusCode":"404","error":"not_found",…}` with HTTP 400 when the object
    does not exist on a download issue). -/
def isNotFound (status : Nat) (body : String) : Bool :=
  status == 404 || (status == 400 &&
    (match (Lean.Json.parse body).toOption >>= fun j => (j.getObjVal? "error").toOption >>= fun v => v.getStr?.toOption with
      | some "not_found" => true
      | _ => false))

/-- Issue a signed URL. `some url` is an absolute URL, `none` means the object does not exist (`isNotFound`). Other
    failures are exceptions. -/
def sign (config : Config) (upload : Bool) (object : String) : IO (Option String) := do
  -- Re-check the configuration and the target (do not issue with values that bypassed the check via the constructor, or
  -- with a target that is not a path element).
  unless validUrl config.url && validBucket config.bucket && validKey config.serviceKey do
    throw (IO.userError "storage configuration invalid")
  unless object.length > 0 && object.length ≤ 512 &&
      object.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '/')) do
    throw (IO.userError "storage object path invalid")
  let (code, output) ← CurlStdin.run arguments (configText config upload object)
  unless code == 0 do throw (IO.userError "storage request failed")
  unless output.utf8ByteSize ≤ 65536 do throw (IO.userError "storage response too large")
  let some (status, body) := splitOutput output | throw (IO.userError "storage response unreadable")
  if isNotFound status body then return none
  unless status == 200 do throw (IO.userError "storage request rejected")
  let some relative := relativeUrlOf upload body | throw (IO.userError "storage response unreadable")
  return some (config.url ++ "/storage/v1" ++ relative)

end Nyxis.Internal.StorageSign
