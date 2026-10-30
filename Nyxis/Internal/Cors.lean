import Nyxis.Http

/-! Core HTTP middleware (A4). The configuration comes from the deployment, never from the application's handlers. CORS
is a browser transport policy, not authorization. -/
namespace Nyxis.Internal.Cors
open Std.Async

structure Config where
  allowedOrigins : List String := []
  deriving Inhabited

/-- Accept only explicit HTTP(S) origins. Wildcards, opaque origins, paths and credentials are not accepted. Matching is
exact; there is no suffix matching and no normalization of request input. -/
def validOrigin (s : String) : Bool := Id.run do
  if !(s.startsWith "http://" || s.startsWith "https://") then return false
  let some uri := Std.Http.URI.parse? s | return false
  let some auth := uri.authority | return false
  return auth.userInfo.isNone && !(toString auth.host).isEmpty &&
    s == s!"{uri.scheme}://{auth}" &&
    s.toList.all (fun c => c.isAlphanum || ":/.-[]".contains c) &&
    !(s.endsWith ":")

/-- The comma-separated deployment setting. If it is absent or empty, CORS is disabled. -/
def parse (setting : String) : Except String Config := do
  if setting.isEmpty then return {}
  let origins := (setting.splitOn ",").map (fun s => s.trimAscii.toString)
  if !origins.all validOrigin then throw "NYXIS_CORS_ORIGINS is invalid"
  return { allowedOrigins := origins.eraseDups }

def allowed (config : Config) (headers : Std.Http.Headers) : Option Std.Http.Header.Value := do
  let values ← headers.getAll? .origin
  let [origin] := values.toList | none
  if validOrigin origin.value && config.allowedOrigins.contains origin.value then
    some origin
  else none

def decorate (config : Config) (headers : Std.Http.Headers) (preflight : Bool)
    (response : Std.Http.Response Std.Http.Body.Any) : Std.Http.Response Std.Http.Body.Any := Id.run do
  -- Add Vary even for rejected or missing origins, so that a shared cache cannot reuse an allowance.
  let mut result := { response with line.headers := response.line.headers.insert! "Vary" "Origin" }
  if let some origin := allowed config headers then
    result := { result with line.headers := result.line.headers.insert (Std.Http.Header.Name.ofString! "Access-Control-Allow-Origin") origin }
    if preflight then
      result := { result with line.headers := (result.line.headers
        |>.insert! "Access-Control-Allow-Methods" "GET, POST, PUT, PATCH, DELETE, OPTIONS"
        |>.insert! "Access-Control-Allow-Headers" "Authorization, Content-Type") }
  return result

/-- Every OPTIONS request finishes before body reading, authentication, routing and DB IO. Credentials and cookies are
not allowed. Browser clients use the Bearer header. -/
def wrap (config : Config)
    (next : Std.Http.Request Std.Http.Body.Stream →
      ContextAsync (Std.Http.Response Std.Http.Body.Any))
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  if req.line.method == .options then
    let response ← (Std.Http.Response.withStatus .noContent).text ""
    return decorate config req.line.headers true response
  return decorate config req.line.headers false (← next req)

/-- For OPTIONS, build a fixed 204 response that is independent of an arbitrary next step `next`. No handler,
authentication, authorization or DB processing is invoked. -/
theorem wrap_options (config : Config) (next)
    (req : Std.Http.Request Std.Http.Body.Stream) (h : req.line.method = .options) :
    wrap config next req = (do
      let response ← (Std.Http.Response.withStatus .noContent).text ""
      return decorate config req.line.headers true response) := by
  unfold wrap
  rw [h]
  rfl

end Nyxis.Internal.Cors
