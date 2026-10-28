import Nyxis.Http

/-! コアの HTTP ミドルウェア(Assumption 1)。設定は配置から来るもので、アプリケーションのハンドラからは来ない。
CORS はブラウザの輸送の方針であり、認可ではない。 -/
namespace Nyxis.Internal.Cors
open Std.Async

structure Config where
  allowedOrigins : List String := []
  deriving Inhabited

/-- 明示的な HTTP(S) のオリジンだけを認める。ワイルドカード・不透明なオリジン・パス・資格情報は認めない。
照合は完全一致で、接尾辞の照合やリクエスト入力の正規化は行わない。 -/
def validOrigin (s : String) : Bool := Id.run do
  if !(s.startsWith "http://" || s.startsWith "https://") then return false
  let some uri := Std.Http.URI.parse? s | return false
  let some auth := uri.authority | return false
  return auth.userInfo.isNone && !(toString auth.host).isEmpty &&
    s == s!"{uri.scheme}://{auth}" &&
    s.toList.all (fun c => c.isAlphanum || ":/.-[]".contains c) &&
    !(s.endsWith ":")

/-- カンマ区切りの配置の設定。無い・空なら CORS を無効にする。 -/
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
  -- 拒否したオリジンや無いオリジンでも Vary を付け、共有キャッシュが許可を再利用できないようにする。
  let mut result := { response with line.headers := response.line.headers.insert! "Vary" "Origin" }
  if let some origin := allowed config headers then
    result := { result with line.headers := result.line.headers.insert (Std.Http.Header.Name.ofString! "Access-Control-Allow-Origin") origin }
    if preflight then
      result := { result with line.headers := (result.line.headers
        |>.insert! "Access-Control-Allow-Methods" "GET, POST, PUT, PATCH, DELETE, OPTIONS"
        |>.insert! "Access-Control-Allow-Headers" "Authorization, Content-Type") }
  return result

/-- すべての OPTIONS は、本文の読み取り・認証・ルーティング・DB の IO の前で終わる。
資格情報や cookie は許可しない。ブラウザのクライアントは Bearer ヘッダを使う。 -/
def wrap (config : Config)
    (next : Std.Http.Request Std.Http.Body.Stream →
      ContextAsync (Std.Http.Response Std.Http.Body.Any))
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  if req.line.method == .options then
    let response ← (Std.Http.Response.withStatus .noContent).text ""
    return decorate config req.line.headers true response
  return decorate config req.line.headers false (← next req)

/-- 日本語: OPTIONSでは任意の次処理nextと無関係な固定204応答を構築する。
ハンドラ・認証・認可・DBの処理を呼ばない。 -/
theorem wrap_options (config : Config) (next)
    (req : Std.Http.Request Std.Http.Body.Stream) (h : req.line.method = .options) :
    wrap config next req = (do
      let response ← (Std.Http.Response.withStatus .noContent).text ""
      return decorate config req.line.headers true response) := by
  unfold wrap
  rw [h]
  rfl

end Nyxis.Internal.Cors
