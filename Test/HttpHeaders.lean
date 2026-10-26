import Nyxis.Internal.PostgresHttp
import Test.Fixture

/-!
# Test.HttpHeaders — 問い合わせ文字列と選別したヘッダの HTTP 統合検査用の実行ファイル

本体と同じ HTTP 入口(`PostgresHttp.handleAuthenticatedWith`)に、要求の要約をそのまま書き出すハンドラと、
許可外の応答ヘッダの挿入を試みるハンドラを載せた検査用のサーバ。`scripts/check-http-headers.py` がこれを起動し、
実 HTTP で次を確かめる: 問い合わせ文字列と選別した要求ヘッダ(Accept・Content-Type・If-None-Match 等)が
ハンドラに届くこと、Authorization と Cookie は届かないこと(Authorization は認証にだけ使われ主体になる)、
応答に Content-Type と許可された少数のヘッダだけが付き、妥当でない値と Set-Cookie は付かないこと。
主体は検査専用の不透明な資格情報から決める(JWT でも配置する検証器でもない)。DB は使わない。
-/

open Nyxis Nyxis.Http Nyxis.Runtime Nyxis.Internal Test.Fixture

private def principalText : Authz.Principal → String
  | .anonymous => "anonymous"
  | .user uid => uid.ty.id ++ "::" ++ uid.eid

private def showHeaders (hs : List (RequestHeader × String)) : String :=
  ";".intercalate (hs.map fun h => h.1.name ++ "=" ++ h.2)

private def showParams (ps : List (String × String)) : String :=
  ";".intercalate (ps.map fun p => p.1 ++ "=" ++ p.2)

/-- 要求の要約(主体・生の問い合わせ・復号した組・選別したヘッダ・本文)を書き出し、許可された応答ヘッダを設定する。 -/
private def echo : Authz.Principal → Authz.Generated → Request → Handler Response := fun principal _ req =>
  pure { status := .ok
         body := "principal=" ++ principalText principal ++ "\nquery=" ++ req.query ++
           "\nparams=" ++ showParams req.queryParams ++ "\nheaders=" ++ showHeaders req.headers ++
           "\nbody=" ++ req.body
         headers := [(.contentType, "application/json"), (.etag, "\"v1\""), (.cacheControl, "no-store")] }

/-- 許可外の挿入を試みる: 改行を含む Content-Type(Set-Cookie の注入)、改行を含む ETag とその 2 つめ、
    共有キャッシュへの保存を許す Cache-Control、2 つめの Content-Type。妥当な Location だけが残り、
    Content-Type は既定に戻る。 -/
private def inject : Authz.Principal → Authz.Generated → Request → Handler Response := fun _ _ _ =>
  pure { status := .created, body := "injected?"
         headers := [(.contentType, "text/html\r\nSet-Cookie: a=b"), (.etag, "bad\nvalue"), (.etag, "\"second\""),
           (.cacheControl, "public, max-age=60"), (.location, "/echo"), (.contentType, "application/json")] }

private def plain : Authz.Principal → Authz.Generated → Request → Handler Response := fun _ _ _ =>
  pure { status := .ok, body := "plain" }

/-- 認可層を通る読み取り(fixture の下書き)。主体が Authorization から決まることの対照。 -/
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
  -- 検査専用の不透明な資格情報。JWT でも配置する検証器でもない。
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
