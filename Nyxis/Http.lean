import Std.Http
import Nyxis.Runtime

/-!
# Nyxis.Http — HTTP サーバの共通部分

Lean 標準ライブラリの `Std.Http`(HTTP/1.1 サーバ)でランタイムを公開するための、接続層が共有する小さな部品:
リクエスト行からのパスと問い合わせ文字列の取り出し、要求ヘッダの選別、本文の上限、モデルのレスポンスの
HTTP レスポンスへの変換、サーバの起動。
ここは定理の外側にある接続コードで、当面は信頼する(`ASSUMPTIONS.md` A4 (b))。

リクエストを主体つきの `AuthenticatedRequest` に変えてモデルを駆動し、PostgreSQL の現在の行で認可する本体は
`Nyxis.Internal.PostgresHttp`(アプリケーションからは import できない。起動は `Nyxis.Internal.ApprovedServer`)。
`import Nyxis` で見えるのはこのモジュールの部品だけで、App を受け取る起動の口は `Nyxis.Internal.ApprovedServer.serve` のほかに無い。
-/

namespace Nyxis.Http

open Std.Async

/-- リクエスト行からパスを取り出す。問い合わせ文字列は含めず、パスの要素はパーセント符号化のまま
    (`/` を含む要素が復号で増えないように)。origin-form と absolute-form 以外は `*` や authority の文字列で、
    ルーティングには掛からない。 -/
def pathOf : Std.Http.RequestTarget → String
  | .originForm path _ => toString path
  | .absoluteForm uri => toString uri.path
  | other => toString other

/-- リクエスト行から生の問い合わせ文字列(`?` の後ろ。パーセント符号化のまま)を取り出す。無ければ空。 -/
def queryOf (target : Std.Http.RequestTarget) : String :=
  target.query.toRawString

/-- 要求ヘッダのうち `RequestHeader` に列挙した名前だけを、受け取った順に取り出す。名前は Std.Http が
    小文字に正規化している。Authorization・Cookie を含む他のヘッダはここで落ち、ハンドラには届かない。 -/
def selectHeaders (headers : Std.Http.Headers) : List (RequestHeader × String) :=
  headers.toList.filterMap fun (name, value) =>
    (RequestHeader.ofName? name.value).map fun header => (header, value.value)

/-- 読み取る本文の上限(バイト)。超えたリクエストは 400 で、ハンドラは呼ばれない。 -/
def maxBodyBytes : UInt64 := 1024 * 1024

/-- 応答の Content-Type。ハンドラが最初に設定した妥当な値、無ければ `text/plain; charset=utf-8`。 -/
def contentTypeOf (r : Response) : Std.Http.Header.Value :=
  ((r.headers.find? (·.1 == .contentType)).bind fun h => Std.Http.Header.Value.ofString? h.2).getD
    (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")

/-- 応答ヘッダの名前(HTTP の名前)。 -/
def headerName : ResponseHeader → Std.Http.Header.Name
  | .contentType => .contentType
  | .cacheControl => .mk "cache-control"
  | .etag => .mk "etag"
  | .location => .mk "location"

/-- Cache-Control の指示のうち、認証済みの主体に許可された応答を共有キャッシュが別の主体へ再送することを
    許す `public` と `s-maxage` は認めない(RFC 9111 §3.5: Authorization 付き要求の応答はこれらが無い限り
    共有キャッシュに保存されない)。指示はカンマ区切り、名前は大小を区別しない。 -/
def acceptableCacheControl (value : String) : Bool :=
  (value.splitOn ",").all fun directive =>
    let name := ((directive.splitOn "=").headD "").trimAscii.toString.toLower
    name != "public" && name != "s-maxage"

/-- ハンドラが設定した値を応答に載せてよいか。`Cache-Control` 以外は HTTP のヘッダ値としての妥当性だけ
    (`responseBuilder` が `Header.Value.ofString?` で確かめる)。 -/
def acceptable (name : ResponseHeader) (value : String) : Bool :=
  match name with
  | .cacheControl => acceptableCacheControl value
  | _ => true

/-- ハンドラが設定した `name` の値。最初のものを使い、`acceptable` で認められ HTTP のヘッダ値として妥当なときだけ。 -/
def headerValueOf (r : Response) (name : ResponseHeader) : Option Std.Http.Header.Value :=
  (r.headers.find? (·.1 == name)).bind fun h =>
    if acceptable name h.2 then Std.Http.Header.Value.ofString? h.2 else none

/-- ハンドラのレスポンスから HTTP レスポンスの行を組む。状態コードはハンドラが返したとおり。Content-Type は
    `contentTypeOf`、他の許可ヘッダは `ResponseHeader.all` の順に、各名前の最初の値が `headerValueOf` で認められた
    ときだけ 1 つ加える(妥当でない値・認めない指示は捨て、同じ名前の 2 つめ以降は使わない)。
    `ResponseHeader` に無い名前(Set-Cookie 等)は表せない。 -/
def responseBuilder (r : Response) : Std.Http.Response.Builder :=
  ResponseHeader.all.foldl (fun builder name =>
      if name == .contentType then builder
      else match headerValueOf r name with
        | some value => builder.header (headerName name) value
        | none => builder)
    ((Std.Http.Response.withStatus r.status).header Std.Http.Header.Name.contentType (contentTypeOf r))

/-- ハンドラのレスポンスを HTTP のレスポンスにする。状態コード・許可ヘッダ・本文はハンドラが返したとおり。 -/
def toHttpResponse (r : Response) : Async (Std.Http.Response Std.Http.Body.Full) := do
  let full ← Std.Http.Body.Full.ofByteArray r.body.toUTF8
  pure ((responseBuilder r).body full)

/-- すべてのインターフェースの `port` で HTTP サーバを起動し、停止まで待つ。 -/
def serve (port : UInt16) (handler : Std.Http.Server.StatelessHandler) : IO Unit := do
  let addr : Std.Net.SocketAddress := .v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, port⟩
  Async.block do
    let server ← Std.Http.Server.serve addr handler
    server.waitShutdown

end Nyxis.Http
