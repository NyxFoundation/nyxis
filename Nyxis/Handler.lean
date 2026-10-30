import Std.Http
import Nyxis.Authz

/-!
# Nyxis.Handler — ハンドラの型

nyxis 上のアプリケーションが HTTP の各エンドポイントに対して書く処理の型。

ハンドラは `IO` ではなく、認可層へのアクション呼び出しだけを効果として持つプログラム
(自由モナドの形)として表す。この型には IO・DB 層・外界への到達を表す構成子が無いので、
ハンドラは認可層を経由せずに DB や外界に到達できない。どのアクションをどの行にどの値で呼ぶかだけを渡し、
主体・対象・効果は渡せない。

## HTTP の要約

ハンドラが読める要求は `Http.Request`: メソッド・パス・生の問い合わせ文字列(`?` の後ろ。パーセント符号化のまま。
`Request.queryParams` で復号した組にできる)・nyxis が選別したヘッダ(`RequestHeader`: Accept・Accept-Language・
Content-Type・If-None-Match・If-Match。名前は型で列挙され、Authorization と Cookie には構成子が無いので
ハンドラには届かない。JWT はランタイムが読んで主体に変える)・本文。

ハンドラが返す応答は `Http.Response`: 状態コード・本文・nyxis が許す少数の応答ヘッダ(`ResponseHeader`:
Content-Type・Cache-Control・ETag・Location。名前は型で列挙され、Set-Cookie には構成子が無い)。
Content-Type を設定しなければ `text/plain; charset=utf-8`。HTTP のヘッダ値として妥当でない値(改行・制御文字・非 ASCII)と、
認証済みの主体への応答を共有キャッシュが別の主体へ再送することを許す Cache-Control の `public` / `s-maxage` は
接続層が捨てる(`Nyxis.Http.responseBuilder`)。
-/

namespace Nyxis

open Cedar.Spec

/-- ハンドラのプログラム。`pure` か、アクション呼び出し `call` の後に続きを待つかのどちらか。 -/
inductive Handler (α : Type) : Type where
  /-- 値を返して終わる。 -/
  | pure (a : α) : Handler α
  /-- アクション `action` を主キー `key` の行に、提案する値 `values` で呼び、結果を受けて続ける。一覧の効果では
      `key` と `values` は使われず、問い合わせ `query`(絞り込み・並べ替え・ページ)が使われる。 -/
  | call (action : EntityUID) (key : Db.Key) (values : Db.Row) (query : Db.ListQuery) (k : Outcome → Handler α) :
      Handler α

namespace Handler

/-- 逐次合成。 -/
protected def bind {α β : Type} : Handler α → (α → Handler β) → Handler β
  | .pure a, f => f a
  | .call action key values query k, f => .call action key values query (fun o => Handler.bind (k o) f)

instance : Monad Handler where
  pure := .pure
  bind := Handler.bind

/-- アクションを呼ぶ。ハンドラが持てる唯一の効果。提案する値の集合・レコードは `Cedar.Data.Set.make` /
    `Map.make` で作る(`Set.mk` / `Map.mk` で作った整列していない・重複のある値は保存形式にできず、
    実 DB の接続層はその書き込みを拒み要求を閉じる。純粋なモデル `Runtime.handleRequest` はそのまま
    受け入れるので、モデルの検査では気づけない)。 -/
def callAction (action : EntityUID) (key : Db.Key) (values : Db.Row := Cedar.Data.Map.empty) :
    Handler Outcome :=
  .call action key values {} .pure

/-- 一覧のアクションを、絞り込み・並べ替え・ページの問い合わせを添えて呼ぶ。主キーと値は使われない。
    結果は `Outcome.list rows total`(返す行と、絞り込みに合い permit された行の数)。 -/
def callList (action : EntityUID) (query : Db.ListQuery := {}) : Handler Outcome :=
  .call action "" Cedar.Data.Map.empty query .pure

end Handler

namespace Http

/-- ハンドラに渡す要求ヘッダの名前。nyxis が選別した少数だけで、Authorization と Cookie は無い。 -/
inductive RequestHeader where
  | accept
  | acceptLanguage
  | contentType
  | ifNoneMatch
  | ifMatch
  deriving DecidableEq, BEq, Repr, Inhabited

namespace RequestHeader

/-- HTTP 上の名前(小文字)。 -/
def name : RequestHeader → String
  | .accept => "accept"
  | .acceptLanguage => "accept-language"
  | .contentType => "content-type"
  | .ifNoneMatch => "if-none-match"
  | .ifMatch => "if-match"

/-- 選別するすべての名前。 -/
def all : List RequestHeader := [.accept, .acceptLanguage, .contentType, .ifNoneMatch, .ifMatch]

/-- 小文字の HTTP の名前から。選別に無い名前(Authorization・Cookie を含む)は `none`。 -/
def ofName? (name : String) : Option RequestHeader :=
  all.find? (·.name == name)

end RequestHeader

/-- ハンドラが設定できる応答ヘッダの名前。nyxis が許す少数だけで、Set-Cookie は無い。 -/
inductive ResponseHeader where
  | contentType
  | cacheControl
  | etag
  | location
  deriving DecidableEq, BEq, Repr, Inhabited

namespace ResponseHeader

/-- HTTP 上の名前(小文字)。 -/
def name : ResponseHeader → String
  | .contentType => "content-type"
  | .cacheControl => "cache-control"
  | .etag => "etag"
  | .location => "location"

/-- 許すすべての名前。 -/
def all : List ResponseHeader := [.contentType, .cacheControl, .etag, .location]

end ResponseHeader

/-- ハンドラに渡す HTTP リクエストの要約。JWT はランタイムが読んで主体に変え、ハンドラには渡さない。
    `query` は生の問い合わせ文字列(`?` の後ろ。無ければ空)、`headers` は nyxis が選別した要求ヘッダ
    (同じ名前が複数あれば受け取った順に複数)。 -/
structure Request where
  method : Std.Http.Method
  path : String
  body : String
  query : String := ""
  headers : List (RequestHeader × String) := []

/-- ハンドラが返す HTTP レスポンス。`headers` は nyxis が許す応答ヘッダ(同じ名前は最初のものだけが使われ、
    HTTP のヘッダ値として妥当でない値(改行・制御文字・非 ASCII)と、共有キャッシュへの保存を許す
    Cache-Control の `public` / `s-maxage` は捨てられる)。Content-Type を設定しなければ `text/plain; charset=utf-8`。 -/
structure Response where
  status : Std.Http.Status
  body : String
  headers : List (ResponseHeader × String) := []

/-- ルーティング。メソッドとパスから、主体・サーバー生成値(nyxis が要求ごとに決めた現在時刻と新しい一意 ID。
    値の提案に使う)・リクエストを受け取るハンドラを選ぶ。`none` なら 404。 -/
abbrev Router :=
  Std.Http.Method → String → Option (Authz.Principal → Authz.Generated → Request → Handler Response)

/-! ## 問い合わせ文字列の復号 -/

/-- 16 進の 1 桁。 -/
private def hexValue? (c : UInt8) : Option UInt8 :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else none

/-- 問い合わせ文字列の要素を復号する: `%XX` はそのバイト、`+` は空白。`%` の後ろが 16 進 2 桁でない、または
    結果が UTF-8 でなければ `none`。 -/
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

/-- 問い合わせ文字列を (名前, 値) の組に分ける。`&` で区切り、最初の `=` で名前と値に分け(`=` が無ければ値は空)、
    それぞれを `decodeComponent` で復号する。復号できない組と空の要素は捨てる。 -/
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

/-- 復号した問い合わせの組。 -/
def Request.queryParams (r : Request) : List (String × String) := parseQuery r.query

/-- 問い合わせの最初の値。 -/
def Request.queryParam? (r : Request) (name : String) : Option String :=
  (r.queryParams.find? (·.1 == name)).map (·.2)

/-- 選別された要求ヘッダの最初の値。 -/
def Request.header? (r : Request) (name : RequestHeader) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

end Http

end Nyxis
