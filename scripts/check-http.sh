#!/bin/sh
# Store版HTTPの配線検査(実 DB の統合テストの前段。主体は匿名のみ、実DBではない)。
#
# `lake build` の後、検査用の初期状態(BulletinBoardTest.Fixture.store)で serveFixture を起動し、
# curlで各エンドポイントの状態コードと本文を照合する。確かめるのは、メソッド・パス・
# 本文がモデル(Nyxis.Runtime.handleRequest)に届き、ハンドラのレスポンスがそのまま HTTP で返ること、匿名の
# 主体で許可される読み取りだけが成功し、それ以外が拒否されること、状態が拒否で変わらないこと。
# 使い方: sh scripts/check-http.sh(環境変数 NYXIS_CHECK_PORT で待ち受けポートを変えられる。既定 18111)。
# 成功なら exit 0。
set -u
cd "$(dirname "$0")/../examples/bulletin-board/backend" || exit 2

PORT="${NYXIS_CHECK_PORT:-18111}"
BASE="http://127.0.0.1:$PORT"
TMP="$(mktemp -d)"
FAILURES=0
SERVER_PID=""

stop_server() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null
    wait "$SERVER_PID" 2>/dev/null
    SERVER_PID=""
  fi
}
cleanup() {
  stop_server
  rm -f "$TMP"/* 2>/dev/null
  rmdir "$TMP" 2>/dev/null
}
trap cleanup EXIT
trap 'cleanup; exit 1' INT TERM

start_server() {
  # $1 = 実行ファイル。ポートが既に使われていれば(他のサーバの応答を検査しないよう)失敗する。
  if curl -s -o /dev/null "$BASE/health" 2>/dev/null; then
    echo "FAIL: port $PORT is already in use (set NYXIS_CHECK_PORT)"
    exit 1
  fi
  "$1" "$PORT" > "$TMP/server.log" 2>&1 &
  SERVER_PID=$!
  if ! curl -s -o /dev/null --retry 20 --retry-delay 1 --retry-connrefused "$BASE/health" || ! kill -0 "$SERVER_PID" 2>/dev/null; then
    echo "FAIL: $1 did not start on port $PORT"
    cat "$TMP/server.log"
    exit 1
  fi
}

# expect <期待する状態コード> <メソッド> <パス> [本文] [本文に含まれるべき文字列]
expect() {
  want="$1"; method="$2"; path="$3"; data="${4:-}"; needle="${5:-}"
  if [ -n "$data" ]; then
    got="$(curl -s -o "$TMP/body" -w '%{http_code}' -X "$method" -H 'Content-Type: application/json' --data "$data" "$BASE$path")"
  else
    got="$(curl -s -o "$TMP/body" -w '%{http_code}' -X "$method" "$BASE$path")"
  fi
  body="$(cat "$TMP/body")"
  if [ "$got" != "$want" ]; then
    echo "FAIL: $method $path -> $got (want $want) body=$body"
    FAILURES=$((FAILURES + 1))
    return
  fi
  if [ -n "$needle" ]; then
    case "$body" in
      *"$needle"*) ;;
      *) echo "FAIL: $method $path -> $got but body lacks $needle: $body"; FAILURES=$((FAILURES + 1)); return ;;
    esac
  fi
  echo "ok:   $method $path -> $got"
}

echo "== lake build"
if ! lake build > "$TMP/build.log" 2>&1; then
  echo "FAIL: lake build"
  tail -40 "$TMP/build.log"
  exit 1
fi

echo "== serveFixture (BulletinBoardTest.Fixture.store: alice/bob/root, pub1 published, draft1 draft; principal = anonymous)"
start_server .lake/build/bin/serveFixture
expect 200 GET /health "" ok
expect 404 GET /nope
expect 404 PUT /posts/pub1 '{"title":"x"}'
# 匿名は公開済み投稿だけ読め、本文は行の JSON。
expect 200 GET /posts/pub1 "" '"title":"public"'
expect 200 GET /posts/pub1 "" '"author":"alice"'
expect 200 'GET' '/posts/pub1?x=1' "" '"published":true'
expect 403 GET /posts/draft1
expect 403 GET /posts/ghost
# 匿名は作成・編集・公開・削除・権限付与のどれもできない。本文が読めなければ 400 でアクションは呼ばれない。
expect 400 POST /posts/new1 'not json'
expect 400 POST /posts/new1 '{"title":"only"}'
expect 403 POST /posts/new1 '{"title":"t","body":"b"}'
expect 403 GET /posts/new1
expect 400 PATCH /posts/pub1 '{}'
expect 403 PATCH /posts/pub1 '{"title":"x"}'
expect 403 POST /posts/pub1/publish
expect 403 POST /posts/pub1/unpublish
expect 403 DELETE /posts/pub1
expect 403 PUT /users/bob/admin '{"admin":true}'
expect 400 PUT /users/bob/admin '{"admin":"yes"}'
# 拒否された操作で状態は変わっていない。
expect 200 GET /posts/pub1 "" '"title":"public"'
expect 403 GET /posts/draft1
stop_server

if [ "$FAILURES" -ne 0 ]; then
  echo "check-http: $FAILURES failure(s)"
  exit 1
fi
echo "check-http: all passed"
exit 0
