#!/bin/sh
# Wiring check for the Store-backed HTTP server (a preliminary stage before the real-DB integration tests; the principal
# is always anonymous, and no real DB is used).
#
# After `lake build`, start serveFixture with the test initial state (BulletinBoardTest.Fixture.store) and compare each
# endpoint's status code and body using curl. It confirms that the method, path and body reach the model
# (Nyxis.Runtime.handleRequest), that the handler's response is returned over HTTP as-is, that only the reads allowed
# for the anonymous principal succeed and everything else is denied, and that denials do not change the state. Usage: sh
# scripts/check-http.sh (the environment variable NYXIS_CHECK_PORT changes the listening port; default 18111). Exits 0
# on success.
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
  # $1 = executable. Fails if the port is already in use (so as not to check another server's responses).
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

# expect <expected status code> <method> <path> [body] [string the response body must contain]
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
# Anonymous can read only published posts, and the body is the row's JSON.
expect 200 GET /posts/pub1 "" '"title":"public"'
expect 200 GET /posts/pub1 "" '"author":"alice"'
expect 200 'GET' '/posts/pub1?x=1' "" '"published":true'
expect 403 GET /posts/draft1
expect 403 GET /posts/ghost
# Anonymous cannot create, edit, publish, delete or grant permissions. If the body cannot be parsed, 400 is returned and
# no action is called.
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
# Denied operations did not change the state.
expect 200 GET /posts/pub1 "" '"title":"public"'
expect 403 GET /posts/draft1
stop_server

if [ "$FAILURES" -ne 0 ]; then
  echo "check-http: $FAILURES failure(s)"
  exit 1
fi
echo "check-http: all passed"
exit 0
