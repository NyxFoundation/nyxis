#!/bin/sh
# 検査: ハンドラは認可層へのアクション呼び出し以外の効果を持てない。
#
# (1) サンプルの変種で `lake build` が非 0 で終わること。変種は BulletinBoard/Variant.lean を置き、BulletinBoard.lean から
#     import する形で作る(`lake build` の既定の対象に含まれる)。変種ごとに違反するハンドラを 1 つだけ含め、
#     そのハンドラの行でエラーが報告されることを確かめる。
#       db-apply   — 認可層を通さず、nyxis の DB 層の操作(`Nyxis.Db.Store.apply`)をハンドラの効果として
#                    実行しようとするハンドラ。
#       db-issue   — DB 操作(`Nyxis.Db.Operation`)を、ハンドラの唯一の効果の構成子 `Handler.call` に
#                    渡そうとするハンドラ。
#       io-handler — IO(標準出力への書き込みとファイルの読み取り)を行うハンドラ。
#     いずれも `Nyxis.Handler` の型が許さないので型エラーになる: `Handler` は `pure` と `call`(アクション・
#     主キー・提案する値)だけから成る自由モナドで、IO への持ち上げ(`MonadLift IO Handler`)も、DB 操作や
#     DB の状態を受け取る構成子も無い。ハンドラが DB 層の純粋な関数を値として計算することはできるが、それは
#     ハンドラの局所データで、ランタイムの DB(`Nyxis.Runtime` が持つ `Store`)には `Handler.call` 以外の
#     経路で届かない。
# (2) サンプルのアプリケーション側のLeanソース(BulletinBoard/内の全.lean と BulletinBoard.lean)に `unsafe` / `implemented_by` / `extern` /
#     `sorry` が無いこと(grep で 0 件)。
#
# (3) 型が通るデバッグ出力・panic・属性・初期化・メタプログラムの変種も、BulletinBoard.lean の
#     nyxis_check_app が拒否する。別の名前空間・private な補助関数も検査する。
# 検査はビルド時 IO の実行を隔離しない。main の IO、信頼済み依存の内部、検査を外した構成も
# この検査の保証外。正確な範囲と残る仮定は ASSUMPTIONS.md A7 を参照。
#
# すべて満たせば exit 0、さもなくば 1。変種の後は正本を戻し、`lake build` が exit 0 に戻ることも確かめる。
# 正本は一時ディレクトリに退避し、中断しても trap で戻す(一時ディレクトリは残す)。
set -u
cd "$(dirname "$0")/../examples/bulletin-board/backend" || exit 1

root=BulletinBoard.lean
variant=BulletinBoard/Variant.lean

if [ -e "$variant" ]; then
  echo "$variant already exists; refusing to overwrite (remove it first)"
  exit 1
fi

tmp=$(mktemp -d) || exit 1
cp "$root" "$tmp/BulletinBoard.lean" || exit 1
restore() { cp "$tmp/BulletinBoard.lean" "$root"; rm -f "$variant"; }
trap restore EXIT
trap 'restore; exit 130' INT TERM HUP
echo "backup and logs: $tmp"

status=0

# $1 = 変種の名前、$2 = 変種の Lean ソース(ファイル)、$3 = 違反するハンドラのエラーが報告されるべき行番号、
# $4 以降 = ビルドログに期待するエラーの語(すべて要る)
try_variant() {
  name=$1
  source=$2
  line=$3
  shift 3
  cp "$source" "$variant" || { echo "$name: cannot place variant"; status=1; return; }
  { echo "import BulletinBoard.Variant"; cat "$tmp/BulletinBoard.lean"; } > "$root"
  log="$tmp/$name.log"
  lake build > "$log" 2>&1
  rc=$?
  restore
  if [ "$rc" -eq 0 ]; then
    echo "$name: lake build exit 0 -- NOT rejected"
    status=1
    return
  fi
  missing=0
  if [ "$line" = audit ]; then
    location='^error: BulletinBoard.lean:.*nyxis app audit:'
  else
    location="^error: BulletinBoard/Variant.lean:$line:"
  fi
  if ! grep -q "$location" "$log"; then
    echo "$name: no error reported at BulletinBoard/Variant.lean:$line (the offending handler)"
    missing=1
  fi
  for expect in "$@"; do
    if ! grep -q -- "$expect" "$log"; then
      echo "$name: expected error text not reported: $expect"
      missing=1
    fi
  done
  if [ "$missing" -eq 0 ]; then
    echo "$name: lake build exit $rc -- rejected with the expected error:"
    grep "$location" "$log" | sed 's/^/  /'
  else
    grep -m5 'error' "$log" | sed 's/^/  /'
    status=1
  fi
}

cat > "$tmp/db-apply.lean" <<'EOF'
import BulletinBoard.Handlers

/-! 変種 db-apply: 認可層を通さず DB 層の操作を効果として実行するハンドラ。ビルドできてはならない。 -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz Nyxis.Db

/-- DB 層の操作をハンドラの効果として実行しようとする。 -/
def applyDirectly : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let (_, outcome) ← Store.apply Cedar.Data.Map.empty (.delete ⟨"Post", []⟩ "pub1")
  pure (BulletinBoard.noContent outcome)

def router : Http.Router := fun method path =>
  match method, path with
  | .delete, "/apply" => some applyDirectly
  | _, _ => BulletinBoard.router method path

end BulletinBoard.Variant
EOF

cat > "$tmp/db-issue.lean" <<'EOF'
import BulletinBoard.Handlers

/-! 変種 db-issue: DB 操作をハンドラの効果の構成子に直接渡すハンドラ。ビルドできてはならない。 -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz Nyxis.Db

/-- DB 操作をハンドラの唯一の効果の構成子に渡そうとする。 -/
def issueDirectly : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  Handler.call (Operation.delete ⟨"Post", []⟩ "pub1") (fun outcome => Handler.pure (BulletinBoard.noContent outcome))

def router : Http.Router := fun method path =>
  match method, path with
  | .delete, "/issue" => some issueDirectly
  | _, _ => BulletinBoard.router method path

end BulletinBoard.Variant
EOF

cat > "$tmp/io-handler.lean" <<'EOF'
import BulletinBoard.Handlers

/-! 変種 io-handler: IO を行うハンドラ。ビルドできてはならない。 -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz

/-- 標準出力に書き、ファイルを読む。 -/
def leak : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  IO.println s!"request: {req.path}"
  let secret ← IO.FS.readFile "/etc/hosts"
  pure { status := .ok, body := secret }

def router : Http.Router := fun method path =>
  match method, path with
  | .get, "/leak" => some leak
  | _, _ => BulletinBoard.router method path

end BulletinBoard.Variant
EOF

try_variant db-apply "$tmp/db-apply.lean" 11 \
  'Type mismatch' 'Store × Outcome' 'but is expected to have type' 'Handler ?m'
try_variant db-issue "$tmp/db-issue.lean" 11 \
  'Application type mismatch' 'Operation.delete' 'but is expected to have type' 'Cedar.Spec.EntityUID'
try_variant io-handler "$tmp/io-handler.lean" 11 \
  'Type mismatch' 'IO Unit' 'but is expected to have type' 'Handler Unit'

# These variants must elaborate successfully; only the final imported-module audit may reject them.
audit_variant() {
  audit_name=$1
  audit_expect=$2
  { echo 'import BulletinBoard.Handlers'; echo 'import Lean'; cat; } > "$tmp/$audit_name.lean"
  try_variant "$audit_name" "$tmp/$audit_name.lean" audit "$audit_expect"
  if grep -q '^error: BulletinBoard/Variant.lean:' "$tmp/$audit_name.log"; then
    echo "$audit_name: invalid fixture (failed before audit)"
    status=1
  fi
}

audit_variant dbg-trace 'forbidden reference dbgTrace' <<'EOF'
def BulletinBoard.leak : Nyxis.Handler Nyxis.Http.Response :=
  dbgTrace "probe" fun _ => pure { status := .ok, body := "x" }
EOF
audit_variant wrapped-trace 'forbidden reference dbgTrace' <<'EOF'
namespace Unrelated
private def helper (s : String) : String := dbgTrace s fun _ => s
def wrapped (s : String) : String := helper s
end Unrelated
def BulletinBoard.leak : Nyxis.Handler Nyxis.Http.Response := pure { status := .ok, body := Unrelated.wrapped "x" }
EOF
audit_variant panic 'forbidden reference panic' <<'EOF'
def BulletinBoard.leak : String := panic! "probe"
EOF
audit_variant initializer 'initializer' <<'EOF'
initialize BulletinBoard.cache : IO.Ref Nat ← IO.mkRef 0
EOF
audit_variant anonymous-initializer 'initializer' <<'EOF'
initialize pure ()
EOF
audit_variant macro 'macro/elaborator attribute' <<'EOF'
macro "sample_literal" : term => `(0)
EOF
audit_variant elaborator 'macro/elaborator attribute' <<'EOF'
open Lean Elab Term
elab "sample_term" : term => pure (mkNatLit 0)
EOF
audit_variant command-elaborator 'macro/elaborator attribute' <<'EOF'
open Lean Elab Command
elab "sample_command" : command => pure ()
EOF
audit_variant unsafe-decl 'unsafe declaration' <<'EOF'
unsafe def BulletinBoard.escape (n : Nat) : Nat := n
EOF
audit_variant extern-decl 'extern attribute' <<'EOF'
@[extern "nyxis_test_unused"] opaque BulletinBoard.escape : Nat → Nat
EOF
audit_variant replaced-decl 'implemented_by attribute' <<'EOF'
def BulletinBoard.replacement (n : Nat) : Nat := n
@[implemented_by BulletinBoard.replacement] def BulletinBoard.escape (n : Nat) : Nat := n
EOF
audit_variant replacement-api 'implemented_by attribute' <<'EOF'
def BulletinBoard.replacement (n : Nat) : Nat := n
def BulletinBoard.escape (n : Nat) : Nat := n
run_cmd Lean.setImplementedBy `BulletinBoard.escape `BulletinBoard.replacement
EOF

# The internal connection module must not turn libpq into an application API.
audit_variant postgres-client 'extern attribute' <<'EOF'
import Nyxis.Internal.Postgres
def BulletinBoard.connectionProbe : IO Unit := do
  let _ ← Nyxis.Internal.Postgres.connect "host=127.0.0.1 port=1 connect_timeout=1"
  pure ()
EOF

# The all-table snapshot continuation is trusted core code, never an application API.
audit_variant postgres-snapshot 'extern attribute' <<'EOF'
import Nyxis.Internal.PostgresLoad
import BulletinBoard.App
def BulletinBoard.snapshotProbe : IO Unit :=
  Nyxis.Internal.PostgresLoad.withSnapshot
    "host=127.0.0.1 port=1 connect_timeout=1" BulletinBoard.schema (fun _ _ => pure ())
EOF

# Model replay is core-only, including its authenticated request entry point.
audit_variant postgres-run 'extern attribute' <<'EOF'
import Nyxis.Internal.PostgresRun
import BulletinBoard.App
def BulletinBoard.runProbe : IO Nyxis.Http.Response :=
  Nyxis.Internal.PostgresRun.handle
    "host=127.0.0.1 port=1 connect_timeout=1"
    { schema := BulletinBoard.schema, policies := BulletinBoard.policies, router := fun _ _ => none }
    []
    { principal := .anonymous, generated := ⟨⟨0⟩, ""⟩, request := { method := .get, path := "/posts/pub1", body := "" } }
EOF

# Importing the HTTP/database bridge from application code must still fail the audit.
audit_variant postgres-http 'extern attribute' <<'EOF'
import Nyxis.Internal.PostgresHttp
import BulletinBoard.App
def BulletinBoard.httpProbe : IO Unit :=
  Nyxis.Internal.PostgresHttp.serveVerifiedApp 18112
    "host=127.0.0.1 port=1 connect_timeout=1"
    { schema := BulletinBoard.schema, policies := BulletinBoard.policies, router := fun _ _ => none }
    [] ⟨"User", []⟩ (fun _ => pure none)
EOF

# Provisioning must remain inaccessible to application code.
audit_variant postgres-init 'extern attribute' <<'EOF'
import Nyxis.Internal.PostgresInit
import BulletinBoard.App
def BulletinBoard.initProbe : IO Unit :=
  Nyxis.Internal.PostgresInit.provision
    "host=127.0.0.1 port=1 connect_timeout=1" BulletinBoard.schema
EOF

# Adopted JWT/OpenSSL FFI stays outside the application's trusted module set.
audit_variant jwt-libcrypto 'extern attribute' <<'EOF'
import JoseLibcrypto
def BulletinBoard.cryptoProbe : Nat := 0
EOF

audit_variant supabase-jwt 'extern attribute' <<'EOF'
import Nyxis.Internal.SupabaseJwt
def BulletinBoard.jwtProbe : IO Unit := do
  let _ ← Nyxis.Internal.SupabaseJwt.prepare "https://example.supabase.co/auth/v1" "{}"
  pure ()
EOF

audit_variant jwks-fetch 'extern attribute' <<'EOF'
import Nyxis.Internal.JwksFetch
def BulletinBoard.fetchProbe : IO Unit := do
  let _ ← Nyxis.Internal.JwksFetch.fetch "https://example.supabase.co/auth/v1"
  pure ()
EOF

# Startup wiring must stay outside the audited handler module graph.
audit_variant sample-server 'extern attribute' <<'EOF'
import BulletinBoard.Server
def BulletinBoard.serverProbe : IO Unit :=
  BulletinBoard.Server.serve 18112
    "host=127.0.0.1 port=1 connect_timeout=1"
    "https://example.supabase.co/auth/v1" BulletinBoard.router
EOF

restore
if lake build > "$tmp/restored.log" 2>&1; then
  echo "restored: lake build exit 0"
else
  echo "restored: lake build FAILED (see $tmp/restored.log)"
  status=1
fi

# (2) アプリケーション側の Lean コード全体(ハンドラ・宣言・起動・検査)に迂回の語が無い。
# 語単位で照合し(`external` 等には一致しない)、grep の exit は 0 = 見つかった、1 = 無し、他 = 失敗。
pattern='unsafe|implemented_by|extern|sorry'
grep -rnwE --include='*.lean' -- "$pattern" BulletinBoard BulletinBoard.lean BulletinBoardTest BulletinBoardTest.lean Main.lean InitDatabase.lean > "$tmp/grep.log" 2>&1
rc=$?
case $rc in
  0) echo "forbidden words found in application code:"; sed 's/^/  /' "$tmp/grep.log"; status=1 ;;
  1) echo "grep: no unsafe / implemented_by / extern / sorry in the application package's Lean sources" ;;
  *) echo "grep failed (exit $rc):"; sed 's/^/  /' "$tmp/grep.log"; status=1 ;;
esac

[ "$status" -eq 0 ] && echo "handler effects: all variants rejected at build time, original builds, application code clean"
exit "$status"
