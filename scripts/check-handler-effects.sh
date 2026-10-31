#!/bin/sh
# Check: a handler cannot have any effect other than action calls to the authorization layer.
#
# (1) `lake build` exits non-zero for variants of the sample. A variant is made by placing BulletinBoard/Variant.lean
# and importing it from BulletinBoard.lean (so it is included in the default `lake build` target). Each variant contains
# exactly one violating handler, and the check confirms that the error is reported at that handler's line. db-apply — a
# handler that tries to run an operation of the nyxis DB layer (`Nyxis.Db.Store.apply`) as a handler effect, bypassing
# the authorization layer. db-issue — a handler that tries to pass a DB operation (`Nyxis.Db.Operation`) to
# `Handler.call`, the only effect constructor of a handler. io-handler — a handler that performs IO (writing to standard
# output and reading a file). All are type errors because the type of `Nyxis.Handler` does not allow them: `Handler` is
# a free monad consisting only of `pure` and `call` (action, primary key, proposed values), with no lift into IO
# (`MonadLift IO Handler`) and no constructor that takes a DB operation or DB state. A handler can compute pure
# functions of the DB layer as values, but those are the handler's local data; they cannot reach the runtime DB (the
# `Store` held by `Nyxis.Runtime`) by any path other than `Handler.call`.
# (2) The sample's application-side Lean sources (all .lean files under BulletinBoard/ and BulletinBoard.lean) contain
# no `unsafe` / `implemented_by` / `extern` / `sorry` (0 grep matches).
#
# (3) Variants with debug output, panic, attributes, initialization or metaprograms that do type-check are also rejected
# by nyxis_check_app in BulletinBoard.lean. Other namespaces and private helper functions are also checked. The check
# does not isolate the execution of build-time IO. IO in main, the internals of trusted dependencies, and configurations
# that drop the check are outside this check's guarantee. For the exact scope and the remaining assumptions, see
# Assumption 3 in ASSUMPTIONS.md.
#
# Exit 0 if all of these hold, otherwise 1. After the variants, the original is restored and `lake build` is confirmed
# to exit 0 again. The original is saved to a temporary directory and restored by a trap even if interrupted (the
# temporary directory is kept).
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

# $1 = variant name, $2 = variant Lean source (file), $3 = line number where the violating handler's error should be
# reported, $4 onward = error words expected in the build log (all required)
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

/-! Variant db-apply: a handler that runs a DB-layer operation as an effect, bypassing the authorization layer. Must not build. -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz Nyxis.Db

/-- Tries to run a DB-layer operation as a handler effect. -/
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

/-! Variant db-issue: a handler that passes a DB operation directly to the handler's effect constructor. Must not build. -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz Nyxis.Db

/-- Tries to pass a DB operation to the handler's only effect constructor. -/
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

/-! Variant io-handler: a handler that performs IO. Must not build. -/

namespace BulletinBoard.Variant

open Nyxis Nyxis.Authz

/-- Writes to standard output and reads a file. -/
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
audit_variant axiom-decl 'depends on axiom BulletinBoard.cheat' <<'EOF'
axiom BulletinBoard.cheat : False
EOF
audit_variant forged-bound 'depends on axiom BulletinBoard.cheat' <<'EOF'
axiom BulletinBoard.cheat : False
namespace Unrelated
def peek (i : Nat) : UInt8 := (ByteArray.mk #[0]).get i BulletinBoard.cheat.elim
end Unrelated
def BulletinBoard.leak : Nyxis.Handler Nyxis.Http.Response :=
  pure { status := .ok, body := toString (Unrelated.peek 4096) }
EOF
audit_variant native-decide 'depends on axiom' <<'EOF'
theorem BulletinBoard.viaNative : 2 + 2 = 4 := by native_decide
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

# (2) The whole application-side Lean code (handlers, declarations, startup, checks) contains no bypass words.
# Matched as whole words (does not match `external` etc.); grep exits 0 = found, 1 = none, other = failure.
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
