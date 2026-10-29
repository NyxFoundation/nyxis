#!/bin/sh
# Exercise the approved JWT dependencies from a disposable Lake project (no git, root Lake config untouched).
# Preflight of the libraries and the core verifier; the sample's own path is checked by check-sample-jwt-db.py.
set -eu
case "${1:-}" in
  ""|--local-postgres|--local-auth) ;;
  *) echo "usage: check-jwt-dependency.sh [--local-postgres|--local-auth]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || exit 2
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/nyxis-jwt.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
pkg-config --modversion libcrypto
# Re-verify the installed tree (revision, archive SHA256, the lean-pq patch); no download when it matches.
python3 "$root/scripts/prepare-dependencies.py"
python3 - "$work" "$root" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

work, root = map(Path, sys.argv[1:])
(work / "schema.cedarschema").write_text((root / "examples/bulletin-board/backend/schema.cedarschema").read_text())
# The approved libraries come from the tree prepare-dependencies.py just verified. No second copy.
vendor = root / ".lake/vendor"
for name in ("lean-jose", "jose-libcrypto", "lean-libcrypto", "lean-json", "leancrypto"):
    if not (vendor / name / "lakefile.lean").exists():
        raise SystemExit(f"{name}: run python3 scripts/prepare-dependencies.py first")
paths = {name: vendor / name for name in ("jose-libcrypto",)}

check = work / "check"
check.mkdir()
(check / "lean-toolchain").write_text((root / "lean-toolchain").read_text())
(check / "ServeHttp.lean").write_text((root / "scripts/jwt-dependency/ServeHttp.lean").read_text())
(check / "Main.lean").write_text((root / "scripts/jwt-dependency/Main.lean").read_text())
# Same rule as postgresLinkArgs in lakefile.lean: on Linux, -L <system libdir> makes Lean's linker
# pick the system libc instead of the bundled one, so pass libpq by its full path there.
pq_dir = subprocess.check_output(['pkg-config', '--variable=libdir', 'libpq'], text=True).strip()
pq_libs = subprocess.check_output(['pkg-config', '--libs', 'libpq'], text=True).split()
if sys.platform == 'darwin':
    pq_link_args = ['-L' + pq_dir] + pq_libs
else:
    pq_link_args = [pq_dir + '/libpq.so' if a == '-lpq' else a for a in pq_libs]
(check / "lakefile.lean").write_text(
    'import Lake\nopen Lake DSL\nrequire «jose-libcrypto» from '
    + json.dumps(str(paths["jose-libcrypto"]))
    + '\nrequire batteries from ' + json.dumps(str(root / '.lake/packages/batteries'))
    + '\nrequire Cedar from ' + json.dumps(str(root / '.lake/packages/Cedar/cedar-lean'))
    + '\nrequire leanPq from ' + json.dumps(str(root / '.lake/vendor/lean-pq'))
    + '\nrequire nyxis from ' + json.dumps(str(root))
    + '\nrequire bulletinBoard from ' + json.dumps(str(root / 'examples/bulletin-board/backend'))
    + '\npackage jwtCheck where\n  moreLinkArgs := #['
    + ', '.join(json.dumps(x) for x in pq_link_args)
    + ']\n@[default_target]\nlean_exe checkJwt where\n  root := `Main\n'
    + '@[default_target]\nlean_exe serveJwtHttp where\n  root := `ServeHttp\n')

subprocess.run([sys.executable, str(root / "scripts/jwt-dependency/make-fixture.py"), str(work)], check=True)
PY
# A new scratch manifest must never cause Lake to clone inherited root dependencies.
# Direct path overrides above reuse the already prepared root cache; enforce no git.
mkdir "$work/no-git"
printf '%s\n' '#!/bin/sh' 'echo "git is forbidden in the JWT check" >&2' 'exit 99' > "$work/no-git/git"
chmod +x "$work/no-git/git"
if PATH="$work/no-git:$PATH" lake build --dir "$work/check" > "$work/build.log" 2>&1; then
  tail -1 "$work/build.log"
else
  cat "$work/build.log"
  exit 1
fi
"$work/check/.lake/build/bin/checkJwt" "$work"

python3 "$root/scripts/jwt-dependency/check-http.py" "$work"

if [ "${1:-}" = --local-postgres ] || [ "${1:-}" = --local-auth ]; then
  python3 "$root/scripts/jwt-dependency/check-local-db.py" "$work"
fi

if [ "${1:-}" = --local-auth ]; then
  python3 "$root/scripts/jwt-dependency/check-local-auth.py" "$work"
fi
