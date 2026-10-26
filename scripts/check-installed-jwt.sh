#!/bin/sh
# Verify the root package's installed JOSE/OpenSSL backend with throwaway material.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/nyxis-installed-jwt.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
python3 "$root/scripts/prepare-dependencies.py"
python3 "$root/scripts/jwt-dependency/make-fixture.py" "$work"
"$root/.lake/build/bin/checkJwtDependency" "$work"
