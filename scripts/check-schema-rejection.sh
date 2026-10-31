#!/bin/sh
# Check: nyxis rejects, at build time, a schema with an action that has no effect declaration, or with an effect that
# references a column not in the schema. Two variants are made from the sample schema examples/bulletin-board/backend/schema.cedarschema:
# (1) no-effect — remove the @effect of one action (deletePost) (2) unknown-column — write a nonexistent column bodyy in
# the effect of editPost Each is temporarily put in place of the original and `lake build` is run; it passes if the
# build exits non-zero and reports the expected error. Finally the original is restored and `lake build` is checked to
# exit 0 again. Exit 0 if all of this holds, otherwise 1. The original is saved in a temporary directory and restored by
# a trap even on interruption (the temporary directory is kept).
set -u
cd "$(dirname "$0")/../examples/bulletin-board/backend" || exit 1

schema=schema.cedarschema
tmp=$(mktemp -d) || exit 1
backup="$tmp/schema.cedarschema"
cp "$schema" "$backup" || exit 1
restore() { cp "$backup" "$schema"; }
trap restore EXIT
trap 'restore; exit 130' INT TERM HUP
echo "backup and logs: $tmp"

status=0

# $1 = variant name, $2 = sed script applied to the original, $3 = error text expected in the build log
try_variant() {
  name=$1
  script=$2
  expect=$3
  sed -e "$script" "$backup" > "$schema" || { echo "$name: sed failed"; status=1; return; }
  if cmp -s "$backup" "$schema"; then
    echo "$name: variant is identical to the original (sed matched nothing; the sample schema may have changed)"
    status=1
    return
  fi
  log="$tmp/$name.log"
  lake build > "$log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "$name: lake build exit 0 -- NOT rejected"
    status=1
  elif grep -q "$expect" "$log"; then
    echo "$name: lake build exit $rc -- rejected with the expected error:"
    grep -m1 'error:' "$log" | sed 's/^/  /'
  else
    echo "$name: lake build exit $rc but the expected error ($expect) was not reported:"
    grep -m3 'error' "$log" | sed 's/^/  /'
    status=1
  fi
}

try_variant no-effect '/^@effect("delete Post")$/d' 'has no effect declaration (@effect)'
try_variant unknown-column 's/^@effect("update Post(title, body)")$/@effect("update Post(title, bodyy)")/' 'column bodyy is not in table Post'

restore
if lake build > "$tmp/restored.log" 2>&1; then
  echo "restored: lake build exit 0"
else
  echo "restored: lake build FAILED (see $tmp/restored.log)"
  status=1
fi

[ "$status" -eq 0 ] && echo "schema rejection: both variants rejected at build time, original builds"
exit "$status"
