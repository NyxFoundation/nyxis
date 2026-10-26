#!/bin/sh
# 検査: nyxis が、効果の宣言が無いアクションや、スキーマに無い列を効果が参照するスキーマを
# ビルド時に拒むことを確かめる。サンプルのスキーマ BulletinBoard/schema.cedarschema から 2 つの変種を作り、
#   (1) no-effect       — 1 つのアクション(deletePost)の @effect を消す
#   (2) unknown-column  — editPost の効果に存在しない列 bodyy を書く
# それぞれを正本の場所に一時的に置いて `lake build` を走らせ、非 0 で終わり期待するエラーが報告されれば合格。
# 終わりに正本を戻し、`lake build` が exit 0 に戻ることも確かめる。すべて満たせば exit 0、さもなくば 1。
# 正本は一時ディレクトリに退避し、中断しても trap で戻す(一時ディレクトリは残す)。
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

# $1 = 変種の名前、$2 = 正本に施す sed のスクリプト、$3 = ビルドログに期待するエラーの語
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

try_variant no-effect '/^@effect("delete Post")$/d' '効果の宣言(@effect)が無い'
try_variant unknown-column 's/^@effect("update Post(title, body)")$/@effect("update Post(title, bodyy)")/' '列 bodyy はテーブル Post に無い'

restore
if lake build > "$tmp/restored.log" 2>&1; then
  echo "restored: lake build exit 0"
else
  echo "restored: lake build FAILED (see $tmp/restored.log)"
  status=1
fi

[ "$status" -eq 0 ] && echo "schema rejection: both variants rejected at build time, original builds"
exit "$status"
