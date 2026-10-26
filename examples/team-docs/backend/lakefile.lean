import Lake
open Lake DSL

-- ルートの lakefile.lean と同じ定義。require 先のリンク引数は伝わらないため、各パッケージが libpq を解決する。
-- 両方を同じに保つ。
def postgresLinkArgs : Array String := run_io do
  let libs ← IO.Process.run { cmd := "pkg-config", args := #["--libs", "libpq"] }
  let dir ← IO.Process.run { cmd := "pkg-config", args := #["--variable=libdir", "libpq"] }
  if System.Platform.isOSX then
    -- pkg-config が -L を省いても、Lean 同梱のリンカはシステムの libdir を探さないことがある。
    return #[s!"-L{dir.trimAscii}"] ++ libs.trimAscii.toString.splitOn.toArray.filter (· != "")
  -- Linux では -L<システムの libdir> を渡すと、Lean 同梱の sysroot の libc・libssl よりシステムのものが先に
  -- 選ばれてリンクが失敗する。libpq だけを絶対パスで渡し、libpq が要求する新しい glibc の版は実行時に解決する。
  return #[s!"{dir.trimAscii}/libpq.so", "-Wl,--allow-shlib-undefined"]

package teamDocs where
  version := v!"0.1.0"
  moreLinkArgs := postgresLinkArgs

require nyxis from "../../.."

input_file appSchema where
  path := "schema.cedarschema"
  text := true
input_file appPolicies where
  path := "policies.cedar"
  text := true

@[default_target]
lean_lib TeamDocs where
  needs := #[appSchema, appPolicies]

@[default_target]
lean_lib TeamDocsTest where
  needs := #[appSchema, appPolicies]

@[default_target]
lean_exe teamDocs where
  root := `Main
  needs := #[appSchema, appPolicies]

@[default_target]
lean_exe initTeamDocsDatabase where
  root := `InitDatabase
  needs := #[appSchema, appPolicies]
