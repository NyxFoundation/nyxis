import Lake
open Lake DSL

-- ルートの lakefile.lean と同じ定義。require 先のリンク引数は伝わらないため、各パッケージが libpq を解決する。
-- 両方を同じに保つ。
def postgresLinkArgs : Array String := run_io do
  let libs ← IO.Process.run { cmd := "pkg-config", args := #["--libs", "libpq"] }
  let dir := (← IO.Process.run { cmd := "pkg-config", args := #["--variable=libdir", "libpq"] }).trimAscii.toString
  let libs := libs.trimAscii.toString.splitOn.toArray.filter (· != "")
  -- pkg-config が -L を省いても、Lean 同梱のリンカはシステムの libdir を探さないことがある。
  if System.Platform.isOSX then
    return #[s!"-L{dir}"] ++ libs
  -- Linux では -L でシステムの libdir を足すと、Lean 同梱の古い glibc ではなくシステムの libc を拾い、
  -- 同梱の Scrt1.o が参照する __libc_csu_init が見つからずリンクに失敗する。libpq だけをフルパスで渡す。
  return libs.map fun a => if a == "-lpq" then s!"{dir}/libpq.so" else a

-- Linux では Lake が lean-libcrypto の libcrypto_shim.so を -L/-l でリンクするだけで実行時の探索先を埋め込まず、
-- 実行ファイルを直接起動すると見つからない。macOS が dylib の絶対パスを埋め込むのに合わせ、絶対パスの rpath を足す。
def cryptoShimLinkArgs (nyxisDir : System.FilePath) : Array String :=
  if System.Platform.isOSX then #[]
  else #[s!"-Wl,-rpath,{nyxisDir / ".lake" / "vendor" / "lean-libcrypto" / ".lake" / "build" / "lib"}"]

package bulletinBoard where
  version := v!"0.1.0"
  moreLinkArgs := postgresLinkArgs ++ cryptoShimLinkArgs (__dir__ / ".." / ".." / "..")

require nyxis from "../../.."

input_file appSchema where
  path := "schema.cedarschema"
  text := true
input_file appPolicies where
  path := "policies.cedar"
  text := true

@[default_target]
lean_lib BulletinBoard where
  needs := #[appSchema, appPolicies]

@[default_target]
lean_lib BulletinBoardTest where
  needs := #[appSchema, appPolicies]

@[default_target]
lean_exe sample where
  root := `Main

@[default_target]
lean_exe initSampleDatabase where
  root := `InitDatabase

@[default_target]
lean_exe serveFixture where
  root := `BulletinBoardTest.ServeFixture

@[default_target]
lean_exe checkPostgresRun where
  root := `BulletinBoardTest.PostgresRun

@[default_target]
lean_exe servePostgresHttp where
  root := `BulletinBoardTest.ServePostgresHttp
