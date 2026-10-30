import Lake
open Lake DSL

-- The same definition as in the root lakefile.lean. Link arguments of a required package are not propagated, so each
-- package resolves libpq. Keep both identical.
def postgresLinkArgs : Array String := run_io do
  let libs ← IO.Process.run { cmd := "pkg-config", args := #["--libs", "libpq"] }
  let dir := (← IO.Process.run { cmd := "pkg-config", args := #["--variable=libdir", "libpq"] }).trimAscii.toString
  let libs := libs.trimAscii.toString.splitOn.toArray.filter (· != "")
  -- Even if pkg-config omits -L, the linker bundled with Lean may not search the system libdir.
  if System.Platform.isOSX then
    return #[s!"-L{dir}"] ++ libs
  -- On Linux, adding the system libdir with -L picks up the system libc instead of the older glibc bundled with Lean,
  -- and linking fails because __libc_csu_init, referenced by the bundled Scrt1.o, is not found. Pass only libpq by full
  -- path.
  return libs.map fun a => if a == "-lpq" then s!"{dir}/libpq.so" else a

-- On Linux, Lake only links lean-libcrypto's libcrypto_shim.so with -L/-l and does not embed a runtime search path, so
-- launching the executable directly fails to find it. To match macOS, which embeds the dylib's absolute path, add an
-- absolute rpath.
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
