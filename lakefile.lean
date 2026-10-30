import Lake
open Lake DSL

-- Link arguments inside the lean-pq package are not propagated to the executables of packages that require it. Resolve
-- libpq without embedding a machine-specific install location. Prerequisites: pkg-config and the libpq development
-- files (brew install libpq / libpq-dev; for Homebrew's keg-only libpq, add $(brew --prefix libpq)/lib/pkgconfig to
-- PKG_CONFIG_PATH). An application package that requires nyxis must also have the same definition in its own lakefile.
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

package nyxis where
  version := v!"0.1.8"
  moreLinkArgs := postgresLinkArgs ++ cryptoShimLinkArgs __dir__

require Cedar from git "https://github.com/cedar-policy/cedar-spec" @
  "6d7fb269d5eec6ce4ae1d4aff9794feba0c0d5a9" / "cedar-lean"
-- Approved pinned dependencies (lean-pq, and lean-jose/jose-libcrypto/lean-libcrypto for JWT, plus their transitive
-- dependencies). python3 scripts/prepare-dependencies.py places them in .lake/vendor/ from archives pinned by SHA256,
-- without using git.
require leanPq from ".lake/vendor/lean-pq"
require «jose-libcrypto» from ".lake/vendor/jose-libcrypto"

@[default_target]
lean_lib Nyxis

-- The policy fixture that Test/Policy.lean embeds at build time. Rebuild Test after changing it.
input_file testPolicies where
  path := "Test/policies-fixture.cedar"
  text := true

-- The test schema and policies that Test/PostgresValues.lean embeds at build time.
input_file valuesSchema where
  path := "Test/values-fixture.cedarschema"
  text := true

input_file valuesPolicies where
  path := "Test/values-fixture.cedar"
  text := true

@[default_target]
lean_lib Test where
  needs := #[testPolicies, valuesSchema, valuesPolicies]

-- Smoke test for importing lean-pq and native linking (needs neither a DB nor credentials).
@[default_target]
lean_exe checkPostgresDependency where
  root := `Test.PostgresDependency

-- Check of transaction failure paths (injected driver; no DB needed).
@[default_target]
lean_exe checkPostgresTransaction where
  root := `Test.PostgresTransaction

-- Check of lean-pq ownership. The parent process observes connections that remain before exit.
@[default_target]
lean_exe checkPostgresLifetime where
  root := `Test.PostgresLifetime

-- Check of failure paths in extracting SELECT results (injected Reader; no DB needed).
@[default_target]
lean_exe checkPostgresResult where
  root := `Test.PostgresResult

-- Check of matching write results against the model (no DB needed).
@[default_target]
lean_exe checkPostgresWrite where
  root := `Test.PostgresWrite

-- Check of taking a snapshot of all tables and of transaction failures (no DB needed).
@[default_target]
lean_exe checkPostgresLoad where
  root := `Test.PostgresLoad

-- Check of the table-creation DDL and of transaction failures (no DB needed).
@[default_target]
lean_exe checkPostgresInit where
  root := `Test.PostgresInit

-- Check of staged execution (point lookups) with an injected driver (no DB needed).
@[default_target]
lean_exe checkPostgresStaged where
  root := `Test.PostgresStaged

-- Real-DB integration check of extension-value, set and record columns (called by scripts/check-postgres-values.py
-- against local Supabase).
@[default_target]
lean_exe checkPostgresValues where
  root := `Test.PostgresValues
  needs := #[valuesSchema, valuesPolicies]

-- Real-DB integration check of external API calls (`sync`) against a mock HTTPS API (called by
-- scripts/check-external-calls.py, which sets up local Supabase and the mock API).
@[default_target]
lean_exe checkExternalCalls where
  root := `Test.ExternalCalls

-- Real-DB integration check of the outbox and internal loop for external API calls (`async`) (scripts/check-outbox.py
-- sets up local Supabase and the mock API and calls it in three forms: provision / enqueue / loop; loop uses 2
-- processes).
@[default_target]
lean_exe checkOutbox where
  root := `Test.Outbox

-- Check of Bearer extraction and of principal determination that fails closed to anonymous (no JWT service needed).
@[default_target]
lean_exe checkHttpAuth where
  root := `Test.HttpAuth

-- Server for the HTTP integration check of query strings, selected request headers and allowed response headers
-- (started and checked by scripts/check-http-headers.py; no DB or JWT needed).
@[default_target]
lean_exe serveHttpHeaders where
  root := `Test.HttpHeaders

-- Adoption check of the pinned OpenSSL/JOSE dependencies.
@[default_target]
lean_exe checkJwtDependency where
  root := `Test.JwtDependency

-- Check of JWKS fetching via curl (called by scripts/check-jwks-fetch.py over isolated TLS).
@[default_target]
lean_exe checkJwksFetch where
  root := `Test.JwksFetch
