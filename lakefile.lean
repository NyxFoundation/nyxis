import Lake
open Lake DSL

-- lean-pq のパッケージ内のリンク引数は、これを require する側の実行ファイルには伝わらない。
-- 機械固有の導入先を埋め込まずに libpq を解決する。前提: pkg-config と libpq の開発ファイル
-- (brew install libpq / libpq-dev。Homebrew の keg-only な libpq は $(brew --prefix libpq)/lib/pkgconfig を PKG_CONFIG_PATH に)。
-- nyxis を require するアプリケーションのパッケージも、同じ定義を自分の lakefile に持つ必要がある。
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

package nyxis where
  version := v!"0.1.7"
  moreLinkArgs := postgresLinkArgs ++ cryptoShimLinkArgs __dir__

require Cedar from git "https://github.com/cedar-policy/cedar-spec" @
  "6d7fb269d5eec6ce4ae1d4aff9794feba0c0d5a9" / "cedar-lean"
-- 承認済みの固定依存(lean-pq と JWT 用の lean-jose/jose-libcrypto/lean-libcrypto とその推移依存)。
-- git を使わず SHA256 で固定したアーカイブから python3 scripts/prepare-dependencies.py が .lake/vendor/ に置く。
require leanPq from ".lake/vendor/lean-pq"
require «jose-libcrypto» from ".lake/vendor/jose-libcrypto"

@[default_target]
lean_lib Nyxis

-- Test/Policy.lean がビルド時に埋め込むポリシーの fixture。変更したら Test を再ビルドする。
input_file testPolicies where
  path := "Test/policies-fixture.cedar"
  text := true

-- Test/PostgresValues.lean がビルド時に埋め込む検査用スキーマとポリシー。
input_file valuesSchema where
  path := "Test/values-fixture.cedarschema"
  text := true

input_file valuesPolicies where
  path := "Test/values-fixture.cedar"
  text := true

@[default_target]
lean_lib Test where
  needs := #[testPolicies, valuesSchema, valuesPolicies]

-- lean-pq の import とネイティブリンクの煙テスト(DB も資格情報も不要)。
@[default_target]
lean_exe checkPostgresDependency where
  root := `Test.PostgresDependency

-- トランザクションの失敗経路の検査(注入ドライバ。DB 不要)。
@[default_target]
lean_exe checkPostgresTransaction where
  root := `Test.PostgresTransaction

-- lean-pq の所有権の検査。親プロセスが終了前の残存接続を観測する。
@[default_target]
lean_exe checkPostgresLifetime where
  root := `Test.PostgresLifetime

-- SELECT 結果の抽出の失敗経路の検査(注入 Reader。DB 不要)。
@[default_target]
lean_exe checkPostgresResult where
  root := `Test.PostgresResult

-- 書き込み結果とモデルの照合の検査(DB 不要)。
@[default_target]
lean_exe checkPostgresWrite where
  root := `Test.PostgresWrite

-- 全テーブルのスナップショット取得とトランザクション失敗の検査(DB 不要)。
@[default_target]
lean_exe checkPostgresLoad where
  root := `Test.PostgresLoad

-- テーブル構築の DDL とトランザクション失敗の検査(DB 不要)。
@[default_target]
lean_exe checkPostgresInit where
  root := `Test.PostgresInit

-- 段階的な実行(点検索)の注入ドライバによる検査(DB 不要)。
@[default_target]
lean_exe checkPostgresStaged where
  root := `Test.PostgresStaged

-- 拡張値・集合・レコードの列の実 DB 統合検査(scripts/check-postgres-values.py がローカル Supabase で呼ぶ)。
@[default_target]
lean_exe checkPostgresValues where
  root := `Test.PostgresValues
  needs := #[valuesSchema, valuesPolicies]

-- 外部 API 呼び出し(`sync`)の模擬 HTTPS API に対する実 DB 統合検査(scripts/check-external-calls.py が
-- ローカル Supabase と模擬 API を用意して呼ぶ)。
@[default_target]
lean_exe checkExternalCalls where
  root := `Test.ExternalCalls

-- 外部 API 呼び出し(`async`)のアウトボックスと内部ループの実 DB 統合検査(scripts/check-outbox.py が
-- ローカル Supabase と模擬 API を用意し、provision / enqueue / loop の 3 つの形で呼ぶ。loop は 2 プロセス)。
@[default_target]
lean_exe checkOutbox where
  root := `Test.Outbox

-- Bearer の抽出と、失敗を匿名へ閉じる主体の決定の検査(JWT のサービス不要)。
@[default_target]
lean_exe checkHttpAuth where
  root := `Test.HttpAuth

-- 問い合わせ文字列・選別した要求ヘッダ・許可された応答ヘッダの HTTP 統合検査用サーバ
-- (scripts/check-http-headers.py が起動して検査する。DB・JWT 不要)。
@[default_target]
lean_exe serveHttpHeaders where
  root := `Test.HttpHeaders

-- 固定した OpenSSL/JOSE 依存の採用検査。
@[default_target]
lean_exe checkJwtDependency where
  root := `Test.JwtDependency

-- curl による JWKS 取得の検査(scripts/check-jwks-fetch.py が隔離 TLS で呼ぶ)。
@[default_target]
lean_exe checkJwksFetch where
  root := `Test.JwksFetch
