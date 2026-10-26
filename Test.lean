import Test.Fixture
import Test.Smoke
import Test.Axioms
import Test.Schema
import Test.Policy
import Test.Cors
import Test.Http
import Test.PostgresValue
import Test.PostgresSql
import Test.PostgresShape
import Test.PostgresSnapshot
import Test.Materials
import Test.External
import Test.CallSend
import Test.Generated

/-!
# Test — nyxis の検査

`lake build` で実行される検査。失敗すればビルドが失敗する。

- `Test.Fixture` — コア専用の検査データ(手書きのスキーマ・ポリシー・DB の初期状態)。アプリのファイルは読まない。
- `Test.Smoke` — fixture によるランタイムの意味論の煙テスト(定理が空虚でないこと)。
- `Test.Axioms` — 主定理と接続層の補助定理が依存する公理の検査(未証明の穴や独自公理が無いこと)。
- `Test.Schema` — Cedar スキーマからの構成と検査(受け入れる文書と拒む文書)。
- `Test.Policy` — Cedar ポリシーからの構成(Cedar の解析器と同じ抽象構文になること、拒む文書)。
- `Test.Cors` — CORS 設定の解析と Origin の照合。
- `Test.Http` — HTTP の要約と応答の行: 要求ヘッダの選別(Authorization・Cookie は落ちる)、問い合わせ文字列の
  復号、応答の Content-Type の既定と妥当でない値の破棄。実 HTTP の統合検査は `serveHttpHeaders`
  (`Test/HttpHeaders.lean`)を `scripts/check-http-headers.py` が起動して行う。
- `Test.Materials` — 判定材料の限定(`Nyxis.Materials`、点検索の土台): 検査用正本からの型環境の構成、cedar-lean の
  level 検証、限定した材料での判定と全実体での判定の一致。末尾にサーバー生成値の検査: 正本が `context` に
  `now` / `id` を宣言したときだけ判定の文脈に現れ、判定がその値に依存し、偽った時刻・ID の提案が拒否されること。
- `Test.External` — 宣言された外部効果(添付の署名付き URL の発行。メール送信・サービス主体。外部 API 呼び出し): `upload` / `download` / `@attachment` / `mail` / `@external` / `call` の受理と拒否(`docs/external-calls.md` §3.4 の
  各変種を含む)、permit されたときだけの発行の記録と nyxis が決めるパス・宛先・URL・本文、結果の列の消費、部分的な取得との
  一致。
- `Test.CallSend` — 外部 API 呼び出しの接続層の純粋部分: 応答の寛容な復号、本文の JSON、curl の設定と出力の分解。
- `Test.Generated` — サーバー生成値の純粋部分(UUID の形)。実時計と乱数の `fresh` は `checkHttpAuth` が検査する。
- `Test.PostgresValue` / `PostgresSql` / `PostgresShape` / `PostgresSnapshot` — PostgreSQL 接続層の純粋部分。
  IO を伴う接続層の検査は `lakefile.lean` の `check*` 実行ファイル(`Test/Postgres*.lean`・`HttpAuth`・`JwksFetch`・`JwtDependency`)。
- `Test.PostgresStaged`(実行ファイル `checkPostgresStaged`)— 段階的な実行(`PostgresRun.runStaged`: 呼び出しごとの
  点検索)を fixture と注入ドライバで検査: 応答と最終状態がモデルと一致し、発行される SQL が主体・対象の行と
  その再生だけ(他のテーブルの全行は取らない)で、不整合・失敗では応答を公開せず ROLLBACK する。
- `Test.PostgresValues`(実行ファイル `checkPostgresValues`)— `values-fixture.cedarschema` / `.cedar` の
  `datetime` / `decimal` / `Set<…>` / レコードの列を実 PostgreSQL で挿入・読み取り・更新し、ポリシーの比較を確かめる
  統合検査(`scripts/check-postgres-values.py` がローカル Supabase で呼ぶ)。
- `Test.ExternalCalls`(実行ファイル `checkExternalCalls`)— `@external` の送り先と `call` を持つ検査用正本で、ローカルの
  模擬 HTTPS API に対する `sync` の呼び出しを実 PostgreSQL の段階的な経路で確かめる統合検査(deny で送信なし、
  `NYXIS_EXT_<名前>` の認証ヘッダ、余分なキーの破棄、欠落・型違いの固定 502 と取り消し、2xx 以外の受け渡し、輸送の
  失敗、鍵の非表示。`scripts/check-external-calls.py` がローカル Supabase と模擬 API を用意して呼ぶ)。
-/
