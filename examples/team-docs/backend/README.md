# team-docs バックエンド

このパッケージは `require nyxis from "../../.."` でリポジトリ直下のコアを利用する。
コアの Lean ソースのコピーは持たない。実行ファイルと検査はこのパッケージでビルドする。

リポジトリ直下で依存とコアを準備する。

```sh
python3 scripts/prepare-dependencies.py
lake build
```

続いてこのディレクトリで実行する。

```sh
lake build
```

`lake-manifest.json` はコアで準備済みの Cedar・batteries・JWT・PostgreSQL 依存を
相対パスで参照する。リビジョンはコアの固定情報に従い、別のコピーを取得しない。

承認する正本は `schema.cedarschema` と `policies.cedar`。
`TeamDocs/Approved.lean` が `nyxis_approved` で宣言し、`TeamDocs/Server.lean` は
その宣言から組む App をコアの起動 API へ渡す。
`TeamDocs.lean` の末尾でアプリ全体を監査し、`Main.lean` がその後に起動処理を行う。
`TeamDocsTest/` はこのアプリだけのモデル検査を持つ。

ビルド成果物はこのディレクトリの `.lake/build/bin/` にある。
`teamDocs` は `NYXIS_DATABASE_URL`・`NYXIS_SUPABASE_ISSUER` を必須とし、
ブラウザ向けには `NYXIS_CORS_ORIGINS` も指定する。`initTeamDocsDatabase` は新規テーブルの明示的な準備専用である。
ローカル Supabase 上の統合テストは [公式サンプルの README](../README.md) を参照する。
