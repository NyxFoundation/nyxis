# Nyxis

[English](README.md) | 日本語

[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Version](https://img.shields.io/badge/version-v0.1.6-orange.svg)](https://github.com/NyxFoundation/nyxis)
[![Status](https://img.shields.io/badge/status-under%20development-yellow.svg)](ASSUMPTIONS.ja.md)
[![Lean](https://img.shields.io/badge/Lean-v4.34.1-0052cc.svg?logo=lean&logoColor=white)](lean-toolchain)
[![Cedar](https://img.shields.io/badge/policies-Cedar-6f42c1.svg)](https://www.cedarpolicy.com/)
[![Formally verified](https://img.shields.io/badge/authorization-formally%20verified-brightgreen.svg)](ASSUMPTIONS.ja.md)
[![PostgreSQL](https://img.shields.io/badge/PostgreSQL-Supabase-4169E1.svg?logo=postgresql&logoColor=white)](https://supabase.com/)
[![Supabase Auth](https://img.shields.io/badge/auth-Supabase%20Auth-3ECF8E.svg?logo=supabase&logoColor=white)](https://supabase.com/auth)
[![GitHub stars](https://img.shields.io/github/stars/NyxFoundation/nyxis?style=social)](https://github.com/NyxFoundation/nyxis)

**認可安全性が形式証明で保証された、Lean 製のバックエンドフレームワーク。**

Nyxis は、AI エージェントにコードを書かせて Web アプリケーションを出す個人開発者が、認可について安心してリリースできるようにするためのフレームワークです。開発者が書いて承認するのは [Cedar](https://www.cedarpolicy.com/) のスキーマとポリシーだけです。ハンドラは Claude Code などに普通に書かせればよく、開発者が Lean を書く必要はありません。

構築されたバックエンドには、次の形式証明が付きます。

> どのような HTTP リクエスト列が送られても、認証された主体の正当な権限を超えるデータの読み取り・変更・削除・権限付与は発生しない。

この性質は `lake build` のたびに Lean のカーネルが検査します。認可のレビューと監査は、スキーマとポリシーを読み、証明が通っていることを確かめれば済みます。

> [!NOTE]
> Nyxis は開発中(v0.1.6)です。保証が届く範囲と、証明の外側で信頼する仮定は [ASSUMPTIONS.ja.md](ASSUMPTIONS.ja.md) に明記しています。本番で使う前に必ず読んでください。

## 仕組み

1. **Cedar のスキーマとポリシーを書いて承認する。** スキーマはテーブル定義を兼ね(エンティティ型 = テーブル、属性 = 列)、各アクションには Nyxis が定める効果を 1 つ添えます。
2. **ハンドラを書く(AI エージェントに書かせる)。** ハンドラは Nyxis の型 `Nyxis.Handler` で書き、持てる効果は認可層へのアクション呼び出しだけです。IO や DB への直接の到達はできません。
3. **`lake build` を通す。** ビルドと同時に、承認した正本への結び付け、アプリケーションのコードの監査、証明の検査が行われます。
4. **任意のクライアントから呼ぶ。** クライアントは Supabase Auth の JWT を付けて HTTP で呼びます。フロントエンドは Nyxis の外にある普通の HTTP クライアントです。

スキーマの例(公式サンプルの掲示板より):

```cedar
entity User = { "admin": Bool };
entity Post = { "author": User, "title": String, "body": String, "published": Bool };

@effect("update Post(title, body)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
```

ポリシーの例:

```cedar
// 投稿の編集・公開・削除は作者と管理者だけができる。
@id("manage-post")
permit (
  principal is User,
  action in [Action::"editPost", Action::"publishPost", Action::"deletePost"],
  resource is Post
) when { resource.author == principal || principal.admin };
```

効果の種類は `read`・`list`・`insert`・`update`(列を列挙)・`delete` に加えて、署名付き URL によるファイル保管、メール通知、外部 API 呼び出しなどがあり、いずれも認可層を通って同じ定理の対象になります。主体は JWT から、対象は DB の現在の行から、現在時刻や一意 ID は要求ごとに Nyxis が決めるため、ハンドラはこれらを偽れません。

## 必要なもの

- [elan](https://github.com/leanprover/elan) 経由の Lean 4(版は `lean-toolchain` で固定)
- Python 3.12 以降、OpenSSL CLI、C コンパイラ
- pkg-config と、libpq・libcrypto の開発用ファイル(macOS なら `brew install libpq`。keg-only の libpq は `$(brew --prefix libpq)/lib/pkgconfig` を `PKG_CONFIG_PATH` に加える)
- 実行時: PostgreSQL(Supabase)と Supabase Auth

## ビルド

```sh
python3 scripts/prepare-dependencies.py   # 固定した依存を SHA256 で照合して .lake/vendor/ に置く
lake build                                # コア・証明・テストのビルドと検査
```

依存の準備の詳細は [docs/dependencies.md](docs/dependencies.md)、ローカル Supabase の準備は [docs/local-supabase.md](docs/local-supabase.md) にあります。

## アプリケーションで使う

Nyxis は Lake の `require` で取り込む独立したパッケージです。アプリケーションのパッケージはスキーマ・ポリシー・ハンドラ・起動だけを持ち、Nyxis のコードを持ちません。Nyxis は固定した依存を自分のチェックアウト内の `.lake/vendor/` から解決するので、先にこのリポジトリを clone して上の「ビルド」を済ませ、公式サンプルと同じくパスで require します。

```lean
require nyxis from "<clone した Nyxis へのパス>"
```

リンク引数は require する側に伝わらないため、ルートの `lakefile.lean` にある `postgresLinkArgs` と `cryptoShimLinkArgs` と同じ定義をアプリケーションの `lakefile.lean` にも置き、`moreLinkArgs := postgresLinkArgs ++ cryptoShimLinkArgs <Nyxis のクローンへのパス>` としてください(Linux では libpq をフルパスでリンクし、lean-libcrypto の `libcrypto_shim.so` の場所を実行ファイルに埋め込むため、ビルドした実行ファイルをそのまま起動できます)。承認する正本は `nyxis_approved` で宣言し、全モジュールを import した最終モジュールの末尾に `nyxis_check_app` を置きます。具体的な形は公式サンプルを参照してください。

## 公式サンプル

- [`examples/bulletin-board/`](examples/bulletin-board/README.md) — 掲示板。投稿の公開と下書き、Google OAuth でのログイン、管理者権限の付与と剥奪。Next.js のフロントエンドが付き、画面を操作しながらポリシーどおりの許可と拒否を体験できます。
- [`examples/team-docs/`](examples/team-docs/README.md) — 組織内での文書共有。所属と役割、日時、一覧の絞り込みとページング、添付ファイル、メール通知、外部 API 呼び出し。現在はバックエンドのみ。

## リポジトリの構成

| パス | 内容 |
|---|---|
| `Nyxis/` | コア(Cedar の解析、認可層、ランタイム、接続コード)と証明。主定理は `Nyxis.Runtime.authorization_safety` |
| `Test/` | コアのテスト。`Test/Axioms.lean` が全定理の公理を検査する |
| `scripts/` | 依存の準備と統合検査のスクリプト |
| `examples/` | 公式サンプル |
| `docs/` | 証明の目録、接続コードの責務、設計文書 |
| `supabase/` | ローカル Supabase の設定 |

## 文書

- [ASSUMPTIONS.ja.md](ASSUMPTIONS.ja.md) — 保証の範囲と、証明の外側で信頼する仮定
- [docs/proofs.md](docs/proofs.md) — 証明している定理と、それぞれが述べないことの目録
- [docs/connection.md](docs/connection.md) — 仮定を支える接続コードの作り
- [CONTRIBUTING.md](CONTRIBUTING.md) — PR の取り込みの流れ、DCO の sign-off、CI が検査すること(英語)

## ライセンス

[MIT License](LICENSE) © 2026 Nyx Foundation
