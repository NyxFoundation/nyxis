# Nyxis 公式サンプル — 掲示板

`backend/` は nyxis を Lake の依存として利用する独立パッケージ、`frontend/` は Next.js App Router の通常の HTTP クライアント。投稿の一覧・詳細・作成・編集・公開切替・削除、Google OAuth のログインとログアウト、利用者の自己登録と管理者権限の付与・剥奪を試せる。アプリのデータは nyxis の HTTP API だけを通じて扱う。フロントエンドは形式証明の対象ではなく、認可はバックエンドが行う。

## ビルド

Node.js 22 以上と npm を使う。リポジトリ直下から順番に実行する。バックエンドや Supabase の起動、資格情報は不要。依存と `next/font` の Google Fonts (Zen Kaku Gothic New / DM Mono) の取得にはネット接続が必要。フォントは成果物に含め、実行時は自己ホストする。

```sh
cd examples/bulletin-board/frontend
npm ci --cache /tmp/nyxis-frontend-npm --no-audit --no-fund
NEXT_TELEMETRY_DISABLED=1 npm run build
npm run typecheck
```

依存は `package-lock.json` で固定。`next build --webpack` で `.next/` に出力する。以下の起動準備は別ターミナルで、リポジトリ直下から行う。

## ローカル Supabase と Google OAuth の設定

macOS の Docker Desktop・Docker CLI・Supabase CLI 2.90.0・Python 3.12 以降・OpenSSL CLI と、このリポジトリの Lean/Lake・pkg-config・libpq 開発環境が必要。ローカルのポート 55321 (Auth)、55322 (DB)、55325 (JWKS TLS 中継)、8080 (sample)、3000 (画面) を使う。Supabase の準備の詳細は [ローカル Supabase の準備](../../docs/local-supabase.md) にある。

人間が用意した Google OAuth クライアントの値を、リポジトリ直下の Git 除外された `.env` に設定する。既存の `.env` があれば他の値を残して追記する。Google のクライアント secret はサーバー専用で、`NEXT_PUBLIC_` 変数には設定しない。

```dotenv
SUPABASE_AUTH_EXTERNAL_GOOGLE_CLIENT_ID=用意したclient_id
SUPABASE_AUTH_EXTERNAL_GOOGLE_SECRET=用意したclient_secret
```

Google 側の承認済みリダイレクト URI に `http://127.0.0.1:55321/auth/v1/callback` を登録する。テストモードのクライアントなら、ログインする Google アカウントをテストユーザーに追加する。`supabase/config.toml` には Google 有効化、上記2変数の `env()` 参照、明示的な Google callback と、画面の戻り先 `http://127.0.0.1:3000/auth/callback` / `http://localhost:3000/auth/callback` が設定済み。JWT issuer は `https://localhost:55325/auth/v1`(sample は HTTPS の issuer しか受け付けないため、ローカル Auth の公開鍵を起動スクリプトが TLS で中継する)。以下ではホスト表記を `127.0.0.1` に揃える。

```sh
python3 scripts/local-supabase.py
lake build
lake build --dir examples/bulletin-board/backend
```

依存を未取得なら `lake build` の前に `python3 scripts/prepare-dependencies.py` を実行する。Auth が起動済みのまま OAuth 設定や `.env` を変更した場合は `supabase stop` 後に `python3 scripts/local-supabase.py` を再実行して反映する。DB の reset は不要。

## 認証済み操作ができるバックエンドを起動する

上の準備後、リポジトリ直下から実行する。

```sh
python3 scripts/local-supabase.py --exec python3 scripts/run-sample-frontend-backend.py --oauth
```

`Ready: http://127.0.0.1:8080` と `OAuth ready` が出たら、この端末を開いたまま次節へ進む。`NYXIS_LOCAL_HTTP_PORT` を指定した場合は API URL も合わせる。

このコマンドはローカル DB URL (55322 番の postgres DB) とローカル Docker context を検査し、一意名の新しい隔離 DB にだけ `initSampleDatabase` でテーブルを作る。既存 DB は初期化しない。公開投稿 `pub1` (題名 `public`、本文 `public body`、作者 `alice`) と下書き `draft1` を用意し、匿名で一覧に `pub1` だけが現れること、公開詳細 200・下書き詳細 403 を起動時に検査する。

ローカル Auth の公開 JWKS だけを `https://localhost:55325/auth/v1/.well-known/jwks.json` で中継する。一時証明書の CA は sample 子プロセスだけに渡し、OS やブラウザの信頼設定は変更しない。バックエンドの JWT の署名・issuer・期限検証を維持する。中継は毎回固定のローカル Auth から公開鍵を取得し、JWT や管理キーを転送しない。

## フロントエンドを起動する

別ターミナルのリポジトリ直下で次を実行する。フックがローカル Supabase の公開値を読み、以下の `env -i` で開発プロセスへ渡す変数を限定する。管理キーや DB 接続文字列を手でコピーする必要はない。OAuth callback の認可コードを端末へ残さないため、開発サーバーの出力を破棄する。

```sh
python3 scripts/local-supabase.py --exec sh -c '
  cd examples/bulletin-board/frontend || exit 1
  exec env -i PATH="$PATH" HOME="$HOME" \
    NEXT_PUBLIC_NYXIS_API_URL=http://127.0.0.1:8080 \
    NEXT_PUBLIC_SUPABASE_URL="$NYXIS_SUPABASE_URL" \
    NEXT_PUBLIC_SUPABASE_ANON_KEY="$NYXIS_SUPABASE_ANON_KEY" \
    NEXT_TELEMETRY_DISABLED=1 npm run dev >/dev/null 2>&1
'
```

`http://127.0.0.1:3000` を開く。初回のコンパイルには少し時間がかかる。バックエンドの CORS 許可は起動スクリプトが `http://127.0.0.1:3000,http://localhost:3000` に設定する。

| 設定 | 内容 |
|---|---|
| `NEXT_PUBLIC_NYXIS_API_URL` | 公開してよい nyxis API URL。省略時は `http://127.0.0.1:8080` |
| `NEXT_PUBLIC_SUPABASE_URL` | 公開 Auth URL。ローカルは `http://127.0.0.1:55321` |
| `NEXT_PUBLIC_SUPABASE_ANON_KEY` | ローカル Supabase の公開 anon キー。service_role キーは使わない |
| `NYXIS_DATABASE_URL` | バックエンド専用。フックから受け取り、起動スクリプトが子の中で隔離 DB へ切り替える |
| `NYXIS_SUPABASE_ISSUER` | バックエンド専用。起動スクリプトが `https://localhost:55325/auth/v1` に設定する |
| `NYXIS_CORS_ORIGINS` | バックエンド専用。上記の2つの画面 origin を起動スクリプトが設定する |

`NEXT_PUBLIC_` の値はブラウザへ公開される。Google secret・service_role キー・Supabase のアクセストークン・DB 接続情報を設定しない。公開値はビルド時に埋め込まれるため、接続先を変えたら再ビルドする。ビルド済みの実行はフロントエンドのディレクトリで `NEXT_TELEMETRY_DISABLED=1 npm start`。OAuth を使うビルドでは、上の3つの公開値を `npm run build` にも渡す。

## 匿名表示とログイン・ログアウトを試す

1. ログイン前のホームで `public` だけが一覧にあることを確かめ、開いて `public body` と作者 `alice` を見る。`draft1` は一覧に現れず、`http://127.0.0.1:3000/posts/draft1` を直接開くと「見られません」となる。この fixture の ID は UUID ではないため、「IDで開く」欄ではなく直接 URL を使う。
2. 右上のログインから「Googleでログイン」を押す。同じタブに戻るとコードを交換し、nyxis の `POST /users/{自分}` で `admin=false` の自己登録を行う。201/409 で続行する。接続失敗時はバックエンドと中継が起動しているか確認して再試行する。
3. メニューの「投稿」から題名と本文を入力し、「下書き」で保存する。遷移先の詳細 URL を控え、本文・下書きタグ・ログイン中の表示を確かめる。投稿の作者は JWT からバックエンドが決める。
4. 詳細画面でログアウトする。同じ詳細 URL で本文が消え、「見られません」とゲストの表示になることを確かめる。再び Google でログインすると本人の下書きが読める。

Auth は PKCE を使う。乱数と SHA-256 はブラウザ標準 Web Crypto に委ねる。JWT/更新トークンは同じタブの `sessionStorage` に保持し、復帰時と期限前に更新する。ログアウト時は私的な表示とローカルセッションを消し、匿名で再取得する。Auth の現在セッションも破棄し、Auth に届かない場合はその旨を表示する。`/login?next=/posts/<投稿ID>` で戻り先を指定でき、外部 URL は受け付けない。

## 最初の管理者を用意する

Google ログインと自己登録が成功したら、右上の人物マークから `/me` (「あなた」) を開き、自分の ID をコピーする。バックエンドを起動した端末に次の1行を入力して Enter を押す。`UUID` はコピーした値に置き換える。

```text
admin UUID
```

`First admin ready in this demo DB` が出たら `/me` を再読込みする。管理者の表示とメニューの「管理」が現れる。登録済みの UUID 形式の利用者だけを対象にし、この端末の初期管理者設定は1回だけ。未登録や形式の誤りは `No change` になる。起動端末からのこの準備は使い捨てのローカル隔離 DB に限り、Auth の利用者・設定や他の DB を変更しない。

以後の管理者の付与・剥奪は画面の `/admin` で利用者 ID を調べて行う。バックエンドが現在の管理者権限を判定する。自分の権限を外す場合は画面内で確認する。ログインしても管理者とは限らず、一般利用者が同じ操作を送ると拒否される。

## 終了と匿名表示だけの起動

フロントエンドとバックエンドの各端末で Ctrl-C を押す。バックエンドは sample と JWKS 中継を停止し、自分が作った隔離 DB と一時 TLS 素材だけを削除する。作った投稿・利用者行・初期管理者の設定もこの DB とともに消える。Supabase Auth の Google 利用者は通常のログインで登録され、そのまま残る。Supabase 自体も残る。強制終了や端末異常時は後片付けできない場合がある。

匿名表示だけなら、バックエンドの `--oauth` を省略できる。その場合は JWKS 中継と初期管理者入力を有効にせず、終了時に DB 行の不変も検査する。フロントエンドは `cd examples/bulletin-board/frontend` の後、`NEXT_PUBLIC_NYXIS_API_URL=http://127.0.0.1:8080 NEXT_TELEMETRY_DISABLED=1 npm run dev` で起動できる。

## デザインと検査

`frontend/design/` と `frontend/mockups/` は人間提供の正本。760px の本文幅、紙と罫、朱の印、黒い接続エラー帯を実装した。S1〜S9 に `data-screen`、状態に `data-state` を付ける。認可拒否は「見られません」/「できません」、接続失敗は「つながりません」、利用者行の未発見は「見つかりません」と区別する。

認証プロトコルの単体検査はフロントエンドのディレクトリで `node --test tests/auth.test.cjs`。実 OAuth/実 DB/画面観測の代わりにはしない。
