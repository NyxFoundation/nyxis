# ローカル Supabase

`scripts/local-supabase.py` はローカル Supabase を起動・確認するスクリプトです。macOS の Docker Desktop、
Docker CLI、Supabase CLI、Python 3 が必要です（確認環境: Supabase CLI 2.90.0）。

```sh
python3 scripts/local-supabase.py
```

Docker Desktop が停止していれば起動し、最大 120 秒待ちます。
ローカル専用 `desktop-linux` コンテキストの Unix ソケットを使い、
呼出し元の `DOCKER_HOST` や別コンテキストを使いません。
`supabase start` は既存コンテナ・ボリュームを再利用します。
初回はイメージを取得するため時間がかかります。全体の内部期限は 540 秒です。
タイムアウト後もデータを削除せず、再実行できます。

ポートは他プロジェクトとの競合を避け、API 55321 / DB 55322 / メール 55324(Mailpit の HTTP API。SMTP は 55326 — メール送信の統合テストで team-docs のサンプルが通知のメールを送る先)を使います。

設定は `supabase init --yes` で生成した `supabase/config.toml` を管理します。
スクリプトは init を実行せず、作業木を変更しません。
生成物 `.temp` / `.branches` は Supabase の `.gitignore` で除外しています。
設定紛失・依存欠落・起動失敗・疎通失敗は exit 75 で終わります。
CLI 出力には接続情報や鍵が含まれるため、成功・失敗とも生出力をログに出しません。
失敗時は表示されたコマンドをローカル端末で確認してください。

検証は PostgreSQL の `SELECT 1`、Auth の health と JWKS の HTTP 200 です。
アプリのテーブル作成・seed・reset・データ削除は行いません。
自動 seed と不要な Studio/Realtime/Edge/Analytics は無効です。
API の公開 schema は空にしてあり、Auth・メール捕捉・Storage(添付の統合テスト用)は有効です。
本番の認証設定が正しいことを証明するものではありません。

## 検証コマンドへの接続情報の受け渡し

スクリプトから呼び出し元のシェルへ export は伝播しません。
次の形式で、実行時に取得した接続情報を子プロセスの環境だけに渡します。

```sh
python3 scripts/local-supabase.py --exec python3 scripts/run-sample-frontend-backend.py --oauth
```

`--exec` は起動を行わず、ローカル status を読み取って指定コマンドを実行します。
`sample` 自体は `NYXIS_SUPABASE_ISSUER` も必須とするので、直接 `--exec` で起動するなら呼び出し側がそれを与えます
(上の起動スクリプトは隔離 DB・JWKS 中継・issuer をまとめて用意します)。
`NYXIS_DATABASE_URL`、`NYXIS_SUPABASE_URL`、取得できた場合は
`NYXIS_SUPABASE_ANON_KEY` / `NYXIS_SUPABASE_SERVICE_ROLE_KEY` を渡します。
接続文字列・鍵のファイル保存や shell の eval は行いません。
DB URL は localhost の 55322 番・postgres DB のみ受け入れます。
検証コマンド自身も環境変数をログに出さないでください。
この URL はローカル検証用 postgres 接続で、本番の専用ロール設定ではありません。

サンドボックスの中から実行する場合、Docker ソケットと localhost への通信の許可が別に必要です。
このスクリプトはサンドボックス設定を変更しません。

## スクリプトの回帰検査

```sh
python3 scripts/check-local-supabase.py
```

実機ではスクリプトを 2 回実行し、両方の exit 0 と前後の
`git status --porcelain` の一致を確認します。停止は必要なときだけ手動で
`supabase stop` を使い、`--no-backup` や `db reset` は使いません。

## 実DBの匿名HTTP検査

```sh
lake build
lake build --dir examples/bulletin-board/backend
python3 scripts/local-supabase.py --exec python3 scripts/check-local-postgres-http.py
```

ローカル専用の一意名のDBを作成し、`initSampleDatabase` でテーブルを構築して
検査用の行を投入します。`sample` の実HTTP経路で公開投稿の読取り、下書きと
書込みの拒否、拒否後のDB行不変、別SQL接続の更新が次のHTTPへ反映されることを
検査します。終了時は子サーバを停止し、この実行で新規作成したDBだけを削除します。
既存のアプリDBとAuthデータは変更しません。パスワードや接続情報は表示しません。
検査用ポートは18116 (`NYXIS_LOCAL_HTTP_PORT` で変更可能)、JWKS 取得の検査(`check-sample-jwks.py`)は18117
(`NYXIS_SAMPLE_JWKS_PORT`)です。

匿名経路だけの検査であり、認証済み主体の検査は下記の 3 節が担います。

## テスト用ES256 JWTと実DBの4主体検査(依存導入の検査)

```sh
lake build
lake build --dir examples/bulletin-board/backend
python3 scripts/local-supabase.py --exec sh scripts/check-jwt-dependency.sh --local-postgres
```

既存のJWT依存検査に加え、一意名の専用DBとテスト専用サーバを使い、匿名・作者・
第三者・管理者の公開投稿／下書きの読取り・編集・削除・公開／非公開、作成、管理者権限の
付与／剥奪をHTTPで検査します。各操作後の全User/Post行を独立したSQL接続から照合し、
拒否時の不変と許可時の効果を確認します。権限の付与・剥奪が次のHTTPへ反映されることと、
不正署名・期限切れ・発行者違いのJWTによる下書きの読取り／編集拒否も検査します。
既存の匿名検査と同じローカルURL・Docker・ポート検査と専用DBの後始末を使います。

鍵とJWTは一時領域のOpenSSL／承認済みLeanバインディングによるテスト用であり、
Supabase Authが発行したJWTではありません。検査用サーバの固定時計・JWKSは本番には
接続しません。これは依存とコアの検証器の検査で、本体経路の証拠は下記「サンプル本体とAuth発行JWTの統合検査」です。

## Supabase Auth発行JWTと実DBの4主体検査

```sh
lake build
lake build --dir examples/bulletin-board/backend
python3 scripts/local-supabase.py --exec sh scripts/check-jwt-dependency.sh --local-auth
```

従来のJWT・実DB検査も実行した後、ローカルAuthに一意なメールアドレスの検査ユーザー3人を
作成します。管理APIで生成したマジックリンクのハッシュを `/verify` に渡し、パスワードを
使わずAuth発行JWTを取得します。[SupabaseのマジックリンクAPI](https://supabase.com/docs/reference/javascript/auth-admin-generatelink)に従った検査用セッション取得です。
Authの `/user` でも各JWTの主体を確認します。

公開JWKSを取得し、承認済みOpenSSL検証器にES256限定・正しい発行者・authenticated audience・
実時計の検証を任せます。実ユーザーIDを専用DBの検査行に使い、4主体のHTTPと全行照合で
許可・拒否・永続化と、権限変更が次のリクエストへ反映されることを確認します。
管理者属性はアプリDBの行で決まり、Authのservice_role資格情報はアプリのHTTPへ送りません。

AuthのURLは `http://127.0.0.1:55321` のみ受け入れます。ユーザーとDBはこの実行で新規作成した
ものだけを終了時に削除し、削除したユーザーのGETが404であることも確認します。
JWT・OTPハッシュ・鍵・接続情報はファイル保存やログ出力せず、公開JWKSファイルだけ一時作成します。

この検査は検査専用サーバを使います。本体経路の検査は次節です。

## サンプル本体とAuth発行JWTの統合検査

```sh
lake build
lake build --dir examples/bulletin-board/backend
python3 scripts/local-supabase.py --exec python3 scripts/check-sample-jwt-db.py --local-auth
python3 scripts/local-supabase.py --exec python3 scripts/check-sample-jwt-db.py
```

最初のコマンドは実際のsampleでAuth発行マジックリンクJWTを検証します。
匿名・作者・第三者・管理者のHTTPと永続行を照合します。
ローカルAuthの`auth.jwt_issuer`は`https://localhost:55325/auth/v1`です。
[CLI 2.90.0の設定定義](https://github.com/supabase/cli/blob/v2.90.0/pkg/config/auth.go)にある設定を使います。
既にローカルSupabaseが起動中の状態でこの設定を変更した場合、`supabase stop`の後、
`python3 scripts/local-supabase.py` で再起動すると反映されます。データのresetは不要です。

検査中だけ55325番に一時TLSサーバを立て、固定のローカルAuth公開JWKSを毎要求取得して
中継します。sampleのHTTPS・証明書・ホスト・issuer・署名検証を維持します。
検査用CAは子プロセスの環境だけへ渡し、アプリやHTTPへ検査用設定は公開しません。
Authの管理資格情報やJWTをJWKS取得先へ送信しません。
作った3ユーザーと専用DBだけを終了時に削除し、JWT/OTP/資格情報は保存しません。

引数なしの2番目の検査は承認済みES256 fixtureでHTTPと永続行を検査し、
有効なJWTの成功と、不正署名・期限切れ・別issuerの匿名化/下書き読取り・編集拒否を確認します。
両モードとも同じsampleプロセスでJWKS失敗4種と復旧、DB障害8件とrollback/復旧、
接続上限100を超える101回の認証済み読取りと生存中の残存接続0を検査します。
この2検査がサンプル本体の経路の検査です。クラウド設定やLinux上のTLS検証を代用しません。

## 判定材料の取得範囲の検査(10万行規模)

```sh
lake build
lake build --dir examples/bulletin-board/backend
python3 scripts/local-supabase.py --exec python3 scripts/check-materials-scale.py
```

実際のsample(段階的な経路)を専用DBに対して起動し、承認済みfixtureのES256 JWT(一時TLSのJWKS中継)で
匿名・作者・第三者・管理者の同じ要求列(読取り・編集・公開切替・作成/削除・権限付与/剥奪・利用者読取り・一覧)を
3つの状態で送ります: 固定データだけ、Userに10万行を足した後、Postにも10万行を足した後(一覧はPostが対象なので
最後の状態では送りません)。要求ごとにsampleの接続が閉じるのを待ってから`pg_stat_user_tables`と
`pg_stat_user_indexes`の差分で各テーブルから読んだ行数を取り、10万行のテーブルについては空の状態と同じ
(索引の点検索ぶんの余裕2行まで)、一覧以外は合計16行以内、応答時間の中央値(12回)が空の状態の2倍以内で
あることを検査します。最後に自分のSELECTで10万行の全走査が同じ統計ビューに現れることを確かめます。
専用DBだけを終了時に削除し、資格情報は出力しません。

## 実Supabaseの接続情報を読み込む

プロジェクトルートの `.env` に次の2変数を置きます（Git無視対象）。

```dotenv
NYXIS_SUPABASE_URL=https://PROJECT_REF.supabase.co
NYXIS_SUPABASE_ANON_KEY=YOUR_ANON_KEY
```

スクリプトは実行のたびに `.env` を読み、2変数の存在とURL形式を確認します。
接続やAuth設定が正しいことの検証は別途必要です。値はログへ出しません。
`.env` の値は同名の親環境変数より優先し、未指定の値は親環境から補います。
引用符、行頭の `export`、コメントに対応しますが、変数展開・コマンド置換・
複数行の値には対応しません。読み込むのは上記2変数だけです。

スクリプトは別プロセスなので、呼び出し元の環境は変更できません。
実クラウドの検証コマンドは、次の形式で実行してください。

```sh
python3 scripts/local-supabase.py --exec-cloud COMMAND ARG ...
```

この実行時にも `.env` を読み直し、子プロセスの環境へ値を渡します。
DockerやローカルSupabaseの起動は不要です。既存の `--exec` は引き続き
ローカル接続情報のみを渡し、`.env` のクラウド情報を使いません。
