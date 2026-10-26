# 公式サンプル 2: team-docs

組織(ワークスペース)に複数の利用者が owner / editor / viewer として属し、文書を組織内で共有し、個別の利用者にも
共有できるアプリ。文書は作成日時と更新日時を持ち、その値は nyxis が要求ごとに決める現在時刻である。
1 つめのサンプル(`../bulletin-board/`)と同じく、nyxis を Lake の依存として取り込む別パッケージの
バックエンド(`backend/`)と、Next.js のフロントエンド(`frontend/`。人間がデザインを提供した後に作る)から成る。

いまあるのはバックエンドだけである。一覧の絞り込み・並べ替え・ページング(`GET /docs?org=&title=&since=&before=&sort=&dir=&limit=&offset=`。
応答は `{"rows": [...], "total": n}`)、添付ファイル(`POST /docs/{id}/attachment` で署名付き
アップロード URL、`GET /docs/{id}/attachment` で署名付きダウンロード URL を発行する。ファイルはクライアントが Supabase
Storage と直接やりとりし、nyxis を通らない)、更新の通知(文書を読める利用者が `POST /docs/{id}/subscriptions`
で宛先のメールアドレスを添えて購読し、`PUT /docs/{id}/shared` で共有されると購読者ごとに通知の行ができて、ポリシーが許す
購読者 — いま文書を読める購読者 — にだけメールが送られる。送れなかった通知は定期処理がサービス主体として後で送る)、外部 API 呼び出し(正本に `@external` で宣言した送り先 `Summarizer` / `Audit` への宣言された効果
`call`。`POST /docs/{id}/summary` は `sync`: nyxis が文書の題名と本文を要約 API に送り、応答 `{summary}` をハンドラが
別のアクション `recordSummary` で列 `summary` に記録する — 応答の値は通常の判定を通ってはじめて DB に入る。`PATCH /docs/{id}` は
編集の後に `async` の `announceDocUpdate`: nyxis が題名と更新日時を予約テーブル `_nyxis_outbox` に同じトランザクションで
書き、COMMIT の後に内部ループが監査ログ API に送る。送り先はどちらも統合テストが
`https://localhost:18118` に立てるローカルの模擬 API)は実装済み。

## バックエンド

承認する正本は `backend/schema.cedarschema`(テーブル定義を兼ねる Cedar スキーマ。各アクションに効果の宣言)と
`backend/policies.cedar`(Cedar ポリシー)。ハンドラは `backend/TeamDocs/Handlers.lean`(HTTP API の表はその冒頭)。

リポジトリ直下で依存とコアを準備してから、`backend/` でビルドする。

```sh
python3 scripts/prepare-dependencies.py
lake build
cd examples/team-docs/backend
lake build
```

`backend/.lake/build/bin/teamDocs [port]` が HTTP サーバ(既定 8080)。`NYXIS_DATABASE_URL`(nyxis 専用ロールの
PostgreSQL 接続文字列)と `NYXIS_SUPABASE_ISSUER`(`https://ホスト[:port]/auth/v1`)を環境変数で渡す。
ブラウザから呼ぶときは `NYXIS_CORS_ORIGINS`(カンマ区切りの origin)も渡す。
添付(署名付き URL の発行)には Supabase Storage の設定を 3 つ揃えて渡す: `NYXIS_STORAGE_URL`(Supabase プロジェクトの
`https://ホスト[:port]`)、`NYXIS_STORAGE_BUCKET`(非公開バケットの名。事前に作っておく)、`NYXIS_STORAGE_SERVICE_KEY`
(service_role キー。秘密。環境変数でだけ渡す)。無ければ添付の発行だけが 503 になり、他の操作は動く。
通知のメール送信には `NYXIS_SMTP_URL`(中継。本番は `smtps://[user:pass@]ホスト[:port]`。秘密。ローカルの Mailpit には
`smtp://127.0.0.1:55326`)と `NYXIS_MAIL_FROM`(差出人)を 2 つ揃えて渡す。無ければ送信を伴う要求(共有)が 503 になる。
定期処理(送れなかった通知の送信)には `NYXIS_SERVICE_PRINCIPAL`(サービス主体の ID。`Service::"<id>"` の形か `<id>`)と、
任意で `NYXIS_JOB_INTERVAL_SECONDS`(間隔。既定 60)を渡す。このサンプルは定期処理を宣言しているので、
`NYXIS_SERVICE_PRINCIPAL` が無ければ起動を拒む。
外部 API 呼び出しには、正本の送り先が名指す鍵 `NYXIS_EXT_SUMMARIZER` と `NYXIS_EXT_AUDIT`(秘密。環境変数でだけ渡す。
模擬 API に対しては任意の文字列)を渡す。正本に送り先がある限り必須で、無ければ起動を拒む。任意で輸送の上限
`NYXIS_CALL_CONNECT_TIMEOUT` / `NYXIS_CALL_MAX_TIME` / `NYXIS_CALL_MAX_RESPONSE_BYTES`(既定 3 秒・10 秒・64KiB)と、
アウトボックスの内部ループの `NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` /
`NYXIS_OUTBOX_BACKOFF_BASE_SECONDS`(既定 5 秒・8 回・10 秒。`docs/external-calls.md` §5)。
`backend/.lake/build/bin/initTeamDocsDatabase` は正本のテーブルを新規に作る(既存テーブルがあれば失敗する)。

## 検査

ローカル Supabase(リポジトリ直下の `supabase start`。`docs/local-supabase.md`。Storage と Mailpit の SMTP ポート 55326 を
有効にしてある)の上で、実際の Auth が発行した JWT を持つ 6 つの主体(owner / editor / viewer / 複数組織の member / 組織外 /
個別共有先)と匿名・不正な JWT から、文書の一覧・読み取り・作成・編集・削除・共有・組織の所属の変更(所属行 `Membership` の
追加と削除、owner の集合の変更)・添付(署名付き URL の発行と、その URL でのローカル Storage へのアップロードとダウンロード)・
通知(購読、共有時のメールが Mailpit に届くこと、読めない購読者には届かないこと、サービス主体の定期処理、JWT ではサービス
主体を名乗れないこと)・外部 API 呼び出し(テストが `https://localhost:18118` に立てる模擬 API に対し、要約の `sync` の
呼び出しが owner / editor にだけ成立して応答が `recordSummary` の判定を通って記録され、空の要約は拒まれ、2xx 以外は 424 に
写り、許可しない主体には 403 で送信が発生せず、許可された編集ごとの `async` の通知がアウトボックスを経て届くこと)を
HTTP で試みる統合テスト:

```sh
python3 scripts/local-supabase.py --exec python3 scripts/check-team-docs.py
```

正本の妥当性は `cedar validate --schema backend/schema.cedarschema --policies backend/policies.cedar --deny-warnings`。
`backend/TeamDocsTest/Model.lean` は同じハンドラをランタイムの純粋モデルの上で動かす検査で、`lake build` が実行する。
