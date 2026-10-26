# 接続コードの作り — 仮定を支える nyxis の責務

[ASSUMPTIONS.md](../ASSUMPTIONS.md) の各仮定(Assumption 1〜3)を支えるために、nyxis が作りで保証していることの説明。ここに書くのは実装の責務であって、信頼する仮定ではない(証明済みの性質に触れるときは定理名を添える)。証明済みの定理と、それぞれが述べないことの目録は [docs/proofs.md](proofs.md)。接続コードは Assumption 1 として当面信頼し、証明できた部分から順に proofs.md へ移している。

## 1. 認証 — JWT から主体を決める(Assumption 1・2)

対象: `Nyxis.Internal.SupabaseJwt` / `JwksFetch` / `HttpAuth`。

- 検証のたびに JWKS を HTTPS で取得する。発行者(コア設定 `NYXIS_SUPABASE_ISSUER`。`https://ホスト[:port]/auth/v1`)から JWKS の URL を固定導出し、要求の URL・ヘッダ・トークンは接続先に使わない。輸送は shell を経由しない curl(8.4 以降。版の確認は起動時に 1 回 `ApprovedServer.serve` が行い、確認できなければ起動を拒む)で、`--disable` を先頭に、HTTPS のみ、リダイレクト非追従、接続 3 秒・全転送 5 秒、本文 64KiB 以内、HTTP 200 のみ受理。機密ヘッダを送らず、stderr は捨てる。取得の失敗は匿名へ閉じ、古い鍵へ戻らない。
- 承認済み実装(OpenSSL の libcrypto と lean-jose / jose-libcrypto / lean-libcrypto)で ES256 の JWT を検証する。`alg: none` を拒み、署名・発行者・audience `authenticated`・有効期限を猶予 0 で確かめる。非空で NUL を含まない `sub` だけをコア設定のエンティティ型の ID にする。暗号と JOSE の解析は自作しない。
- 検証に失敗するリクエストと JWT の無いリクエストは匿名として扱う。Authorization ヘッダは単一の `Bearer` 値だけを受け、重複・結合ヘッダ・空白のみ・NUL 入りは匿名。時計はリクエストごとに、JWKS の取得後に読む。
- 同じ機械の時計をサーバー生成値の現在時刻(下の 4.)にも使う。

## 2. HTTP の入口と応答(Assumption 1)

対象: `Nyxis.Http`(`Std.Http` の上の共通部品)、`Nyxis.Internal.PostgresHttp`、`Nyxis.Internal.HttpResponse`、`Nyxis.Internal.Cors`。

- ハンドラに渡す要求の要約は、メソッド・パス(問い合わせ文字列を除く)・問い合わせ文字列・`Nyxis.Http.RequestHeader` に列挙した少数の要求ヘッダ(Accept・Accept-Language・Content-Type・If-None-Match・If-Match)・本文だけで、Authorization と Cookie はその型に無い(`Http.selectHeaders`)。本文は 1 MiB まで、超過と UTF-8 でない本文は 400 でハンドラを呼ばない。
- 応答は `Http.responseBuilder` が組む。ハンドラが設定できるのは `Nyxis.Http.ResponseHeader` に列挙した少数(Content-Type・Cache-Control・ETag・Location。Set-Cookie は型に無い)で、妥当でない値と Cache-Control の `public` / `s-maxage` は捨て、同じ名前は最初の値だけを載せる。Content-Type が無ければ `text/plain; charset=utf-8`。
- DB 失敗(取得が判定材料を覆わない・取得した行の形状不一致・SQL や照合の失敗を含む)は詳細無しの固定 503、読めない本文は固定 400、`GET /health` は DB に触れず固定 200。外部 API 呼び出し(`sync`)の 2xx の応答が宣言した型に合わなかった失敗だけは、トランザクションの取り消しの後に詳細無しの固定 502(`PostgresRun.gatewayResponse`)。DB 接続・JWKS・curl・JWT の診断文字列は応答にもログにも出さない。
- CORS(`Nyxis.Internal.Cors`)は、コア設定 `NYXIS_CORS_ORIGINS`(カンマ区切りの HTTP(S) オリジンの完全一致。未設定・空は不許可、不正な設定は起動拒否)に合う Origin ヘッダ(ちょうど 1 つのとき)にだけ Allow-Origin を付け、プリフライト(OPTIONS)の応答にはさらに固定の Allow-Methods / Allow-Headers を付け、すべての応答に `Vary: Origin` を付ける。OPTIONS は本文の読み取り・認証・ハンドラ・DB より前に空の 204 を返す。cookie の credentials は許可しない。
- 実起動 `Nyxis.Internal.ApprovedServer.serve` は、宣言から組んだ App だけを起動する(下の 7.)。

## 3. 段階的な実行 — 1 要求 = 新規接続 1 本の SERIALIZABLE トランザクション(Assumption 1・2)

対象: `Nyxis.Internal.PostgresRun.handleStaged` / `runStaged`(実起動 `PostgresHttp.handleVerified` → `ApprovedServer.serve` が使う経路)、`PostgresMaterials`、`PostgresSql`、`PostgresResult`、`PostgresWrite`、`PostgresShape`。

- ハンドラのアクション呼び出しごとに、判定に必要な実体だけを主キーの点検索で取得する(`PostgresMaterials.load`)。判定が絞り込みで行を見るところ — 一覧の対象テーブル、一意性の組と同じ値の行、削除で消える行を参照する行(連鎖の段ごと)、所属行(`loadMemberships`)— では、絞り込みを WHERE 句にした SELECT(`PostgresSql.selectFiltered`)で取得する。SQL はコア生成の SELECT だけで、絞り込みの定数もパラメータで渡す。
- 取得が判定材料を覆っているかを実行可能な検査(`Authz.coversStep`: 対象の行の有無、ポリシーの level について要求から到達できる実体、参照先の行の有無、連鎖の各行とその後の状態の判定材料)で確かめてから、取得した行だけで判定する(`Authz.step`)。取得した行は正本から構成した形状(`PostgresShape`)で列の型と必須属性を検査し、発行前の提案値も検査する。
- 発行した操作だけを SQL にし(`PostgresSql`。識別子はスキーマから、値はパラメータから)、各操作の結果を直前の `Store.apply` の期待値と照合する(`PostgresRun` / `PostgresResult` / `PostgresWrite`。書き込みは commandOk・行列 0・影響件数 0 または 1・操作別のタグ)。検査に通らない・形状が合わない・不一致・失敗は rollback して応答を返さない。応答は checked COMMIT の後だけ返す。
- ここで信頼するのは「点検索の結果は DB の現在の行であり、WHERE 句つき SELECT の結果は DB の現在の行のうち絞り込みに合う行の全部である(SQL の比較がモデル `Db.Filter.matches` と一致する)」こと(`PostgresRun.Chain`。絞り込みの集合は `Authz.rowFilters`)。これは Assumption 1 の信頼で、新たな仮定ではない。
- 正本の制約は同じ規則で DB にも置く(`PostgresSql.createTable` の `UNIQUE (列, …)`、参照の列の保存形式の ID を持つ生成列 `_nyxis_ref_<列>` と `PostgresSql.foreignKeys` の `FOREIGN KEY … ON DELETE RESTRICT`、参照する側の索引。`PostgresInit.provision` が全テーブルの後に付ける)。判定はモデルが先に行い、連鎖の削除はモデルが判定した各行の DELETE を深い行から順に明示的に発行する(DB の CASCADE は使わない)。DB の制約はその裏付けで、判定が外れていれば(取得が DB と食い違っていれば)SQL が失敗して要求全体が閉じる(rollback、503)。制約の有無は判定の結論を変えないので、この裏付けに新たな信頼は要らない。
- 全テーブルの現在行を読んで `Store` を復元し(`PostgresLoad`)、モデル `Runtime.handleRequest` を純粋に計算して発行した操作を同じく SQL にして照合する参照経路(`PostgresRun.handle`)は実起動では使わない。コアの検査(`scripts/check-postgres-values.py`)が両経路をそれぞれ別の実 DB で同じ期待値(応答・残る行)に照らして確かめる。この経路で `Store` が DB の現在の行であると信頼するのは上と同じ種類の信頼で、新たな項目ではない。形状検査(`PostgresShape`)の対象は、段階的な経路では取得した行、参照経路では認可前の全行で、どちらも発行前の提案値を検査する。
- テーブルの構築は HTTP とは別の明示的な実行ファイル(`PostgresInit.provision`。全 CREATE TABLE の計画を接続前に検査し、新規接続の SERIALIZABLE で実行)で行い、既存テーブルでは失敗する。移行・初期データ・権限の作成は行わない。
- PostgreSQL クライアントは lean-pq(固定版)に人間承認の `scripts/patches/lean-pq-ownership.patch`(所有権と資源解放の修正のみ。追加バインディングは無い)を当てて使う。利用は nyxis 内部に限り、ハンドラには接続・生 SQL・クライアントの操作 API を公開しない。エラーの後は接続を再利用しない。

## 4. サーバー生成値(Assumption 1・2)

対象: `Nyxis.Internal.Generated.fresh` → `PostgresHttp.dispatch`。

- 一意 ID は、認証の直後に 1 度だけ、ランタイムの乱数(`IO.getRandomBytes`。OS の乱数源)16 バイトから版 4 の UUID として作り、現在時刻とともに `Runtime.AuthenticatedRequest.generated` としてハンドラ(値の提案用)と認可層(正本が `context` に `now` / `id` を宣言したアクションの文脈)に渡す。要求のどの項目からも決めず、ハンドラは差し替えられない(主定理)。
- ID の一意性はランタイムの乱数源に依存し、定理は主張しない(衝突しても挿入は 409 に閉じる)。1 要求に生成値は 1 組(複数行を挿入するハンドラは同じ ID を 1 行の主キーにしか使えず、一覧の各行の判定は同じ `now` を見る)。
- 挿入の主キーと提案値に生成値を使うのはハンドラで、nyxis は強制しない。提案値が生成値と一致することはポリシーが `context.values.x == context.now` / `== context.id` と書いて判定し、主キーは Cedar の式から参照できないので、主キーに生成 ID を使うことはハンドラの作り(と 2 つめのサンプルの統合テスト)が担う。

## 5. 宣言された外部効果 — Storage・メール・外部 API 呼び出し(Assumption 1〜3)

対象: `Nyxis.Internal.StorageSign` / `MailSend` / `CallSend` / `ExternalSend` / `Outbox`、`PostgresRun.runStaged`。

- 判定が外部効果を記録していれば(`Authz.External`: 主体・生成値・アクション・対象・内容。permit された行について `Authz.payloadOf` が決めたもの)、その記録についてだけ Storage に発行を求め、メールを送り、外部 API を呼び、`async` の呼び出しをアウトボックスに書く(`PostgresRun.sendExternal` → `Driver.external` → `ExternalSend.send` → `StorageSign.sign` / `MailSend.send` / `CallSend.call`、`async` の呼び出しは `Outbox.enqueue`)。結果(`Authz.ExternalResult`: 署名付き URL、`sync` の呼び出しの応答、結果なし)の値が判定を変えないことは `Authz.step_external_indep`。得た結果つきで続きを進める。ハンドラは宛先も内容も送り先も提案できない(効果の型にその引数が無い。`call` で `context.values` を取るアクションの提案値だけが、判定を通って本文に入る)。
- 発行・送信の失敗(接続・TLS・5xx・SMTP の拒否。`sync` の呼び出しでは輸送の失敗と応答の復号の失敗)は例外で、同じトランザクションの DB 操作ごと rollback して 503 を返す(黙って成功にしない)。ただし `sync` の呼び出しの 2xx の応答が宣言した型に合わなかった失敗(`CallSend.invalidResponse`: JSON でない・宣言したキーの欠落・型違い)だけは、`PostgresRun.handleStaged` が取り消しの後に固定の 502(`PostgresRun.gatewayResponse`)に写す(`PostgresRun.handleStaged_success` のもう 1 つの分岐: 応答は固定値で、同じ本体 `PostgresRun.stagedBody` のトランザクションがその例外で失敗している)。発行・送信が成功した後に COMMIT が失敗すると、DB は戻るが発行・送信は取り消せない(DB の外の効果。`sync` の呼び出しではこれが Assumption 3 の冪等キーの仮定)。そのときも応答は checked COMMIT の後にしか返らないので URL や応答は利用者に届かず、届いた URL の対象は常に permit された行のオブジェクトに限り、送られたメール・呼び出しは常に permit された行の宣言された列(と判定を通った提案値)の内容に限る(送信済みの記録を DB に残すアプリでは、その更新だけが戻って再送されうる)。
- Storage: 発行先の URL(`{NYXIS_STORAGE_URL}/storage/v1/object/[upload/]sign/{バケット}/{パス}`)はコア設定と記録から固定の形で組む(要求の URL・ヘッダ・本文・ハンドラの値は使わない)。パスは `テーブル/<主キー>/<名>` で、要素は英数字・`-`・`_` だけに限り、そうでない主キーや名では発行しない(`Db.objectPath`)。輸送は JWKS と同じ承認済み curl(HTTPS のみ、リダイレクト非追従、接続 3 秒・全転送 5 秒、本文 64KiB)で、資格情報(`NYXIS_STORAGE_SERVICE_KEY`)は標準入力の設定で渡し引数に出さない。ダウンロード URL の有効期限はコアの定数 `StorageSign.expiresIn`(600 秒)で、要求からは変えられない(アップロード URL の期限は Storage 側が決める)。Storage が「オブジェクトが無い」(404、または 400 の `not_found`)を返せば `Outcome.notFound`。
- メール: 中継(`NYXIS_SMTP_URL`)・差出人(`NYXIS_MAIL_FROM`)はコア設定で固定。宛先・差出人は印字可能 ASCII の単一のアドレスに限り(空白・`<>`・`"`・`\`・`,`・`;` は拒む)、件名のヘッダから改行と制御文字を除き(非 ASCII は encoded-word)、本文は UTF-8 の text/plain で送る。メッセージは所有者だけが読める一時ファイルに書いて curl の `upload-file` で渡し、送信後に消す(curl の SMTP は標準入力の設定と本文を同時には取れない)。`--disable` 先頭、`--proto =smtp,smtps`、リダイレクト非追従、接続 5 秒・全転送 20 秒。資格情報は標準入力の設定で渡し引数に出さない。
- 外部 API 呼び出し(`sync`): URL は正本の `@external` の送り先のベース URL と固定のパス(`{key}` は主キー)、または行の URL の列の値(`https://` のみ。`Db.callUrl`)で、要求の URL・ヘッダ・ハンドラの値は使わない。認証ヘッダは送り先ごとにコア設定 `NYXIS_EXT_<名前>`(正本には環境変数名だけ)から起動時に組み(`CallSend.Config.load`。無ければ起動を拒む)、標準入力の設定で渡し引数・記録・応答・例外に出さない。本文は行の宣言された列と判定を通った提案値の JSON(`GET` / `DELETE` では無し)。接続と全転送の上限・応答本文の上限はコア設定(`NYXIS_CALL_CONNECT_TIMEOUT` / `NYXIS_CALL_MAX_TIME` / `NYXIS_CALL_MAX_RESPONSE_BYTES`。既定 3 秒・10 秒・64KiB。正本の `<秒>s` は全転送の上限を短くだけ上書き)。2xx の応答は JSON として読み、正本で宣言したレコード型に寛容に復号する(`CallSend.decode`: 宣言したキーの欠落と型違いだけを拒み、余分なキーは捨てる)。2xx 以外は状態コードと生の本文を `Outcome.calledError` としてハンドラに渡す(トランザクションは続く)。復号の失敗は上の固定 502。模擬 API に対する統合検査は `scripts/check-external-calls.py`(`Test/ExternalCalls.lean`: deny で送信なし・認証ヘッダ・余分なキーの破棄・欠落と型違いの 502 と取り消し・2xx 以外・輸送の失敗・鍵の非表示)。
- 外部 API 呼び出し(`async`。アウトボックス): permit された記録を `PostgresRun.driver` の `external` が要求と同じ接続(同じ SERIALIZABLE トランザクション)で予約テーブル `_nyxis_outbox` に 1 行書く(`Outbox.enqueue`。主キー `<要求の一意 ID>-<番号>`、主体・アクション・対象・送り先の名前・メソッド・解決済みの URL・本文の JSON・`pending`。鍵は書かない)。送信はせず、ハンドラには `ok none` が渡る。要求の COMMIT が失敗すればこの行も残らない。テーブルは `PostgresSql.outbox` の DDL を `PostgresInit.plan` が正本のテーブルの後に出す(形は docs/external-calls.md §4.3 に固定。正本のテーブルからは見えない)。COMMIT の後は nyxis 自身の内部ループ(`Outbox.loop`。`ApprovedServer.serve` が正本に `async` の宣言があるときだけ別スレッドで始める。判定はしない)が、コア設定の間隔(`NYXIS_OUTBOX_INTERVAL_SECONDS`、既定 5 秒)ごとに期限の来た `pending` の行を READ COMMITTED のトランザクションで 1 行ずつ `FOR UPDATE SKIP LOCKED` で取り出し(複数インスタンスで同じ行を 2 つが送らない)、その行の内容だけを `sync` と同じ輸送の方針(承認済み curl、HTTPS のみ、認証ヘッダは送り先ごとにコア設定から。`CallSend.arguments` / `configTextJson`)で送り、同じトランザクションで状態を更新する(`Outbox.step` / `settle`): 2xx → `sent`、4xx → `failed`、他の状態コード・輸送の失敗 → `attempts` を増やして `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS × 2^attempts` 秒後に再試行、`NYXIS_OUTBOX_MAX_ATTEMPTS`(既定 8)で `failed`。応答本文は捨て、`failed` の行は消さない。送信の後に状態の更新・COMMIT が失敗した(プロセスが落ちた)行は再送される(少なくとも 1 回の配送。Assumption 2 の「定理が述べないこと」)。`async` の宣言があるのに送り先の設定(`NYXIS_EXT_<名前>`)が無ければ起動を拒む(`Outbox.check`)。統合検査は `scripts/check-outbox.py`(`Test/Outbox.lean`: deny で記録なし、要求中は送信なし、1 要求 2 行、COMMIT 失敗で行が残らない、2 プロセスの内部ループで各行ちょうど 1 回、5xx → 2xx の再送、4xx の即 `failed`、最大試行回数の `failed`、鍵の非表示)。
- 診断は応答にもログにも出さない。

## 6. 定期処理とサービス主体(Assumption 3)

対象: `Nyxis.Internal.Jobs`、`ApprovedServer`。

- サービス主体は予約型 `Service`(テーブルではなく、行も属性も無い。`CedarSchema` が属性・親・tags・所属行・添付・効果の対象を拒む)の実体 `Service::"<設定の ID>"` で、定期処理の起動にだけ使う(`Authz.Principal.service`)。
- 定期処理はコア設定 `NYXIS_SERVICE_PRINCIPAL`(サービス主体の ID)と `NYXIS_JOB_INTERVAL_SECONDS`(間隔。コアは 1〜86400 秒だけを受け付け既定値を持たない。2 つめのサンプルの `Main` が未設定のとき 60 を渡す)から、同じプロセスの別スレッドで固定間隔に、アプリが `App.jobs` に宣言した各定期処理を主体 `Service::"<ID>"`・新しいサーバー生成値・`job := some i` の要求として `PostgresRun.handleStaged`(HTTP と同じ 1 起動 = 1 トランザクションの段階的な経路)に流す。失敗した起動は捨て、次の間隔で再び流す。ハンドラと同じ型(IO なし)で書かれる。
- HTTP の入口(`PostgresHttp.dispatch`)は `job := none` の要求しか組まず、主体を JWT の検証結果と配置の利用者型だけから作る(`HttpAuth.principalOf`)。配置は利用者型が `Anonymous` でも `Service` でもないことの証明を持つ(`Deployment.user_not_service`)ので、JWT の `sub` が設定の ID と同じでもその主体は `User::"<sub>"` であり、サービス主体にはならない。
- 正本が `entity Service;` を宣言していないのに設定がある・定期処理を宣言したのに設定が無い場合は起動を拒む。

## 7. 承認済み正本の構成(Assumption 3)

対象: `Nyxis.Build`、`Nyxis.CedarSchema`、`Nyxis.CedarPolicy`、`Nyxis.Approved`、`Nyxis.Internal.ApprovedServer`。

- 認可の入力はアプリケーション側の宣言 `nyxis_approved name from "<schema>" and "<policies>"` からビルド時に構成する。`Nyxis.CedarSchema` が `.cedarschema` を読んで効果の宣言(`@effect` と、親・所属行・一意性・参照整合・添付の注釈)を検査し、`Nyxis.CedarPolicy` が `.cedar` を Cedar 4.13 の解析器と同じ抽象構文に構成する。構成に失敗すれば `lake build` が失敗する。Lake の `input_file` / `needs` で正本の変更を再ビルドへ反映する。
- `name.app` は router(と定期処理)だけを受け取り、実起動 `Nyxis.Internal.ApprovedServer.serve` は宣言・形状・利用者型を持つ `Deployment` と router(ほかに port・接続文字列・issuer・CORS 設定・外部効果の設定・サービス主体の設定)を受け取り、App を必ず宣言から内部で組む。
- 構成コードは証明の対象ではなく、`Test/Schema.lean`・`Test/Policy.lean` と、サンプルの `BulletinBoardTest/Model.lean`(正本から構成した値と手書きの抽象構文の一致)で振る舞いを確かめる。Cedar 自身によるポリシーの検証(スキーマとの整合)は `cedar validate` が担う。

## 8. アプリケーションの監査(Assumption 3)

対象: `Nyxis.Handler`、`Nyxis.AppCheck`(コマンド `nyxis_check_app`)。

- `Nyxis.Handler` は IO への持ち上げや DB の操作・状態を受け取る構成子を持たない。
- `nyxis_check_app` は、検査器のコンパイル時に固定した信頼済みモジュール(nyxis とその Lean・Std・Cedar 等の依存)以外の全定数を調べ、`dbgTrace*` / `panic*` / `ptrAddrUnsafe` / `unsafeCast` / `sorryAx` / `setImplementedBy` への参照、unsafe 宣言、extern・implemented_by 属性、初期化、macro・elaborator 属性を拒否する。private な補助関数や別モジュールのラッパーも対象になる。
- アプリからの lean-pq・JOSE・それらを使う `Nyxis.Internal.*` の import は、依存の extern 属性で監査が拒む。`Nyxis.Internal.Generated` / `HttpAuth` のように extern を持たない内部モジュールの import は監査に掛からないが、それらの処理は IO で、`Handler` の型からは呼べない。
- 限界: 監査は elaboration と import の後の環境を検査するもので、ビルドのサンドボックスではない。検査に到達する前のビルド過程の IO、定数を残さないコマンド、検査後に追加したコード、検査を削除・差し替えたビルドは防げず、`main` の IO の内容も制限しない。禁止リストの網羅性は未証明。これらは Assumption 3 として信頼する。

## 9. 型と定義による性質(仮定ではないもの。多くは定理の文ではなく型と定義の構造による)

- ハンドラが主体・対象・効果を指定したり差し替えたりできないこと(`Handler` の型と `Authz.step` の構造。主体と生成値を偽れないことは主定理の `i.principal = r.principal ∧ i.generated = r.generated` が定理として述べる)。主体はそのリクエストの JWT から、対象は DB の現在の行から、効果はスキーマの宣言から、nyxis が決める。
- 発行される DB 操作が宣言された効果の範囲内(種類・テーブル・更新では列)にあること(`Db.Operation.withinEffect`)。
- 認可層 `Authz.step` が呼ぶ Cedar の評価器が cedar-spec の Lean モデルそのもの(`Cedar.Spec.isAuthorized`)であり、別の実装を使わないこと。したがって「Cedar の実装がモデルと一致する」という仮定を置かない(評価器を実行するランタイムは Assumption 1)。
- 判定の実体は現在の行のうちスキーマに適合する行とスキーマのアクションで、親を指す列(`@parents`)と所属行(`@memberships`)の値のうち宣言された親の型のものが祖先になる(`Materials.rowAncestors_ty`)。認可層の実際の判定(`Authz.permits`)は要求から有限の段数で到達できる実体だけ(`Authz.materials`、cedar-lean の `sliceAtLevel`)で行う。全体での判定と一致することは定理(`Authz.permits_authorized`。proofs.md)。
- ハンドラが読める要求ヘッダと設定できる応答ヘッダが列挙型に限られること(上の 2.)。「列挙外の名前が現れない」は型と定義による性質で、定理の文ではない。
- 判定材料の約束: 主体の実体は常に DB の現在の行(無ければ実体なし)。対象は DB の現在の行、挿入で行が無ければ提案される行(主体自身を除く)。挿入・更新の提案値は `context.values`。書き込みの `Outcome.ok` は行を返さない。permit された操作が DB 層で `conflict`(挿入で同じ主キーの行がある)/ `notFound` に終わっても操作は記録される(状態は変わらない)。正本の制約(`@unique` / `@references`)に違反する操作は permit されていても記録されず `conflict` になり、競合が無く連鎖で消える行のどれかが permit されない削除は記録されず `denied` になる(どちらもその呼び出しだけ。競合の判定が先。`Authz.stepOp`)。
