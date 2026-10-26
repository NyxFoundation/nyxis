# 外部 API 呼び出し — 設計

nyxis のバックエンドから外部の HTTP API を呼ぶ仕組みの設計。2026-10-25 に確定した決定を記す。

関連: [ASSUMPTIONS.md](../ASSUMPTIONS.md) Assumption 2・3(メールと外部 API の送り先、鍵の秘匿と冪等キー)、[docs/proofs.md](proofs.md)(定理の (6)〜(9))、
[docs/connection.md](connection.md) 5.(外部効果の送信)。

実装: §3 の文法と §3.4 の拒否(`Nyxis/CedarSchema.lean`)、純粋モデル(`Nyxis/Db.lean` の
`EffectKind.call`、`Nyxis/Authz.lean` の `Payload.call` / `ExternalResult` / `CallRecorded`)、定理の (8)(9)
(`Nyxis/Runtime.lean`)、`sync` の送信と応答の寛容な復号(`Nyxis/Internal/CallSend.lean`)、復号の失敗の固定の 502 への
写し(`PostgresRun.handleStaged`: `CallSend.invalidResponse` だけを取り消しの後に `PostgresRun.gatewayResponse` に写す)、
模擬 API への統合テスト(`Test/ExternalCalls.lean` と `scripts/check-external-calls.py`)、§4.2〜§4.3 の
アウトボックスと内部ループ(`Nyxis/Internal/Outbox.lean`: `enqueue` が `PostgresRun.driver` から要求のトランザクションで
`_nyxis_outbox` に書き、`loop` / `tick` / `step` が READ COMMITTED の `FOR UPDATE SKIP LOCKED` で 1 行ずつ送って状態を更新する。
予約テーブルは `PostgresSql.outbox` の DDL を `PostgresInit.plan` が正本のテーブルの後に出す。起動は
`ApprovedServer.serve` の `Outbox.start`(正本に `async` の宣言があるときだけ)。統合テストは `Test/Outbox.lean` と
`scripts/check-outbox.py`)、2 つめのサンプルへの導入(`examples/team-docs/backend` の正本に
`@external` の送り先 `Summarizer`(`sync`。`summarizeDoc` の応答 `{ summary: String }` をハンドラが別のアクション
`recordSummary` で列 `summary` に記録する — 空の要約はポリシーが拒む)と `Audit`(`async`。`editDoc` の後の
`announceDocUpdate` がアウトボックス経由で送られる)。送り先はローカルの模擬 API `https://localhost:18118`(正本の `base` は
固定文字列なので、統合テスト `scripts/check-team-docs.py` が同じ固定ポートに立てる)。起動処理 `Main.lean` が
`CallSend.Config.load` と `Outbox.Config.load` を配線する)。以前の `webhook` 効果は D12 のとおり廃止した
(`WebhookSend.lean` は削除)。

## 1. 実装前の現状と問題(2026-10-25 の対話の時点)

実装前の `@effect("webhook T(URL 列; 本文列…)")`(旧 `Nyxis/Internal/WebhookSend.lean`)は次に固定されていた。

| 項目 | 現状 |
|---|---|
| メソッド・形式 | POST、JSON 固定 |
| ヘッダ | Content-Type のみ(認証ヘッダを付けられない) |
| 送り先 | 行の列の値。HTTPS 限定 |
| 応答 | 2xx かどうかだけ見て本文は捨てる |
| 実行時機 | 要求の SERIALIZABLE トランザクション内で同期 |
| 失敗時 | 503 で要求全体を取り消す。再試行なし |

このため、認証付きの API を呼べず、応答を使えず、送信後に COMMIT が失敗すると外部には届いて DB は巻き戻る
(非原子性)。外部連携は「通知を投げる」用途にしか使えない。

## 2. 決定の一覧

| # | 論点 | 決定 |
|---|---|---|
| D1 | 送り先 | 正本で名前付きの送り先(予約の仲間 `entity Stripe;` に `@external`)を宣言する。ベース URL と認証方式は正本、鍵はコア設定の環境変数。ハンドラは URL もヘッダも組めない |
| D2 | 呼び出し | 宣言された効果 `@effect("call …")` として認可層を通す。本文は対象行の列と `context.values` の提案値と生成値から nyxis が組む |
| D3 | 応答の渡し先 | 応答を正本で宣言した型に復号し、ハンドラへ値として渡す(nyxis が列へ直接書く案は不採用)。DB へ書くときはハンドラが別アクションを呼び、通常の判定を通る |
| D4 | 実行時機 | 正本が決める(ハンドラは選ばない)。`sync` は応答を返しトランザクション内で同期、`async` は応答なしでアウトボックスに書いて COMMIT し、後で送る |
| D5 | sync の非原子性 | 許容して文書化する。副作用のある API を sync で呼ぶなら冪等キーに要求の一意 ID `context.id` を使う(信頼する仮定: Assumption 3) |
| D6 | アウトボックスの置き場 | nyxis の予約テーブル `_nyxis_outbox`。正本に現れず、アプリのポリシーからも見えない |
| D7 | 送信者 | サービス主体の定期処理ではなく nyxis 自身の内部ループ。送信時に再判定しない(permit は書き込み時に 1 回) |
| D8 | 失敗の終着 | 最大試行回数を超えた行は `failed` で残し、nyxis は消さない。アプリが読む効果は当面なし(SQL で直接見る運用) |
| D9 | 応答の型検査 | 寛容。宣言したキーの欠落と型違いだけを拒否し、余分なキーは捨てる |
| D10 | sync の 2xx 以外 | 503 にせず、状態コードと生の本文をハンドラへ渡す(`Outcome.calledError`)。業務上の失敗(402・422 等)をハンドラが 400・409 等に写せる |
| D11 | 上限 | 既存の webhook と同じ水準をコア設定で変えられる。sync の全転送上限は効果ごとに短く上書きできる |
| D12 | 既存の `webhook` 効果 | `call` の `async` に吸収して廃止する(送り先が行の列の値である点だけが現行と異なるので、§3.3 の `url: 列` で残す)。`mail` は別の輸送(SMTP)なので残す |

## 3. 正本の文法

### 3.1 送り先の宣言(エンティティ側)

```
@external("base: https://api.stripe.com; auth: bearer NYXIS_EXT_STRIPE")
entity Stripe;
```

- `Service` / `Anonymous` と同じ予約の仲間。テーブルではなく、属性・親・tags を持てない。アクションの `appliesTo` の
  主体にも対象にも書けない(効果の中でだけ名指しする)。
- `base`: `https://` で始まる固定のベース URL。パスを含んでよい。末尾の `/` は正規化する。
- `auth`: 次の 3 種。環境変数名だけが正本に載り、値はコア設定で渡す。未設定なら起動を拒む。
  - `bearer <環境変数名>` — `Authorization: Bearer <値>`
  - `header <ヘッダ名> <環境変数名>` — 任意の 1 ヘッダ(例: `header X-API-Key NYXIS_EXT_MAPS`)。値は前後の空白を
    除いたうえで、途中に空白(SP)を含んでよい(例: `header Authorization NYXIS_EXT_LEGACY` に `Basic …` を渡す)。
    `bearer` の値は空白を含まない
  - `none`
- 1 つの正本に送り先はいくつでも宣言できる。

### 3.2 操作の宣言(アクション側)

```
@effect("call Stripe POST /v1/charges T(amount, currency) sync -> { id: String, status: String }")
action "chargeOrder" appliesTo {
  principal: [User],
  resource: [Order],
  context: { "values": { "amount": Long, "currency": String }, "id": String }
};
```

文法(1 アクションに効果は 1 つ。既存と同じ):

```
call <送り先> <メソッド> <パス> <T>(<列>, …) (sync [<秒>s] -> <レコード型> | async)
```

- `<送り先>`: `@external` を持つ予約型の名前。無ければ拒む。
- `<メソッド>`: `GET` / `POST` / `PUT` / `PATCH` / `DELETE`。
- `<パス>`: 固定文字列。`{key}` だけを対象行の主キーで埋められる(ハンドラや列の値はパスに入らない)。
  `?` と `#` は拒む。問い合わせ文字列が要る API は本文で代替できないので当面対象外とする。
- `<T>(<列>, …)`: 本文に載せる対象行の列。`T` はアクションの `resource` にあるテーブル。空 `T()` も許す。
  `GET` / `DELETE` では本文を送らないので列は書けない。
- `context.values` を宣言したアクションでは、提案値も本文に混ぜる(列と同名なら拒む)。ポリシーは
  `context.values` で絞れる(例: `context.values.currency == "jpy"`)。
- 本文は JSON オブジェクト。値の写しは `CallSend.jsonOf`(旧 `WebhookSend.jsonOf`)と同じ(実体参照は ID、datetime はエポックミリ秒、
  decimal は文字列、集合は配列、レコードはオブジェクト)。生成値は `context.id` を `values` に写すことで載せる
  (nyxis が勝手に本文へ足すキーは無い)。
- `sync [<秒>s] -> <レコード型>`: 応答の型。Cedar のレコード型(`{ 名前: 型, 名前?: 型 }`。入れ子・`Set`・`datetime`
  等の拡張型を許す)。`<秒>s` は全転送の上限の上書き(コア設定の既定より短い値だけ)。
- `async`: 応答なし。アウトボックス経由。

### 3.3 送り先が行の列である場合(現行 webhook の後継)

```
@external("auth: none")
entity Hook;

@effect("call Hook POST url: endpoint T(title, body) async")
```

- `@external` に `base` が無い送り先は `url: <列>` で対象行の String 型の列を送り先に使う。`https://` で始まる値だけ
  許し、ポリシーが `resource.endpoint like "https://hooks.example/*"` で絞る(現行と同じ)。
- `base` と `url:` の併用は拒む。`url:` の送り先は `sync` も書けるが、不特定の送り先を同期で待つことになるので
  `async` を推す(文書化のみ、強制しない)。

### 3.4 ビルド時に拒むもの(`CedarSchema.elaborate` に追加)

- `@external` の無い型を `call` が名指す。`@external` の `base` が `https://` でない、`auth` の形が違う。
- `{key}` 以外のプレースホルダ、`?` / `#` を含むパス。
- `GET` / `DELETE` に本文の列がある。無い列・重複・`values` と同名の列。
- `sync` の応答型に Cedar のレコード型として構成できないもの。`async` に `->` がある。
- `@external` の型を `appliesTo` の主体・対象に書く、属性・親を持たせる。

## 4. 実行の流れ

### 4.1 sync

`PostgresRun.runStaged` の 1 段として、既存の外部効果と同じ位置で行う。

1. 判定材料の取得 → 覆いの検査 → `Authz.step`。permit されなければ `denied`(403 に写す)。何も送らない。
2. permit されたら `Authz.Payload.call` を記録する。内容: 送り先名・メソッド・解決済みの URL・本文(列名と値の列)。
   認証ヘッダの値は記録に含めない(送信時にコア設定から付ける)。
3. `Driver.external` が送る。輸送は現行の webhook と同じ curl の方針(`--disable`、HTTPS のみ、リダイレクト非追従、
   `--noproxy *`、`--globoff`)。
4. 応答:
   - 輸送の失敗(接続・TLS・タイムアウト・本文上限超過): 例外 → 要求全体 503、トランザクション取り消し。
   - 2xx: 本文を JSON として復号し、宣言した型に寛容に照らす(D9)。合わなければ 502、取り消し。
     合えば `Outcome.called (value : Cedar.Spec.Value)` でハンドラの続きへ。
   - 2xx 以外: `Outcome.calledError (status : Nat) (body : String)` でハンドラの続きへ。`body` は生の文字列
     (上限は応答本文の上限と同じ)。トランザクションは続く。
5. 非原子性(D5): 送信の後に COMMIT が失敗し得る。nyxis は防がず、Assumption 3(冪等キー)として文書化する。

### 4.2 async

1. 同じく判定 → permit なら `Payload.call` を記録。
2. `Driver.external` は送らず、`_nyxis_outbox` に 1 行 INSERT する(同じトランザクション)。ハンドラには
   `Outcome.ok none` を渡す。
3. COMMIT で確定。失敗すればアウトボックス行も残らない(原子性)。
4. nyxis の内部ループ(`Jobs` とは別。`Outbox.loop`)が `pending` の行を取り出し、送る。
   - 行の取り出しは `FOR UPDATE SKIP LOCKED` で 1 行ずつ(複数インスタンスの二重送信を避ける)。ループのトランザクションは
     READ COMMITTED(要求の SERIALIZABLE ではない。同じ述語を読んで別々の行を更新するキューでは SERIALIZABLE だと送信の後の
     COMMIT が直列化の失敗で取り消され、同じ行を再送してしまう — 統合テストで実測)。送信の後の状態の更新・COMMIT
     が失敗した(プロセスが落ちた)行は `pending` のまま残り再送される(配送は少なくとも 1 回)。
   - 2xx: `sent`。
   - 5xx・輸送の失敗: `attempts` を増やし、次の時刻を指数バックオフで決める。
   - 4xx: 即 `failed`(再試行しても変わらない)。
   - 最大試行回数超過: `failed`。
5. 応答本文は捨てる(`async` に応答型は無い)。

### 4.3 `_nyxis_outbox` の形

| 列 | 型 | 内容 |
|---|---|---|
| `_nyxis_id` | text PK | 要求の一意 ID + 段の番号(1 要求で複数の async 呼び出しがあり得る) |
| `principal` | text | 記録の主体(監査用。送信判定には使わない) |
| `action` | text | 判定したアクション |
| `target` | text | 対象 `テーブル/<主キー>` |
| `destination` | text | 送り先名 |
| `method` / `url` | text | 解決済み |
| `body` | jsonb | 本文 |
| `state` | text | `pending` / `sent` / `failed` |
| `attempts` | int | 試行回数 |
| `next_at` | timestamptz | 次の試行時刻 |
| `last_status` / `last_error` | int / text | 最後の応答。`last_error` は診断文字列を含めない(カテゴリだけ) |
| `created_at` / `sent_at` | timestamptz | |

- 正本のテーブルと同じ DB・同じロール。`PostgresInit` が正本のテーブルと一緒に作る(どの正本でも。`async` の宣言が無ければ
  空のまま。`_nyxis_outbox` という名前のテーブルは正本に書けない)。`pending` の行だけの部分索引
  `_nyxis_outbox_pending_idx (next_at) WHERE state = 'pending'` を添える(ループの 1 回のコストが送信済み・失敗の行の数に
  依存しないため。列・状態・遷移は変えない)。
- `_nyxis_id` は `<要求の一意 ID>-<その要求で何番目の async 呼び出しか>`(同じトランザクションで先に書いた同じ要求の行の数)。
  `last_error` のカテゴリは `status`(2xx 以外の応答)/ `transport`(接続・TLS・期限・本文上限)/ `config`(送り先が設定に
  無い・URL が HTTPS でない。再試行しない)/ `attempts`(最大試行回数超過)。
- アプリのハンドラ・ポリシーからは到達できない(`Authz.Schema.tables` に無い)。読む効果は当面足さない(D8)。

## 5. コア設定

| 環境変数 | 内容 | 既定 |
|---|---|---|
| `NYXIS_EXT_<名前>`(正本の `auth` が名指す名前) | 送り先ごとの鍵 | 必須(未設定は起動拒否) |
| `NYXIS_CALL_CONNECT_TIMEOUT` | 接続(秒) | 3 |
| `NYXIS_CALL_MAX_TIME` | 全転送(秒)。sync の `<秒>s` はこれより短い値だけ | 10 |
| `NYXIS_CALL_MAX_RESPONSE_BYTES` | 応答本文 | 65536 |
| `NYXIS_OUTBOX_INTERVAL_SECONDS` | 内部ループの間隔 | 5 |
| `NYXIS_OUTBOX_MAX_ATTEMPTS` | 最大試行回数 | 8 |
| `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS` | バックオフの底(`base × 2^attempts`) | 10 |

## 6. 定理への追加

`Nyxis.Runtime.authorization_safety` の定理文は変えず、(6)(7) と同じ形の項を足す。

- **(8)** 記録されたすべての呼び出し(`Payload.call`。sync・async とも)は、その要求の主体と生成値について対象の行の
  読み取りと同じ判定材料で permit され、送り先・メソッド・パスは正本の宣言、本文は対象行の宣言された列と
  `context.values` の提案値から nyxis が決めたものである。アウトボックスの各行はこの記録そのものである。
- **(9)** ハンドラに渡った応答の値(`Outcome.called` / `calledError`)は、その呼び出しの結果の列(`Runtime.Externals`
  を `Option String` から応答の和型 `Authz.ExternalResult` へ広げた)から来る任意の値であり、判定(発行する操作・記録)を変えない
  (現行の `Authz.step_external_indep` の拡張)。応答の値が DB に入る経路は、ハンドラが別アクションで提案する
  `values` だけで、(1) の判定を通る。

純粋モデルの変更点: `Db.EffectKind` に `call (dest method path : …) (columns : List Column) (mode : CallMode)`、
`Authz.Payload` に `call`、`Db.Outcome` に `called` / `calledError`、`Runtime.Externals` の要素型。接続コードの
証明済み範囲(`StagedRun.external`: 記録された内容についてだけ `Driver.external` を呼ぶ)は async の INSERT と
`Outbox.loop` にも同じ形で述べる(ループが送るのはアウトボックス行の内容だけ)。`Outbox.loop` の外界動作(間隔・
再試行)は `Jobs.loop` と同じく未証明で Assumption 1(接続コード)に残す。

## 7. 未決

- **受信側**(外部サービスからの callback / inbound webhook)。JWT を持たない要求の主体を、署名検証つきの
  「外部主体」として正本に宣言する形が候補。送信側を固めてから扱う。
- 問い合わせ文字列を要する API(`GET /v1/search?q=…`)。本文で代替できないので、`{values.q}` のような安全な埋め込みを
  後で検討する。
- アウトボックスの状態をハンドラが読む効果(D8 の保留)。
- 外部からの値の型のうち、Cedar のレコード型で表せないもの(配列の配列、`null` と欠落の区別)。
