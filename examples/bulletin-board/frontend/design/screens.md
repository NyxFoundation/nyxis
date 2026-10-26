# 画面一覧 — Nyxis 公式サンプル(掲示板)フロントエンド

実装後に「この一覧の各画面に到達できること」を機械的に検査するための正本。画面 ID と状態 ID は一意。
実装では各画面のルート要素に `data-screen="<画面ID>"`、主要な状態に `data-state="<状態ID>"` を必ず付ける(`README.md` の U1)。機械検査はこの属性で到達を判定する。

## 画面に出す言葉と、技術的な意味

画面には技術用語を出さない。画面の言葉と、ポリシー・HTTP 上の意味の対応は次のとおり。

| 画面の言葉 | 意味 |
|---|---|
| ゲスト | 匿名。JWT が無い、または検証に失敗したリクエストの主体。期限切れの JWT も同じ |
| ログイン中 | 認証済みで、自分の利用者行(`User`)が登録済み |
| 「あなた」タグ | その投稿の `author` が自分(作者) |
| 管理者 | 利用者行の `admin` が true |
| 利用登録まだ | 有効な JWT を持つが、利用者行が無い(未登録) |
| 公開中 / 下書き | `published` が true / false |
| 「見られません」「できません」の朱い印 | 403。ポリシーが permit しなかった(認可により拒否)。投稿の読み取り・編集・削除は、行が無いときもポリシーが行の属性を評価できず 403 になる(存在を漏らさない。下の「403 と 404 の順序」) |
| 「公開しました」「保存しました」「できました」の緑の印 | 2xx。ポリシーが permit し、効果が実行された |
| 見つかりません | 404。行が無い(ルートが無い場合も含む)。存在しない投稿への読み取り・編集・公開・削除は管理者でも 403。利用者の読み取り・管理者の付与は、認可された要求で行が無ければ 404 |
| 入力をたしかめる(黄色の下線と一文) | 400。本文が読めない・必須項目が無い |
| すでにあります | 409。既に存在する ID、既に登録済み |
| つながりません(黒い帯) | 503 または通信失敗 |
| くわしく | 折りたたみ。開くと状態コード・アクション名・ポリシー ID を 1 行で出す(技術者向け) |

### 403 と 404 の順序(バックエンドで確認済み。`README.md` Q5・Q6)

- `GET /posts/{id}`・`PATCH /posts/{id}`・`publish`/`unpublish`・`DELETE /posts/{id}` は、行が無くても 404 ではなく **403**。ポリシー `read-published-post` / `read-draft-post` / `manage-post` が行の属性(`published`・`author`)を見るので、行が無いと評価できず deny になる(存在を漏らさないための設計)。
- 管理者も例外ではない。`manage-post` は `resource.author == principal || principal.admin` の左辺で存在しない行の属性を参照すると error → deny になるため、編集・公開・削除も **403**。読み取りも管理者を含め **403**。
- `PUT /users/{id}/admin`(`setAdmin`)と `GET /users/{id}`(`readUser`)は、認可された要求なら対象の利用者行が無い場合に **404**。認可されない要求は **403**。

したがって存在しない投稿の読み取りは `denied` / `loadDenied`、操作は `actionDenied` / `saveDenied` / `publishDenied` になる(管理者を含む)。「見られません」の紙は存在を断定しない(タグを出さず、一文も「存在しないか、下書きです。」で始める)。

API の対応(現行は `backend/BulletinBoard/Handlers.lean` の表。追加予定は `README.md` Q1〜Q3)。

| 画面の操作 | API | アクション |
|---|---|---|
| 投稿の一覧 | `GET /posts`(追加予定) | `listPosts`(読める行だけを返す。403 にはならない) |
| 投稿を開く | `GET /posts/{id}` | `readPost` |
| 投稿 → 保存 | `POST /posts/{id}` | `createPost` |
| 編集 → 保存 | `PATCH /posts/{id}` | `editPost` |
| 公開する / 下書きにもどす | `POST /posts/{id}/publish` / `POST /posts/{id}/unpublish` | `publishPost` |
| 削除 → 消す | `DELETE /posts/{id}` | `deletePost` |
| 管理者にする / 管理者を外す | `PUT /users/{id}/admin` | `setAdmin` |
| 利用登録(ログイン時に自動) | `POST /users/{id}`(追加予定。自分の ID のみ。201、登録済みは 409) | `registerUser` |
| 自分・ほかの人を調べる | `GET /users/{id}`(追加予定。本人と管理者。200 で `{ "admin": bool }` 相当、行が無ければ 404、他人の行を本人以外が読むと 403) | `readUser` |

## 画面の総覧

| ID | 画面名 | 画面の見出し | 想定ルート | 到達方法 | 模型 |
|---|---|---|---|---|---|
| S1 | PostList | ホーム | `/` | 初期表示、メニューの「ホーム」 | `post-list-anonymous.png`, `post-list-admin.png`, `mobile-post-list.png` |
| S2 | PostDetail | (投稿の題名) | `/posts/[id]` | 一覧の題名、「IDで開く」、URL 直打ち | `post-detail-author.png`, `post-detail-denied.png`, `mobile-post-detail-denied.png` |
| S3 | PostCreate | 投稿 | `/posts/new` | メニュー・一覧の「投稿」 | `post-create.png` |
| S4 | PostEdit | 編集 | `/posts/[id]/edit` | 投稿の「編集」、URL 直打ち | `post-edit.png` |
| S5 | Login | Nyxis 掲示板 | `/login` | 「Googleでログイン」。`?next=` で戻り先を持つ | `login.png` |
| S6 | AuthCallback | ログインしています | `/auth/callback` | Google 認証からの戻り。直接開くと S5 へ | `auth-callback.png` |
| S7 | Me | あなた | `/me` | 右上の人物マーク | `me.png` |
| S8 | AdminUsers | 管理 | `/admin` | メニューの「管理」(管理者だけに出る)、S7 の「ためす」、URL 直打ち | `admin-users.png` |
| S9 | NotFound | 見つかりません | 上記以外のルート | URL 直打ち | なし(部品 P3 の「見つかりません」を全幅で置く) |

`/posts/new` は静的ルートとして `/posts/[id]` より優先する。投稿 ID は UUID なので `new` と衝突しない。

## S1 PostList(ホーム)

- ルート: `/`
- 目的: いまの人が読める投稿だけを並べる。ほかの人の下書きは一覧に現れない(API が返さない)。
- 内容: 見出し「ホーム」と件数、番号付きの行(題名、公開中/下書きタグ、「あなた」タグ、本文の 1 行、書いた人の ID 先頭 8 桁)。日付は無い(スキーマに無い)。末尾に「IDで開く」入力。説明文は置かない。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `PostList.loading` | 全員 | 取得中 | 行のシルエット 3 本 |
| `PostList.anonymous` | ゲスト | 取得成功 | 公開中の行だけ。「投稿」は出さない。右上は「ゲスト」と「Googleでログイン」 |
| `PostList.user` | ログイン中 | 取得成功 | 公開中 + 自分の下書き(破線の「下書き」タグ + 「あなた」タグ)。「投稿」ボタンとメニュー |
| `PostList.admin` | 管理者 | 取得成功 | 公開中 + 全員の下書き。メニューに「管理」 |
| `PostList.unregistered` | 利用登録まだ | 取得成功 | `PostList.user` と同じ一覧。右上の人物マークが「利用登録まだ」(黄の輪郭) |
| `PostList.empty` | 全員 | 読める行が 0 件 | 破線の枠に「まだ投稿がありません」 |
| `PostList.offline` | 全員 | 503 / 通信失敗 | 見出しの下に黒い帯「つながりません」+「もう一度」 |
| `PostList.denied` | 全員 | 403(通常は起きない) | 一覧の場所に朱い印「見られません」 |

- 表示する操作: 投稿を開く(S2)、投稿(S3、ゲストには出さない)、IDで開く(S2)、もう一度。
- エラー状態: 上記 `offline` / `denied`。ID が UUID 形式でないときは送らずに入力欄を黄色にして「IDをたしかめてください」。
- 通知: ログアウト直後は黒い通知「ログアウトしました」、削除直後は「消しました」。

## S2 PostDetail(投稿)

- ルート: `/posts/[id]`
- 目的: 投稿を読む。書いた人と管理者には編集・公開する/下書きにもどす・削除のボタンを出す。
- 内容: 白い紙(上辺の太い罫)にタグ、ID、題名、本文。紙の下にボタン列と「リンクをコピー」。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `PostDetail.loading` | 全員 | 取得中 | 紙の中にシルエット |
| `PostDetail.published.anonymous` | ゲスト | 公開中、200 | 読むだけ。ボタン列なし |
| `PostDetail.published.user` | ログイン中(書いた人ではない) | 公開中、200 | 読むだけ。「リンクをコピー」だけ出す |
| `PostDetail.draft.author` | 書いた人 | 下書き、200 | ボタン列: 編集(S4)・公開する・削除。模型 `post-detail-author.png` |
| `PostDetail.published.author` | 書いた人 | 公開中、200 | ボタン列: 編集・下書きにもどす・削除 |
| `PostDetail.any.admin` | 管理者 | 200 | 書いた人と同じボタン列。「あなた」タグは自分の投稿にだけ付く |
| `PostDetail.confirmDelete` | 書いた人・管理者 | 「削除」を押した | 朱の枠「この投稿を消しますか?」[消す][やめる]。ブラウザの confirm は使わない |
| `PostDetail.denied` | 全員 | 403。ほかの人の下書き(ゲスト・ログイン中・利用登録まだ)、または存在しない ID(管理者を含む全員) | 紙の中は灰色のシルエット(固定の幅)に朱い印「見られません」。タグは出さない(存在を断定しない)。下に一文「存在しないか、下書きです。下書きは、書いた人と管理者だけが見られます。」、[Googleでログイン](ゲストのみ)[ホームにもどる]、「くわしく」。模型 `post-detail-denied.png` |
| `PostDetail.notFound` | 全員 | 404(通常は起きない。存在しない ID は 403 → `denied`) | 破線の枠「見つかりません」+[ホームにもどる] |
| `PostDetail.offline` | 全員 | 503 / 通信失敗 | 黒い帯「つながりません」+「もう一度」 |
| `PostDetail.actionDenied` | 書いた人・管理者 | 公開/下書き/削除が 403(書いた人・管理者とも、ほかで消された投稿でも 403) | ボタン列の横に朱い印「できません」。本文は残す |
| `PostDetail.actionConflict` | 書いた人・管理者 | 409 | ボタン列の横に「すでに変わっています」+[読み直す] |
| `PostDetail.actionNotFound` | 書いた人・管理者 | 404 の汎用表示用。現行の投稿 API では到達しない(ほかで消された投稿も 403 → `actionDenied`) | 破線の枠「見つかりません」 |

- 操作後: 公開する / 下書きにもどす は 204 → 再取得 → 紙の上に緑の印「公開しました」「下書きにしました」(2 秒で消える)。削除は 204 → S1 へ + 通知「消しました」。

## S3 PostCreate(投稿)

- ルート: `/posts/new`
- 目的: 題名・本文を書き、下書き/公開するを選んで保存(`POST /posts/{id}`)。ID はクライアントが生成(UUID v4)し、紙の下に小さく出す。
- 内容: 見出し「投稿」。紙の中に題名(大きい入力、下線)、本文、切替[下書き|公開する]、[やめる][保存]、ID と「新しいIDに」。説明文は置かない。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `PostCreate.anonymous` | ゲスト | — | 紙の代わりに一文「投稿するにはログインが必要です」+[Googleでログイン](`?next=/posts/new`) |
| `PostCreate.editing` | ログイン中・管理者 | — | 入力可能。模型 `post-create.png` |
| `PostCreate.unregistered` | 利用登録まだ | — | 入力可能。右上の人物マークは「利用登録まだ」。送信は許す(`README.md` Q4) |
| `PostCreate.invalid` | ログイン中 | 題名または本文が空 | 送らずに、その入力欄を黄色にして「題名を入れてください」「本文を入れてください」 |
| `PostCreate.submitting` | ログイン中 | 送信中 | 「保存」を押せなくする |
| `PostCreate.badRequest` | ログイン中 | 400 | 題名欄を黄色にしてサーバの文言を一文で。入力は保持 |
| `PostCreate.conflict` | ログイン中 | 409 | ID 行に取り消し線と「このIDはすでにあります」+[新しいIDに] |
| `PostCreate.denied` | ログイン中(ログイン切れなど) | 403 | 紙の上に朱い印「できません」+ 一文「ログインしなおしてください」 |
| `PostCreate.offline` | ログイン中 | 503 / 通信失敗 | 黒い帯「つながりません」+「もう一度」。入力は保持 |

- 成功: 201 → S2 へ + 緑の印「保存しました」(公開を選んだときは「公開しました」)。

## S4 PostEdit(編集)

- ルート: `/posts/[id]/edit`
- 目的: 題名・本文の編集(`PATCH`)と、公開する/下書きにもどす(`publish`/`unpublish`)。別の API なので、紙(題名・本文)と、その下の「いまは 下書き [公開する]」の行に分ける。削除は S2 に置く。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `PostEdit.loading` | 全員 | 取得中 | 紙の中にシルエット |
| `PostEdit.editing.author` | 書いた人 | 200 | 模型 `post-edit.png` |
| `PostEdit.editing.admin` | 管理者 | 200 | 同じ。「あなた」タグは付かない |
| `PostEdit.editing.nonAuthor` | ログイン中(書いた人ではない) | 公開中で 200 | 入力可能。見出しの横に薄い朱の印「できません(見込み)」は置かない。保存すると `saveDenied` |
| `PostEdit.anonymous` | ゲスト | 公開中で 200 | 一文「編集にはログインが必要です」+[Googleでログイン]。下書きなら `loadDenied` |
| `PostEdit.loadDenied` | 全員 | GET が 403(ほかの人の下書き、または存在しない ID。管理者は存在しない ID のときだけ) | S2 の `denied` と同じ紙・印・一文 |
| `PostEdit.notFound` | 全員 | 404 の汎用表示用。現行の投稿 API では到達しない(存在しない ID の取得は 403 → `loadDenied`、保存/公開/下書きにもどすも管理者を含め 403) | 破線の枠「見つかりません」 |
| `PostEdit.invalid` | 書いた人・管理者 | 題名・本文が空 | 入力欄を黄色にして一文。両方空のときは API に送らない |
| `PostEdit.saveDenied` | ログイン中 | PATCH が 403 | 紙の上に朱い印「できません」。入力は保持 |
| `PostEdit.publishDenied` | ログイン中 | publish/unpublish が 403 | 「いまは」の行に朱い印「できません」 |
| `PostEdit.badRequest` | 書いた人・管理者 | 400 | 入力欄を黄色にしてサーバの文言 |
| `PostEdit.conflict` | 書いた人・管理者 | 409 | 「すでに変わっています」+[読み直す] |
| `PostEdit.offline` | 全員 | 503 / 通信失敗 | 黒い帯「つながりません」+「もう一度」。入力は保持 |

- 成功: 保存は 204 → S2 へ + 緑の印「保存しました」。公開する / 下書きにもどす は 204 → 行のタグを更新 + 緑の印(画面に留まる)。

## S5 Login(ログイン)

- ルート: `/login`(`?next=<戻り先>`、`?error=<理由>`)
- 目的: Google OAuth(Supabase Auth)を始める。パスワードやマジックリンクの UI は無い。
- 内容: 朱の四角と「Nyxis 掲示板」、[Googleでログイン]、「ログインせずに見る」。それ以外の文は置かない。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `Login.anonymous` | ゲスト | — | 模型 `login.png` |
| `Login.alreadyLoggedIn` | ログイン中・管理者・利用登録まだ | — | 人物マークと「ログイン中です」+[ホームへ][ログアウト] |
| `Login.oauthError` | ゲスト | `?error=` あり | ボタンの上に一文「ログインできませんでした」。印は使わない |
| `Login.authOffline` | ゲスト | Supabase Auth に到達できない | 黒い帯「つながりません」+「もう一度」 |

- Google ボタンの意匠は Google のブランドガイドラインに従って実装する(`README.md` U5)。

## S6 AuthCallback(ログインしています)

- ルート: `/auth/callback`
- 目的: 認可コードをセッションに交換し、初回なら利用登録を行い、戻り先へ遷移する。
- 内容: 見出し「ログインしています」と、3 つの丸(Google / 利用登録 / ホームへ)を線でつないだ進み具合。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `AuthCallback.exchanging` | — | コード交換中 | 1 つめの丸が回転中 |
| `AuthCallback.authFailed` | ゲスト | 交換に失敗 | S5 へ遷移(`?error=`) |
| `AuthCallback.registering` | 利用登録まだ | `POST /users/{自分}` 送信中 | 2 つめの丸が回転中。模型 `auth-callback.png` |
| `AuthCallback.registered` | ログイン中 | 201 | 3 つめまで黒 → 戻り先へ |
| `AuthCallback.alreadyRegistered` | ログイン中 | 409 | 登録済みとして続行(失敗を見せない) |
| `AuthCallback.registerDenied` | 利用登録まだ | 403 | 2 つめの丸に朱い印「できません」+[もう一度][登録せずに続ける] |
| `AuthCallback.registerBadRequest` | 利用登録まだ | 400 | 同上(実装の不整合として) |
| `AuthCallback.registerOffline` | 利用登録まだ | 503 / 通信失敗 | 黒い帯「つながりません」+[もう一度][登録せずに続ける]。JWT は保持 |
| `AuthCallback.direct` | 全員 | 認可コードが無い | S5 へ遷移 |

- 戻り先は `?next=` から取り、無ければ `/`。外部 URL は受け付けない。

## S7 Me(あなた)

- ルート: `/me`
- 目的: 「いま誰として見ているか」「何ができるか」を言葉ではなく部品で示す。右上の人物マークの遷移先。
- 内容: 紙に大きな人物マーク、「ログイン中」、ID 全文と[コピー]、[ログアウト]。「できること」の 4 枚(公開中の投稿を見る / 投稿する / 自分の投稿を直す・公開する・消す / 管理者を決める)に緑の○か朱の×。「ためす」のボタン 2 つ。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `Me.loading` | — | 確認中 | 紙の中にシルエット |
| `Me.anonymous` | ゲスト | — | 破線の人物マークと「ゲスト」。ID 行は無い。できること: 見る○、ほか×。[Googleでログイン] |
| `Me.user` | ログイン中 | `GET /users/{自分}` が 200、admin false | 模型 `me.png` |
| `Me.admin` | 管理者 | 200、admin true | 朱の人物マークと「管理者」タグ。できること: すべて○、3 枚目は「みんなの投稿を直す・公開する・消す」 |
| `Me.unregistered` | 利用登録まだ | `GET /users/{自分}` が 404 | 黄の輪郭の人物マークと「利用登録まだ」+[利用登録する]。4 枚目は「?」 |
| `Me.expired` | ゲスト(ログイン切れ) | ローカルの JWT が期限切れ | `Me.anonymous` + 一文「ログインの期限が切れました」 |
| `Me.offline` | ログイン中 | `GET /users/{自分}` が 503 / 通信失敗 | ID は出し、4 枚目は「?」。黒い帯「つながりません」 |

- 表示する操作: コピー、ログアウト、利用登録する(利用登録まだ)、ためす(ほかの人の下書きを開く → S2 の `denied`、管理の画面を開く → S8)。

## S8 AdminUsers(管理)

- ルート: `/admin`
- 目的: ID で利用者を調べ、[管理者にする]/[管理者を外す]を押す(`PUT /users/{id}/admin`)。管理者でなくても開け、押すと朱い印になる。
- 内容: 見出し「管理」。ID 入力と[調べる]。結果の紙: 人物マーク、タグ(管理者 / なし)、ID、ボタン。説明文は置かない。

| 状態 ID | 誰 | 条件 | 表示 |
|---|---|---|---|
| `AdminUsers.admin` | 管理者 | — | 模型 `admin-users.png`(付与直後、緑の印「できました」) |
| `AdminUsers.nonAdmin` | ログイン中・利用登録まだ | — | 同じ画面。メニューに「管理」は出ない。押すと `denied` |
| `AdminUsers.anonymous` | ゲスト | — | 同じ画面 + 右上に「Googleでログイン」。押すと `denied` |
| `AdminUsers.lookupResult` | 管理者 | 200 | 結果の紙 |
| `AdminUsers.lookupNotFound` | 管理者 | 404 | 破線の枠「見つかりません」 |
| `AdminUsers.lookupDenied` | ログイン中(管理者でない) | 自分以外の ID で 403 | 結果の場所に朱い印「見られません」 |
| `AdminUsers.confirmSelfRevoke` | 管理者 | 対象が自分で「管理者を外す」 | 朱の枠「自分を管理者から外しますか?」[外す][やめる] |
| `AdminUsers.invalid` | 全員 | ID が UUID 形式でない | 入力欄を黄色にして「IDをたしかめてください」 |
| `AdminUsers.success` | 管理者 | 204 | 結果の紙に緑の印「できました」、タグとボタンを更新 |
| `AdminUsers.denied` | ログイン中・ゲスト | 403 | 結果の紙に朱い印「できません」 |
| `AdminUsers.notFound` | 管理者 | 404 | 破線の枠「見つかりません」 |
| `AdminUsers.badRequest` | 管理者 | 400 | 入力欄を黄色にしてサーバの文言 |
| `AdminUsers.offline` | 全員 | 503 / 通信失敗 | 黒い帯「つながりません」+「もう一度」 |

- 自分を外した直後は右上の人物マークを再確認し、メニューの「管理」を消す。

## S9 NotFound(見つかりません)

- ルート: 定義されていないルート全般(Next.js の not-found)。
- 表示: 通常のヘッダに、破線の枠「見つかりません」+[ホームへ]。

## 共通要素(すべての画面に出る)

### P1 Header(ヘッダと人物マーク)

左に朱の四角と「Nyxis 掲示板」、その右にメニュー(ホーム / 投稿 / 管理。選択中は下線 3px)。右に人物マーク(S7 へ)とログイン/ログアウト。下に 3px の罫。モバイル幅では 2 段に積む。

| 状態 ID | 表示 |
|---|---|
| `Header.checking` | 人物マークがシルエット |
| `Header.anonymous` | 破線の丸 + 「ゲスト」+[Googleでログイン]。メニューは「ホーム」だけ |
| `Header.user` | 黒い丸に ID 先頭 2 桁 + 「ログイン中」+「ログアウト」。メニュー: ホーム / 投稿 |
| `Header.admin` | 朱の丸に ID 先頭 2 桁 + 「管理者」タグ。メニュー: ホーム / 投稿 / 管理 |
| `Header.unregistered` | 黄の輪郭の丸 + 「利用登録まだ」。押すと S7 |
| `Header.adminUnknown` | 黒い丸 + 「ログイン中」(管理者かどうかの確認が `つながりません` のとき) |

ログアウト: Supabase のセッションを破棄 → `/` へ → 通知「ログアウトしました」。確認は挟まない。

### P2 Stamp(印)

結果を言葉の代わりに印で示す。斜め 7 度、二重線、太い文字。

| 状態 ID | 色 | 文言 | 使う場所 |
|---|---|---|---|
| `Stamp.denied.read` | 朱 | 見られません | 読めなかった紙の上(S2・S4 の読み込み、S8 の調べる) |
| `Stamp.denied.act` | 朱 | できません | 押した操作が 403 のとき、そのボタン列や紙の上 |
| `Stamp.ok.published` | 緑 | 公開しました | 公開した直後の紙の上 |
| `Stamp.ok.saved` | 緑 | 保存しました | 保存した直後 |
| `Stamp.ok.done` | 緑 | できました | 管理の操作など |

朱の印は消えない(ページを離れるまで)。緑の印は 2 秒で薄れて消える。印の下には、必要なときだけ一文(「存在しないか、下書きです。下書きは、書いた人と管理者だけが見られます。」)を置く。文はアクションごとに固定し、行の内容からは作らない(存在するかどうかも文に出さない)。

### P3 その他の状態

| 種類 | 状態 ID | 形 |
|---|---|---|
| 見つかりません | `State.notFound` | 破線の枠、中央に「見つかりません」 |
| つながりません | `State.offline` | 黒い帯、左に線が切れた電波のアイコン、右に[もう一度] |
| 入力をたしかめる | `State.invalid` | 入力欄の下線を黄色、背景を薄い黄色、下に一文 |
| すでにあります | `State.conflict` | ID に取り消し線、朱の文「このIDはすでにあります」、[新しいIDに] |
| たしかめる | `State.confirm` | 朱の枠に一文、[消す][やめる] |
| 通知 | `State.toast` | 黒い帯に緑のチェック。右上、数秒で消える。印で済むときは使わない |

### P4 タグ

公開中(緑の枠)、下書き(灰の破線枠)、あなた(青の枠)、管理者(朱の枠)。色だけに頼らず必ず文字を持つ。

## 検査用の到達性一覧

実装後の機械検査で、少なくとも次の組み合わせに到達できること。「誰」はテスト用の 3 ユーザー(書いた人・ほかの人・管理者)とゲストで作る。

| 画面 ID | 状態 ID | 誰 | 準備 |
|---|---|---|---|
| S1 | `PostList.anonymous` | ゲスト | 公開中 1 件以上 |
| S1 | `PostList.user` | 書いた人 | 自分の下書き 1 件以上 |
| S1 | `PostList.admin` | 管理者 | ほかの人の下書き 1 件以上 |
| S1 | `PostList.empty` | ゲスト | 公開中 0 件 |
| S1 | `PostList.offline` | ゲスト | バックエンド停止 |
| S2 | `PostDetail.published.anonymous` | ゲスト | 公開中の投稿 |
| S2 | `PostDetail.published.user` | ほかの人 | ほかの人の公開中の投稿 |
| S2 | `PostDetail.draft.author` | 書いた人 | 自分の下書き |
| S2 | `PostDetail.published.author` | 書いた人 | 自分の公開中の投稿 |
| S2 | `PostDetail.any.admin` | 管理者 | ほかの人の下書き |
| S2 | `PostDetail.confirmDelete` | 書いた人 | 削除を押す |
| S2 | `PostDetail.denied` | ゲスト、ほかの人 | ほかの人の下書きの ID |
| S2 | `PostDetail.denied` | ゲスト、管理者 | 存在しない ID(404 ではなく 403) |
| S2 | `PostDetail.offline` | ゲスト | バックエンド停止 |
| S3 | `PostCreate.anonymous` | ゲスト | — |
| S3 | `PostCreate.editing` | 書いた人 | — |
| S3 | `PostCreate.invalid` | 書いた人 | 題名を空で保存 |
| S3 | `PostCreate.conflict` | 書いた人 | 既存の ID で保存 |
| S3 | `PostCreate.offline` | 書いた人 | バックエンド停止 |
| S4 | `PostEdit.editing.author` | 書いた人 | 自分の投稿 |
| S4 | `PostEdit.editing.nonAuthor` | ほかの人 | ほかの人の公開中の投稿 |
| S4 | `PostEdit.loadDenied` | ほかの人 | ほかの人の下書き |
| S4 | `PostEdit.saveDenied` | ほかの人 | ほかの人の公開中の投稿で保存 |
| S4 | `PostEdit.publishDenied` | ほかの人 | ほかの人の公開中の投稿で下書きにもどす |
| S4 | `PostEdit.loadDenied` | 書いた人 | 存在しない ID(404 ではなく 403) |
| S5 | `Login.anonymous` | ゲスト | — |
| S5 | `Login.alreadyLoggedIn` | 書いた人 | — |
| S5 | `Login.oauthError` | ゲスト | `?error=access_denied` |
| S6 | `AuthCallback.registering` | 新しい人 | 初回ログイン |
| S6 | `AuthCallback.alreadyRegistered` | 書いた人 | 2 回目のログイン |
| S6 | `AuthCallback.registerOffline` | 新しい人 | 登録中にバックエンド停止 |
| S7 | `Me.anonymous` | ゲスト | — |
| S7 | `Me.user` | 書いた人 | — |
| S7 | `Me.admin` | 管理者 | — |
| S7 | `Me.unregistered` | 利用登録まだ | 利用者行を作らない |
| S8 | `AdminUsers.admin` | 管理者 | — |
| S8 | `AdminUsers.nonAdmin` | ほかの人 | — |
| S8 | `AdminUsers.anonymous` | ゲスト | — |
| S8 | `AdminUsers.success` | 管理者 | ほかの人を管理者にする |
| S8 | `AdminUsers.denied` | ほかの人 | 自分を管理者にしようとする |
| S8 | `AdminUsers.notFound` | 管理者 | 存在しない ID |
| S8 | `AdminUsers.confirmSelfRevoke` | 管理者 | 自分を外す |
| S9 | — | ゲスト | `/no-such-page` |
| P1 | `Header.anonymous` / `.user` / `.admin` / `.unregistered` | それぞれ | 全画面 |
| P2 | `Stamp.denied.read` / `Stamp.denied.act` / `Stamp.ok.published` | ゲスト、ほかの人、書いた人 | S2 の 403、S4 の保存 403、S2 の公開 |
