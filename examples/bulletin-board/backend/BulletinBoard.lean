import BulletinBoard.Approved
import BulletinBoard.Handlers
import BulletinBoard.App
import Nyxis.AppCheck

/-!
# BulletinBoard — nyxis 上のサンプルアプリ(掲示板)のバックエンド

公開済み投稿は誰でも読め、下書きは作者と管理者だけが読める。認証済みユーザーは投稿を作成でき、
編集・削除・公開は作者と管理者だけができる。管理者権限の付与・剥奪は管理者だけができる。
画面は `../frontend/` の公式フロントエンドが担い、このパッケージは HTTP API だけを持つ。

- `BulletinBoard.Approved` — 人間が承認する正本 `schema.cedarschema` と `policies.cedar` の宣言 `BulletinBoard.Approved.sources`。
- `BulletinBoard.Handlers` — 各エンドポイントのハンドラ(`Nyxis.Handler` で書く)とルーティング `BulletinBoard.router`。
- `BulletinBoard.App` — 宣言とルーティングを組んだアプリケーション `BulletinBoard.app`(`BulletinBoard.schema` / `policies` は宣言の別名)。
- 起動処理は監査済みのこのモジュールを読み込む `Main.lean` に置く。

アプリケーション側のコードは `BulletinBoard/` の Lean ファイルで、型の外へ出る語(`unsafe` / `implemented_by` / `extern` / `sorry`)を
含まない(`scripts/check-handler-effects.sh` が grep で確かめる)。
末尾の `nyxis_check_app` は、全アプリモジュールの定義と属性をビルド時に監査する。
新しいアプリモジュールは必ずこのファイルから import し、検査の後には宣言を置かない。
-/

nyxis_check_app
