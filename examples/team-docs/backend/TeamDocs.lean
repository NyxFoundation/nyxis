import TeamDocs.Approved
import TeamDocs.Handlers
import TeamDocs.Jobs
import TeamDocs.App
import Nyxis.AppCheck

/-!
# TeamDocs — 2 つめの公式サンプル(team-docs)のバックエンド

組織(ワークスペース)に複数の利用者が owner / editor / viewer として属し、文書を組織内で共有し、個別の利用者にも
共有できる。文書は作成日時と更新日時を持ち、その値は nyxis が要求ごとに決める現在時刻である。
画面は `../frontend/` の公式フロントエンド(人間のデザイン提供後に作る)が担い、このパッケージは HTTP API だけを持つ。

- `TeamDocs.Approved` — 人間が承認する正本 `schema.cedarschema` と `policies.cedar` の宣言 `TeamDocs.Approved.sources`。
- `TeamDocs.Handlers` — 各エンドポイントのハンドラ(`Nyxis.Handler` で書く)とルーティング `TeamDocs.router`。
- `TeamDocs.Jobs` — 定期処理 `TeamDocs.jobs`(`Nyxis.Runtime.Job` で書く。送信済みでない通知の送信)。
- `TeamDocs.App` — 宣言とルーティングと定期処理を組んだアプリケーション `TeamDocs.app`(`TeamDocs.schema` / `policies` は宣言の別名)。
- 起動処理は監査済みのこのモジュールを読み込む `Main.lean` に置く。

アプリケーション側のコードは `TeamDocs/` の Lean ファイルで、型の外へ出る語(`unsafe` / `implemented_by` / `extern` / `sorry`)を
含まない。末尾の `nyxis_check_app` は、全アプリモジュールの定義と属性をビルド時に監査する。
新しいアプリモジュールは必ずこのファイルから import し、検査の後には宣言を置かない。
-/

nyxis_check_app
