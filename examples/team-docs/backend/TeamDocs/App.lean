import TeamDocs.Approved
import TeamDocs.Handlers
import TeamDocs.Jobs

/-!
# TeamDocs.App — 2 つめの公式サンプルの組み立て

承認済み正本の宣言 `TeamDocs.Approved.sources`(`schema.cedarschema` と `policies.cedar` からビルド時に構成)に
ハンドラのルーティング `TeamDocs.router` と定期処理 `TeamDocs.jobs`を組み合わせた `Nyxis.Runtime.App`。スキーマと
ポリシーは宣言から定義的に決まり、アプリケーション側が別の値を渡す口は無い。実起動(`TeamDocs.Server`)も同じ宣言から
`Deployment` を組み、ルータと定期処理だけを受け取る。この値はモデル検査(`TeamDocsTest`)で使う。
-/

namespace TeamDocs

/-- 宣言から構成したスキーマ。 -/
abbrev schema := Approved.schema

/-- 宣言から構成したポリシー。 -/
abbrev policies := Approved.policies

/-- 2 つめの公式サンプル。認可の入力は宣言そのもので、アプリケーション側はルータと定期処理だけを供給する。 -/
def app : Nyxis.Runtime.App := Approved.app router jobs

end TeamDocs
