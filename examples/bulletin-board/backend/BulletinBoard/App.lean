import BulletinBoard.Approved
import BulletinBoard.Handlers

/-!
# BulletinBoard.App — サンプルアプリの組み立て

承認済み正本の宣言 `BulletinBoard.Approved.sources`(`schema.cedarschema` と `policies.cedar` からビルド時に構成)に
ハンドラのルーティング `BulletinBoard.router` を組み合わせた `Nyxis.Runtime.App`。スキーマとポリシーは宣言から
定義的に決まり、アプリケーション側が別の値を渡す口は無い。実起動(`BulletinBoard.Server`)も同じ宣言から
`Deployment` を組み、ルータだけを受け取る。この値はモデル検査(`BulletinBoardTest`)で使う。
-/

namespace BulletinBoard

/-- 宣言から構成したスキーマ。 -/
abbrev schema := Approved.schema

/-- 宣言から構成したポリシー。 -/
abbrev policies := Approved.policies

/-- サンプルアプリ。認可の入力は宣言そのもので、アプリケーション側はルータだけを供給する。 -/
def app : Nyxis.Runtime.App := Approved.app router

end BulletinBoard
