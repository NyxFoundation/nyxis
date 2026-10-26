import Nyxis.Db
import Nyxis.Authz
import Nyxis.Handler
import Nyxis.Runtime
import Nyxis.Http
import Nyxis.CedarSchema
import Nyxis.CedarPolicy
import Nyxis.Build

/-!
# Nyxis

認可安全性が形式証明つきの、Lean 製の DB・ランタイム。`import Nyxis` でアプリケーションに見えるのは次のモジュール。

- `Nyxis.Db` — DB 層。テーブル・列・行、アクションの効果の宣言、DB 操作、DB の状態の純粋モデル。
- `Nyxis.Authz` — 認可層。主体・対象・効果を nyxis が決め、Cedar の判定が allow のときだけ効果を実行する。
- `Nyxis.Handler` — ハンドラの型。認可層へのアクション呼び出しだけを効果として持つ。HTTP のリクエスト・レスポンス・
  ルーティングの型もここにある。
- `Nyxis.Runtime` — ランタイムの意味論と認可安全性の定理 `Nyxis.Runtime.authorization_safety`。
- `Nyxis.Approved` — アプリケーションが宣言した承認済み正本(スキーマとポリシー)の対と、その宣言から組んだ App に
  ついての定理 `Nyxis.Approved.authorization_safety`。
- `Nyxis.Http` — `Std.Http` でランタイムを公開するための共通部分(パス・本文の上限・レスポンスの変換・起動)。
- `Nyxis.CedarLex` / `CedarSchema` / `CedarPolicy` — Cedar の文書(`.cedarschema` / `.cedar`)から `Authz.Schema` と
  cedar-spec の `Cedar.Spec.Policies` を構成し、効果の宣言を検査する。
- `Nyxis.Build` — ビルド時に文書を読んで定義するコマンド `nyxis_approved`(および `nyxis_schema` / `nyxis_policies`)。
  構成に失敗すればビルドが失敗する。

`import Nyxis` に含まれないもの:

- `Nyxis.ReadSafety` — ハンドラに渡る行の出所についての系(接続層の証明が参照する)。
- `Nyxis.AppCheck` — アプリケーションの最終モジュールが呼ぶ監査 `nyxis_check_app`(`ASSUMPTIONS.md` A7)。
- `Nyxis.Internal.*` — 接続コード(JWT の検証、PostgreSQL、HTTP の入口、CORS、実起動 `ApprovedServer`)。
  アプリケーションからの import は監査が拒む。起動処理だけが監査の後に import する。
-/
