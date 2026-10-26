import Nyxis.Build
import Nyxis.Runtime

/-! 2 つめの公式サンプル(team-docs)が所有する承認済み正本の宣言。実起動はこの宣言から組んだ App のルータだけを
受け付ける。解析と埋め込みは信頼するビルド時のコード(A4/A6)で、以下の等式と特殊化はカーネルが検査する。
これらの文は HTTP/JWT/SQL の対応や非干渉を証明するものではない。 -/
open Nyxis

namespace TeamDocs.Approved

nyxis_approved sources from "../schema.cedarschema" and "../policies.cedar"

abbrev schema := sources.schema
abbrev policies := sources.policies

/-- アプリケーションはルータと定期処理だけを供給する。認可の入力は固定された正本から来る。 -/
def app (router : Http.Router) (jobs : List Runtime.Job := []) : Runtime.App := sources.app router jobs

theorem app_schema (router : Http.Router) (jobs : List Runtime.Job := []) : (app router jobs).schema = schema := rfl
theorem app_policies (router : Http.Router) (jobs : List Runtime.Job := []) : (app router jobs).policies = policies := rfl

/-- 日本語の読み下し: 任意の型付きルータ・定期処理の列・初期Store・認証済み要求列(定期処理の起動を含む)について、
固定正本から組んだAppが発行する操作は要求の主体とサーバー生成値(nyxis が要求ごとに決めた現在時刻と一意 ID)
に一致し、その正本の認可範囲内にある。
状態遷移はその操作列と整合する。ハンドラに渡った(主キー, 行)の組(読み取りの成功では呼び出しの主キーと
その行、一覧では返した各組)は、同じ要求が発行しその正本で認可されたその主キーの読み取りが、直前の状態で
指す行である。一覧の件数と返す行は、判定時の状態の対象テーブルの行のうち問い合わせの絞り込みに合い、その正本で
その主体に permit された行(候補)だけから決まる(件数は候補の数、返す行は候補を並べ替えてページを切ったもの。
`Runtime.ListResult`)。各操作を判定したアクションは、ハンドラの呼び出しのものか、その正本が宣言した連鎖の削除の
アクション(その宣言のテーブルの行の削除。`Authz.ActionOrigin`)である。記録された外部効果(文書の添付の署名付き
URL の発行。通知のメール送信)は要求の主体と生成値について、この正本が `upload Doc` / `download Doc` /
`mail Notification(email; subject, body)` を宣言したアクションで対象の行について permit され、内容(パス、または宛先・
件名・本文)は nyxis がその行から決めたもの(`Authz.ExternalAuthorized`)で、ハンドラに渡った署名付き URL には
その呼び出しの記録がある。記録された外部 API 呼び出し(この正本はまだ宣言していないので記録は生じない)の内容は
その正本の宣言と対象の行と提案値だけから決まり(`Authz.CallRecorded`)、ハンドラに渡った外部 API の応答にはその呼び出しの
記録がある。定期処理の起動(主体はサービス主体)についても同じ。認可前の内部取得や生HTTP応答全体、URL や応答の中身は
この結論に含まない。
-/
theorem authorization_safety (router : Http.Router) (jobs : List Runtime.Job) (store : Db.Store)
    (requests : List Runtime.AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authz.Authorized schema policies i)
    ∧ Authz.Coherent store ((Runtime.trace (app router jobs) store requests).issued.map Prod.snd)
      (Runtime.trace (app router jobs) store requests).store
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ kv ∈ c.entries,
          ∃ i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued ∧
            i.principal = r.principal ∧ i.generated = r.generated ∧ Authz.Authorized schema policies i ∧
            i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
          Runtime.ListResult schema policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued →
        ∃ cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests ∧
          ∃ c ∈ cs, Authz.ActionOrigin schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
          ∃ e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external → Authz.CallRecorded schema e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, c.outcome.isCalled = true →
          ∃ e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  Nyxis.Approved.authorization_safety sources router jobs store requests

end TeamDocs.Approved
