import Nyxis.Runtime

/-! Application-independent pairing of the schema and policies declared by the application.
The build command constructs these values from two Cedar files. Human approval of those
files remains A6; this type does not certify that a human has approved arbitrary values.
Parsing, embedding and deployment wiring remain within the existing A4/A6/A7 boundary.
-/
namespace Nyxis

/-- Authorization inputs from the application's declared sources. No handler or IO is stored. -/
structure Approved where
  schema : Authz.Schema
  policies : Cedar.Spec.Policies

namespace Approved

/-- A router (and, optionally, periodic jobs) can supply behavior, but cannot replace this declaration's
    authorization inputs. -/
def app (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) : Runtime.App :=
  ⟨sources.schema, sources.policies, router, jobs⟩

theorem app_schema (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) :
    (sources.app router jobs).schema = sources.schema := rfl

theorem app_policies (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) :
    (sources.app router jobs).policies = sources.policies := rfl

/-- 日本語の読み下し: 任意の正本の宣言・型付きルータ・定期処理の列・初期Store・認証済み要求列(定期処理の起動を含む)に
ついて、宣言した正本から組んだAppが発行する操作は要求の主体とサーバー生成値(nyxis が要求ごとに決めた現在時刻と一意 ID)
に一致し、その正本の認可範囲内にある。
状態遷移はその操作列と整合する。ハンドラに渡った(主キー, 行)の組(読み取りの成功では呼び出しの主キーと
その行、一覧では返した各組)は、同じ要求が発行しその正本で認可されたその主キーの読み取りが、直前の状態で
指す行である。一覧の件数と返す行は、判定時の状態の対象テーブルの行のうち問い合わせの絞り込みに合い、その正本で
その主体に permit された行(候補)だけから決まる(件数は候補の数、返す行は候補を並べ替えてページを切ったもの。
`Runtime.ListResult`)。各操作を判定したアクションは、ハンドラの呼び出しのものか、その正本が宣言した連鎖の削除の
アクション(その宣言のテーブルの行の削除。`Authz.ActionOrigin`)である。記録された外部効果(添付の署名付き URL の
発行。メール送信。外部 API 呼び出し)は要求の主体と生成値について、その正本が効果を宣言したアクションで
対象の行について permit され、内容は nyxis が決めたもの(`Authz.ExternalAuthorized`)で、ハンドラに渡った署名付き URL には
その呼び出し(同じアクション・主キー・判定時の状態)の記録がある。記録された呼び出しの送り先・メソッド・URL・本文はその
正本の宣言(効果と `@external` の送り先)と対象の行と判定を通った提案値だけから決まり(`Authz.CallRecorded`)、ハンドラに
渡った外部 API の応答にはその呼び出しの認可済みの記録がある(応答の値は任意で判定を変えない)。認可前の内部取得や
生HTTP応答全体、URL や応答の中身はこの結論に含まない。
-/
theorem authorization_safety (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job)
    (store : Db.Store) (requests : List Runtime.AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧
        Authz.Authorized sources.schema sources.policies i)
    ∧ Authz.Coherent store ((Runtime.trace (sources.app router jobs) store requests).issued.map Prod.snd)
      (Runtime.trace (sources.app router jobs) store requests).store
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ kv ∈ c.entries,
          ∃ i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued ∧
            i.principal = r.principal ∧ i.generated = r.generated ∧
            Authz.Authorized sources.schema sources.policies i ∧ i.action = c.action ∧
            ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
          Runtime.ListResult sources.schema sources.policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued →
        ∃ cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests ∧
          ∃ c ∈ cs, Authz.ActionOrigin sources.schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧
          Authz.ExternalAuthorized sources.schema sources.policies e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
          ∃ e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧
            Authz.ExternalAuthorized sources.schema sources.policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external →
        Authz.CallRecorded sources.schema e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, c.outcome.isCalled = true →
          ∃ e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧
            Authz.ExternalAuthorized sources.schema sources.policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  Runtime.authorization_safety (sources.app router jobs) store requests

end Approved
end Nyxis
