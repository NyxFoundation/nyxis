import TeamDocs.Handlers

/-!
# TeamDocs.Jobs — 2 つめの公式サンプルの定期処理

nyxis の定める型 `Nyxis.Runtime.Job`(= `Generated → Handler Unit`。ハンドラと同じく、効果は認可層へのアクション
呼び出しだけ)で書く。実起動(`TeamDocs.Server` → `Nyxis.Internal.ApprovedServer.serve`)が固定間隔(コア設定
`NYXIS_JOB_INTERVAL_SECONDS`)に、サービス主体(`Service::"<NYXIS_SERVICE_PRINCIPAL>"`。JWT ではない)で
HTTP の要求と同じ段階的な経路に流す。何ができるかはポリシー(`policies.cedar` の `principal is Service` の条項)が決める:
送信済みでない通知の一覧と、宛先の利用者がいま文書を読める通知の送信、送信済みへの更新だけ。
-/

namespace TeamDocs

open Cedar.Spec
open Nyxis
open Nyxis.Authz

/-- 送信済みでない通知を集め、ポリシーが許すものだけを送って送信済みにする(共有時に宛先が読めず送れなかった通知は、
    後に共有されれば送られる)。拒否された通知はそのまま残る。 -/
def notifyPending : Nyxis.Runtime.Job := fun _ => do
  let listed ← Handler.callList (act "listNotifications") { filters := [⟨"sent", .eq, boolCell false⟩] }
  match listed with
  | .list rows _ =>
    for kv in rows do
      let sent ← Handler.callAction (act "sendNotification") kv.1
      match sent with
      | .ok none =>
        let _ ← Handler.callAction (act "markNotificationSent") kv.1 (rowOf [("sent", some (boolCell true))])
        pure ()
      | _ => pure ()
  | _ => pure ()

/-- このアプリの定期処理。 -/
def jobs : List Nyxis.Runtime.Job := [notifyPending]

end TeamDocs
