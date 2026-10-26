import Nyxis.Internal.StorageSign
import Nyxis.Internal.MailSend
import Nyxis.Internal.CallSend

/-! 宣言された外部効果の実行(Assumption 1・2。コア専用、未証明)。

認可層が記録した外部効果の内容(`Authz.Payload`)についてだけ、接続層(`PostgresRun.runStaged`)が種類に応じて
Storage への発行(`StorageSign`)・メールの送信(`MailSend`)・外部 API の `sync` の呼び出し(`CallSend`)を行う。設定(`Config`)は
コア設定で、要求のどの項目からも決めない。設定の無い種類の効果は実行できず例外(要求全体が 503)。`async` の呼び出しは
接続層がアウトボックス(`Nyxis.Internal.Outbox`)に書き、ここには来ない。 -/
namespace Nyxis.Internal.ExternalSend

/-- 外部効果の設定。無い項目の効果は 503 になる。 -/
structure Config where
  /-- Supabase Storage。 -/
  storage : Option StorageSign.Config := none
  /-- メールの中継と差出人。 -/
  mail : Option MailSend.Config := none
  /-- 外部 API の送り先ごとの認証ヘッダと上限。 -/
  calls : Option CallSend.Config := none

/-- 記録された内容を実行する。署名付き URL の発行は結果の URL(`none` はオブジェクトが無い)、メールは `none`
    (結果の値は無い)、`sync` の呼び出しは応答(`called` / `calledError`)。`async` の呼び出しはここでは送らない: 接続層
    (`PostgresRun.driver`)が要求のトランザクションでアウトボックスに書く(`Nyxis.Internal.Outbox.enqueue`)ので、
    ここに届くことは無い(例外)。 -/
def send (config : Config) : Authz.Payload → IO Authz.ExternalResult
  | .upload object => sign true object
  | .download object => sign false object
  | .mail recipient subject body => do
    let some mail := config.mail | throw (IO.userError "mail is not configured")
    MailSend.send mail recipient subject body
    pure .none
  | .call destination method url body mode =>
    match mode with
    | .async => throw (IO.userError "async calls are written to the outbox by the connection layer")
    | .sync timeout response => do
      let some calls := config.calls | throw (IO.userError "external api calls are not configured")
      CallSend.call calls destination method url body timeout response
where
  sign (upload : Bool) (object : String) : IO Authz.ExternalResult :=
    match config.storage with
    | some storage => do
      match ← StorageSign.sign storage upload object with
      | some url => pure (.signed url)
      | none => pure .none
    | none => throw (IO.userError "storage is not configured")

end Nyxis.Internal.ExternalSend
