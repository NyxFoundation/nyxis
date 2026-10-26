import Std.Sync.Mutex
import Nyxis.Internal.PostgresHttp
import BulletinBoard.App
import BulletinBoardTest.Fixture

/-!
# BulletinBoardTest.ServeFixture — プロセス内の DB で起動する検査用の実行ファイル

`BulletinBoard.app` を、`BulletinBoardTest.Fixture.store`(利用者 alice・bob・root(管理者)と、alice の公開済み投稿 pub1・
下書き draft1)を初期状態とするプロセス内の `Store` の上で、本体と同じ HTTP 入口(`PostgresHttp.handleAuthenticatedWith`)
に載せる。主体は常に匿名。`scripts/check-http.sh` がこれを起動し、HTTP の配線(メソッド・パス・本文がモデルに届き、
ハンドラのレスポンスがそのまま返ること)を確かめる。PostgreSQL・JWT は使わず、デプロイするものではない。
-/

def main (args : List String) : IO Unit := do
  let port : UInt16 ← match args.head? with
    | none => pure 8081
    | some s => match s.toNat? with
      | some n => if 0 < n && n ≤ 65535 then pure n.toUInt16 else throw (IO.userError s!"port out of range: {s}")
      | none => throw (IO.userError s!"port is not a number: {s}")
  let store ← Std.Mutex.new BulletinBoardTest.Fixture.store
  -- リクエストは Mutex の下で 1 つずつモデルを進めるので、処理された列は `Runtime.trace` と同じ形になる。
  let backend : Nyxis.Runtime.AuthenticatedRequest → IO Nyxis.Http.Response := fun r =>
    store.atomically do
      let run := Nyxis.Runtime.handleRequest BulletinBoard.app (← get) r
      set run.store
      pure run.result
  IO.println s!"nyxis fixture: listening on port {port}"
  Nyxis.Http.serve port (Std.Http.Server.Handler.ofFn
    (Nyxis.Internal.PostgresHttp.handleAuthenticatedWith (fun _ => pure .anonymous) Nyxis.Internal.Generated.fresh backend))
