/-! 承認済みの curl を、設定を標準入力(`--config -`)で渡して起動する共通部(コア専用、未証明。A2/A4 の curl)。
`StorageSign`・`MailSend`・`CallSend` が使う。資格情報と要求の値は設定の中にだけ置き、プロセスの引数には
現れない。診断(stderr)は捨て、子プロセスは必ず回収する。 -/
namespace Nyxis.Internal.CurlStdin

/-- 標準入力に設定を書く。handle の所有権を受け取り、戻るときに参照が無くなって閉じる(設定の終わりを curl に伝える。
    閉じなければ curl は設定の続きを待ち続ける)。 -/
private def feed (stdin : IO.FS.Handle) (input : String) : IO Bool := do
  try
    stdin.putStr input
    stdin.flush
    pure true
  catch _ => pure false

/-- `curl <args>` を起動し、標準入力に `input` を渡して、終了コードと標準出力を返す。 -/
def run (args : Array String) (input : String) : IO (UInt32 × String) := do
  let spawned ← IO.Process.spawn {
    cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .null }
  -- 元の子プロセスの値を以後参照しない(その stdin の参照が残ると handle が閉じない)。
  let (stdin, child) ← spawned.takeStdin
  let fed ← feed stdin input
  try
    let output ← child.stdout.readToEnd
    let code ← child.wait
    return (if fed then code else 1, output)
  catch _ =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    return (1, "")

/-- curl の設定の引用符つきの値にする(`\` と `"` と改行を逃がす)。 -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n" else if c == '\r' then "\\r"
    else c.toString) ++ "\""

end Nyxis.Internal.CurlStdin
