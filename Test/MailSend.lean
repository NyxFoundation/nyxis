import Nyxis.Internal.MailSend

/-!
# Test.MailSend — メールのメッセージ構成の単体検査

`Nyxis.Internal.MailSend` の純粋関数(base64 とその折り返し、件名の encoded-word、メッセージの行長)を `#guard` で
検査する。符号化した件名と本文が、ここで定義する復号器で元に戻ることも確かめる。実サンプルに対する統合検査は
`scripts/check-team-docs.py`(Mailpit が復号する)。
-/

namespace Test.MailSend

open Nyxis.Internal.MailSend

private def config : Config := ⟨"smtps://relay.example:465", "from@example.test"⟩

/-- 行(CRLF 区切り)の最大バイト数。 -/
private def maxLineBytes (s : String) : Nat :=
  (s.splitOn "\r\n").foldl (fun m l => max m l.utf8ByteSize) 0

/-- 検査用の base64 の復号(`=` の詰め物と折り返しの CRLF は読み飛ばす)。 -/
private def unbase64 (s : String) : ByteArray := Id.run do
  let table := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList
  let mut out := ByteArray.empty
  let mut acc := 0
  let mut bits := 0
  for c in s.toList do
    if let some v := table.findIdx? (· == c) then
      acc := acc * 64 + v
      bits := bits + 6
      if bits ≥ 8 then
        bits := bits - 8
        out := out.push (acc / 2 ^ bits).toUInt8
        acc := acc % 2 ^ bits
  return out

/-- 検査用: `subjectField` の値を復号する(素の件名、または CRLF + SP で畳んだ UTF-8 の B の encoded-word の並び。
    各語はそれだけで UTF-8 として復号できなければならない — 語が文字の途中で切れていれば U+FFFD になる)。 -/
private def decodeSubject (field : String) : String :=
  let words := (String.ofList (field.toList.drop 9)).splitOn "\r\n "
  if field.startsWith "Subject: =?UTF-8?B?" then
    String.join (words.map fun w =>
      (String.fromUTF8? (unbase64 (String.ofList ((w.toList.drop 10).dropLast.dropLast)))).getD "�")
  else String.join words

/-- 検査用: メッセージの本文(空行の後の base64)を復号する。 -/
private def decodeBody (m : String) : Option String :=
  match m.splitOn "\r\n\r\n" with
  | [_, body] => String.fromUTF8? (unbase64 body)
  | _ => none

/-- 件名から除かれる文字(改行・制御文字)を除いた値。 -/
private def cleaned (s : String) : String := String.ofList (s.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127)

private def asciiLong : String := String.ofList (List.replicate 300 'x')
private def jpBody : String := String.join (List.replicate 60 "あいうえお、これは長い本文の一部です。")
private def jpSubject : String := String.join (List.replicate 12 "件名の例")
-- 1・3・4 バイトの文字が混ざる(塊の上限の手前で次の文字が溢れる場合を通る)。
private def mixedSubject : String := "a" ++ String.join (List.replicate 20 "件😀")

-- base64 は RFC 4648 のとおり(既知のベクトル)。復号器はその逆。
#guard base64 "".toUTF8 == ""
#guard base64 "f".toUTF8 == "Zg=="
#guard base64 "fo".toUTF8 == "Zm8="
#guard base64 "foobar".toUTF8 == "Zm9vYmFy"
#guard base64 "a1 body\r\n".toUTF8 == "YTEgYm9keQ0K"
#guard ["", "f", "fo", "foo", jpBody, mixedSubject].all fun s => String.fromUTF8? (unbase64 (base64 s.toUTF8)) == some s
-- 折り返し: 76 文字ごとに CRLF(最後の行以外はちょうど 76 文字)。CRLF を除けば折り返さない base64 と同じ。
#guard ((base64 jpBody.toUTF8 (wrap := 76)).splitOn "\r\n").dropLast.all (·.length == 76)
#guard String.join ((base64 jpBody.toUTF8 (wrap := 76)).splitOn "\r\n") == base64 jpBody.toUTF8
#guard base64 "foobar".toUTF8 (wrap := 76) == "Zm9vYmFy"

-- 件名: 印字可能な ASCII で `Subject: ` の行が 78 文字以内ならそのまま(Mailpit も素の件名を返す)。空の件名も壊れない。
#guard subjectField "a1" == "Subject: a1"
#guard subjectField "" == "Subject: "
#guard subjectField (String.ofList (List.replicate 69 'y')) == "Subject: " ++ String.ofList (List.replicate 69 'y')
#guard (subjectField (String.ofList (List.replicate 70 'y'))).startsWith "Subject: =?UTF-8?B?"
-- 改行と制御文字は除く(ヘッダの注入にならない)。
#guard subjectField "hello\r\nBcc: evil@example.com" == "Subject: helloBcc: evil@example.com"
-- `=?` を含む件名は、encoded-word と読まれないように符号化する(RFC 2047 §7)。
#guard (subjectField "=?UTF-8?B?Zm9v?=").startsWith "Subject: =?UTF-8?B?"
-- 長い・非 ASCII の件名は encoded-word。最初の語は `Subject: ` の行に、以降は継続行(SP 始まり)に置き、各行は
-- 76 バイト以下。復号すると(改行と制御文字を除いた)元の件名に戻る。
#guard ((subjectField asciiLong).splitOn "\r\n").length > 1
#guard ((subjectField jpSubject).splitOn "\r\n").all fun l =>
  l.startsWith "Subject: =?UTF-8?B?" || l.startsWith " =?UTF-8?B?"
#guard [asciiLong, jpSubject, mixedSubject, "件名", "hello\r\n件名", "=?UTF-8?B?Zm9v?=", "a1", ""].all fun s =>
  maxLineBytes (subjectField s) ≤ 76 && decodeSubject (subjectField s) == cleaned s
-- 塊分けは文字の境界を跨がない(最初の塊は 39 バイト、以降は 45 バイト以下で、連結すると元に戻る)。
#guard [jpSubject, mixedSubject].all fun s =>
  let chunks := chunkByBytes s 39 45
  chunks.length > 1 && (chunks.headD "").utf8ByteSize ≤ 39 && chunks.all (·.utf8ByteSize ≤ 45) &&
    String.join chunks == s

-- メッセージは 7 bit で、各行は 76 バイト以下。
#guard [("a1", "a1 body"), (jpSubject, jpBody), (asciiLong, asciiLong)].all fun (s, b) =>
  let m := message config "to@example.test" s b
  maxLineBytes m ≤ 76 && m.toList.all (·.toNat < 128)
-- 本文は crlf 正規化した本文に末尾 CRLF を付けたものの base64(Mailpit の Text はこれを復号した値)。
#guard (message config "to@example.test" "a1" "a1 body").endsWith
  "Content-Transfer-Encoding: base64\r\n\r\nYTEgYm9keQ0K\r\n"
#guard decodeBody (message config "to@example.test" jpSubject jpBody) == some (jpBody ++ "\r\n")
#guard decodeBody (message config "to@example.test" "s" "line1\rline2\n\nline3\r\n\x00end") ==
  some "line1line2\r\n\r\nline3\r\nend\r\n"
#guard decodeBody (message config "to@example.test" "s" "") == some "\r\n"

end Test.MailSend
