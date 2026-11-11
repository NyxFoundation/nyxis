import Nyxis.Internal.MailSend

/-!
# Test.MailSend — unit checks for composing a mail message

Checks the pure functions of `Nyxis.Internal.MailSend` (base64 and its folding, the subject's encoded-words, the line
lengths of the message) with `#guard`. It also checks that an encoded subject and body are restored by the decoder
defined here. The integration check against a real application is `scripts/check-team-docs.py` (Mailpit decodes).
-/

namespace Test.MailSend

open Nyxis.Internal.MailSend

private def config : Config := ⟨"smtps://relay.example:465", "from@example.test"⟩

/-- The largest number of bytes in a line (CRLF-separated). -/
private def maxLineBytes (s : String) : Nat :=
  (s.splitOn "\r\n").foldl (fun m l => max m l.utf8ByteSize) 0

/-- A base64 decoder for the checks (`=` padding and folding CRLFs are skipped). -/
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

/-- For the checks: decode the value of `subjectField` (a plain subject, or a sequence of UTF-8 B encoded-words folded
    with CRLF + SP; each word must decode as UTF-8 on its own — a word cut in the middle of a character gives U+FFFD).
    -/
private def decodeSubject (field : String) : String :=
  let words := (String.ofList (field.toList.drop 9)).splitOn "\r\n "
  if field.startsWith "Subject: =?UTF-8?B?" then
    String.join (words.map fun w =>
      (String.fromUTF8? (unbase64 (String.ofList ((w.toList.drop 10).dropLast.dropLast)))).getD "�")
  else String.join words

/-- For the checks: decode the body of a message (the base64 after the empty line). -/
private def decodeBody (m : String) : Option String :=
  match m.splitOn "\r\n\r\n" with
  | [_, body] => String.fromUTF8? (unbase64 body)
  | _ => none

/-- The subject with the removed characters (newlines, control characters) taken out. -/
private def cleaned (s : String) : String := String.ofList (s.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127)

private def asciiLong : String := String.ofList (List.replicate 300 'x')
private def wideBody : String := String.join (List.replicate 60 "가나다라마, 이것은 긴 본문의 일부입니다.")
private def wideSubject : String := String.join (List.replicate 12 "제목예시")
-- Characters of 1, 3 and 4 bytes mixed (covers the next character overflowing just before a chunk's limit).
private def mixedSubject : String := "a" ++ String.join (List.replicate 20 "제😀")

-- base64 follows RFC 4648 (known vectors). The decoder is its inverse.
#guard base64 "".toUTF8 == ""
#guard base64 "f".toUTF8 == "Zg=="
#guard base64 "fo".toUTF8 == "Zm8="
#guard base64 "foobar".toUTF8 == "Zm9vYmFy"
#guard base64 "a1 body\r\n".toUTF8 == "YTEgYm9keQ0K"
#guard ["", "f", "fo", "foo", wideBody, mixedSubject].all fun s => String.fromUTF8? (unbase64 (base64 s.toUTF8)) == some s
-- Folding: a CRLF every 76 characters (every line but the last is exactly 76). Without the CRLFs it equals the unfolded
-- base64.
#guard ((base64 wideBody.toUTF8 (wrap := 76)).splitOn "\r\n").dropLast.all (·.length == 76)
#guard String.join ((base64 wideBody.toUTF8 (wrap := 76)).splitOn "\r\n") == base64 wideBody.toUTF8
#guard base64 "foobar".toUTF8 (wrap := 76) == "Zm9vYmFy"

-- Subject: printable ASCII whose `Subject: ` line fits in 78 characters is used as is (Mailpit returns the plain
-- subject too). An empty subject does not break either.
#guard subjectField "a1" == "Subject: a1"
#guard subjectField "" == "Subject: "
#guard subjectField (String.ofList (List.replicate 69 'y')) == "Subject: " ++ String.ofList (List.replicate 69 'y')
#guard (subjectField (String.ofList (List.replicate 70 'y'))).startsWith "Subject: =?UTF-8?B?"
-- Newlines and control characters are removed (no header can be injected).
#guard subjectField "hello\r\nBcc: evil@example.com" == "Subject: helloBcc: evil@example.com"
-- A subject containing `=?` is encoded so that it is not read as an encoded-word (RFC 2047 §7).
#guard (subjectField "=?UTF-8?B?Zm9v?=").startsWith "Subject: =?UTF-8?B?"
-- A long or non-ASCII subject becomes encoded-words: the first word on the `Subject: ` line and the later ones on
-- continuation lines (starting with SP), each line at most 76 bytes. Decoding restores the original subject (with
-- newlines and control characters removed).
#guard ((subjectField asciiLong).splitOn "\r\n").length > 1
#guard ((subjectField wideSubject).splitOn "\r\n").all fun l =>
  l.startsWith "Subject: =?UTF-8?B?" || l.startsWith " =?UTF-8?B?"
#guard [asciiLong, wideSubject, mixedSubject, "제목", "hello\r\n제목", "=?UTF-8?B?Zm9v?=", "a1", ""].all fun s =>
  maxLineBytes (subjectField s) ≤ 76 && decodeSubject (subjectField s) == cleaned s
-- Chunking never crosses a character boundary (the first chunk is at most 39 bytes and the later ones at most 45, and
-- joining them restores the input).
#guard [wideSubject, mixedSubject].all fun s =>
  let chunks := chunkByBytes s 39 45
  chunks.length > 1 && (chunks.headD "").utf8ByteSize ≤ 39 && chunks.all (·.utf8ByteSize ≤ 45) &&
    String.join chunks == s

-- The message is 7-bit and every line is at most 76 bytes.
#guard [("a1", "a1 body"), (wideSubject, wideBody), (asciiLong, asciiLong)].all fun (s, b) =>
  let m := message config "to@example.test" s b
  maxLineBytes m ≤ 76 && m.toList.all (·.toNat < 128)
-- The body is the base64 of the CRLF-normalised body plus a trailing CRLF (Mailpit's Text is this, decoded).
#guard (message config "to@example.test" "a1" "a1 body").endsWith
  "Content-Transfer-Encoding: base64\r\n\r\nYTEgYm9keQ0K\r\n"
#guard decodeBody (message config "to@example.test" wideSubject wideBody) == some (wideBody ++ "\r\n")
#guard decodeBody (message config "to@example.test" "s" "line1\rline2\n\nline3\r\n\x00end") ==
  some "line1line2\r\n\r\nline3\r\nend\r\n"
#guard decodeBody (message config "to@example.test" "s" "") == some "\r\n"

end Test.MailSend
