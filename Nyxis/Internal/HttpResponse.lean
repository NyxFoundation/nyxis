import Nyxis.Http

/-! HTTP 応答の構築の対応。ハンドラ向けの API には含まれない。 -/
namespace Nyxis.Internal.HttpResponse
open Std.Async

private theorem baseIO_immediate {α : Type} (action : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM action : Async α).toRawBaseIO w = .mk (.pure (.ok a)) w' := by
  cases h : action w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match action w with | .mk x wx => ST.Out.mk (MaybeTask.pure (Except.ok x)) wx) = _
    rw [h]

private theorem bind_immediate {α β : Type} (action : Async α) (next : α → Async β)
    (w wa : Void IO.RealWorld) (a : α)
    (h : action.toRawBaseIO w = .mk (.pure (.ok a)) wa) :
    (action >>= next).toRawBaseIO w = (next a).toRawBaseIO wa := by
  change (EAsync.bind action next).toRawBaseIO w = _
  simp only [EAsync.bind, BaseAsync.bind, BaseAsync.mk, BaseAsync.toRawBaseIO]
  simp only [bind, instMonadBaseIO._aux_13, ST.bind]
  change action w = _ at h
  rw [h]
  rfl

private theorem bytes_immediate (bytes : ByteArray) (w : Void IO.RealWorld) :
    ∃ full w', (Std.Http.Body.Full.ofByteArray bytes).toRawBaseIO w =
      .mk (.pure (.ok full)) w' := by
  unfold Std.Http.Body.Full.ofByteArray
  obtain ⟨state, w', hs⟩ := baseIO_immediate _ w
  exact ⟨_, w', (bind_immediate _ _ w w' state hs)⟩

/-- 日本語: 標準text変換の成功値は、同じ開始状態でcontentのUTF-8バイト列から
構築したFull本文を持ち、指定builderの状態コード・固定Content-Typeを保つ。
本文構築直後と応答変換終了のIO状態は等しい。例外の内容やDBの行を追加しない。
Full本文の消費・Mutexの外界動作・ネットワーク送信は含まない。
本番の固定503/400/health本文にも同じ定理を適用できる。 -/
theorem text_success (builder : Std.Http.Response.Builder) (content : String)
    (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Full)))
    (response : Std.Http.Response Std.Http.Body.Full)
    (h : (builder.text content).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    response.line.status = builder.line.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray content.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (builder.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body full := by
  obtain ⟨full, wa, hf⟩ := bytes_immediate content.toUTF8 w
  have hb := bind_immediate (Std.Http.Body.Full.ofByteArray content.toUTF8)
    (fun full => pure ((builder.header Std.Http.Header.Name.contentType
      (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body full)) w wa full hf
  change (builder.text content).toRawBaseIO w = _ at hb
  rw [hb] at h
  change ST.Out.mk (.pure (.ok _)) wa = .mk pending w' at h
  cases h
  cases hv
  exact ⟨rfl, full, hf, rfl⟩

/-- 日本語: `Nyxis.Http.responseBuilder` が組む応答の行の状態コードはモデル応答のもの。
許可ヘッダの追加(Content-Type と、妥当な値だけを順に加える少数のヘッダ)は状態コードを変えない。 -/
theorem responseBuilder_status (r : Nyxis.Http.Response) :
    (Nyxis.Http.responseBuilder r).line.status = r.status := by
  unfold Nyxis.Http.responseBuilder
  generalize hb : ((Std.Http.Response.withStatus r.status).header Std.Http.Header.Name.contentType
    (Nyxis.Http.contentTypeOf r)) = base
  have hbase : base.line.status = r.status := by
    subst hb
    rfl
  clear hb
  generalize Nyxis.Http.ResponseHeader.all = names
  induction names generalizing base with
  | nil => exact hbase
  | cons h rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact hbase
    · split
      · exact hbase
      · exact hbase

/-- 日本語: 実toHttpResponseの成功値は、モデル応答と同じ状態コードを持ち、
同じ本文のUTF-8バイト列から構築したFull本文をそのまま持つ。
同じIO状態での本文構築結果と、応答の行(状態コード・モデル応答の許可ヘッダの妥当な値だけから
`Nyxis.Http.responseBuilder` が組む Content-Type と少数のヘッダ)の構造まで一致し、
モデル応答に無いヘッダや本文を加えない。
この定理単体は本文取得前からの到達性・dispatchの返却値との合成・Anyへの型消去・送信を含まない。 -/
theorem toHttpResponse_success (r : Nyxis.Http.Response) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Full)))
    (response : Std.Http.Response Std.Http.Body.Full)
    (h : (Nyxis.Http.toHttpResponse r).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    response.line.status = r.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray r.body.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (Nyxis.Http.responseBuilder r).body full := by
  obtain ⟨full, wa, hf⟩ := bytes_immediate r.body.toUTF8 w
  have hb := bind_immediate (Std.Http.Body.Full.ofByteArray r.body.toUTF8)
    (fun full => pure ((Nyxis.Http.responseBuilder r).body full)) w wa full hf
  change (Nyxis.Http.toHttpResponse r).toRawBaseIO w = _ at hb
  rw [hb] at h
  change ST.Out.mk (.pure (.ok _)) wa = .mk pending w' at h
  cases h
  cases hv
  exact ⟨responseBuilder_status r, full, hf, rfl⟩

/-- 日本語: 実ハンドラと同じreturnによるFull→Any変換の成功応答は、指定builderの
行・extensionsと固定Content-Typeを設定したヘッダを持ち、同じUTF-8バイト列から構築したFull本文を
ofReplayableBodyで包んだものに等しい。recv/close/サイズ/再生操作はそのFullへ
委譲され、別の本文やIO処理を追加しない。構築直後と終了のIO状態も同じ。
Fullの消費の意味論、dispatchとの合成、ネットワーク送信は含まない。 -/
theorem text_any_success (builder : Std.Http.Response.Builder) (content : String)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (response : Std.Http.Response Std.Http.Body.Any)
    (h : (((do return ← builder.text content) :
      ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    response.line.status = builder.line.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray content.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (builder.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨full, wa, hf⟩ := bytes_immediate content.toUTF8 w
  have ht := bind_immediate (Std.Http.Body.Full.ofByteArray content.toUTF8)
    (fun full => pure ((builder.header Std.Http.Header.Name.contentType
      (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body full)) w wa full hf
  change (builder.text content).toRawBaseIO w = _ at ht
  have hb := bind_immediate (builder.text content)
    (fun response => pure (response : Std.Http.Response Std.Http.Body.Any)) w wa _ ht
  change ((builder.text content >>= fun response =>
    pure (response : Std.Http.Response Std.Http.Body.Any)) :
      Async (Std.Http.Response Std.Http.Body.Any)).toRawBaseIO w = _ at h
  rw [hb] at h
  change ST.Out.mk (.pure (.ok _)) wa = .mk pending w' at h
  cases h
  cases hv
  exact ⟨rfl, full, hf, rfl⟩

/-- 日本語: モデル応答の実HTTP変換にハンドラと同じFull→Any変換を続けても、
モデルの状態コードと本文UTF-8バイト列による構築結果と、`Nyxis.Http.responseBuilder` が
モデル応答の許可ヘッダの妥当な値だけから組む行(Content-Type と少数のヘッダ)を保存する。
Any本文は同じFullの全操作と再生操作を保持する。消費・輸送とdispatchとの合成は含まない。 -/
theorem toHttpResponse_any_success (r : Nyxis.Http.Response)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (response : Std.Http.Response Std.Http.Body.Any)
    (h : (((do return ← Nyxis.Http.toHttpResponse r) :
      ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    response.line.status = r.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray r.body.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (Nyxis.Http.responseBuilder r).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨full, wa, hf⟩ := bytes_immediate r.body.toUTF8 w
  have ht := bind_immediate (Std.Http.Body.Full.ofByteArray r.body.toUTF8)
    (fun full => pure ((Nyxis.Http.responseBuilder r).body full)) w wa full hf
  change (Nyxis.Http.toHttpResponse r).toRawBaseIO w = _ at ht
  have hb := bind_immediate (Nyxis.Http.toHttpResponse r)
    (fun response => pure (response : Std.Http.Response Std.Http.Body.Any)) w wa _ ht
  change ((Nyxis.Http.toHttpResponse r >>= fun response =>
    pure (response : Std.Http.Response Std.Http.Body.Any)) :
      Async (Std.Http.Response Std.Http.Body.Any)).toRawBaseIO w = _ at h
  rw [hb] at h
  change ST.Out.mk (.pure (.ok _)) wa = .mk pending w' at h
  cases h
  cases hv
  exact ⟨responseBuilder_status r, full, hf, rfl⟩

end Nyxis.Internal.HttpResponse
