import Nyxis.Http

/-! Correspondence for building HTTP responses. Not part of the handler-facing API. -/
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

/-- The success value of the standard text conversion has the Full body built, from the same starting state, from the
UTF-8 bytes of `content`, and keeps the given builder's status code and the fixed Content-Type. The IO state right after
building the body equals the IO state at the end of the response conversion. No exception contents or DB rows are added.
Consumption of the Full body, the external behavior of the Mutex and network sending are not covered. The same theorem
also applies to the fixed production 503/400/health bodies. -/
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

/-- The status code of the response line built by `Nyxis.Http.responseBuilder` is that of the model response. Adding the
allowed headers (Content-Type, and the few headers added in order with only valid values) does not change the status
code. -/
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

/-- The success value of the real toHttpResponse has the same status code as the model response, and holds as-is the
Full body built from the UTF-8 bytes of the same body. It matches down to the structure of the body-building result in
the same IO state and of the response line (the status code, plus the Content-Type and few headers that
`Nyxis.Http.responseBuilder` builds only from the valid values of the model response's allowed headers), and adds no
headers or body that are not in the model response. This theorem alone does not cover reachability from before the body
is read, composition with dispatch's return value, type erasure to Any, or sending. -/
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

/-- The success response of the Full→Any conversion by the same `return` as a real handler has the given builder's line
and extensions, headers with the fixed Content-Type set, and equals the Full body built from the same UTF-8 bytes
wrapped with ofReplayableBody. recv/close/size/replay operations are delegated to that Full, and no other body or IO
processing is added. The IO state right after building equals the IO state at the end. The semantics of consuming the
Full, composition with dispatch, and network sending are not covered. -/
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

/-- Following the real HTTP conversion of a model response with the same Full→Any conversion as a handler preserves the
result built from the model's status code and the UTF-8 bytes of its body, and the line (Content-Type and a few headers)
that `Nyxis.Http.responseBuilder` builds only from the valid values of the model response's allowed headers. The Any
body keeps all operations and the replay operation of the same Full. Consumption, transport and composition with
dispatch are not covered. -/
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
