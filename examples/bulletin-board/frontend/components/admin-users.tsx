"use client";

import { useEffect, useRef, useState } from "react";
import { ApiError, readUser, setAdmin, withTimeout, type Failure } from "../lib/api";
import { useAuth } from "./auth";
import { ResponseState, uuidPattern } from "./posts";

type Result = { id: string; admin: boolean };
export function AdminUsers() {
  const { ready, session, identity, refreshIdentity } = useAuth();
  const [id, setId] = useState("");
  const [result, setResult] = useState<Result | null>(null);
  const [phase, setPhase] = useState("");
  const [failure, setFailure] = useState<Failure | null>(null);
  const [busy, setBusy] = useState(false);
  const confirm = phase === "confirmSelfRevoke";
  const pending = useRef<AbortController | null>(null);
  const retry = useRef<() => void>(() => {});
  const revokeButton = useRef<HTMLButtonElement>(null);
  useEffect(() => () => { pending.current?.abort(); }, []);
  function valid() {
    if (uuidPattern.test(id.trim())) return true;
    setPhase("invalid"); setFailure(null); return false;
  }
  async function run(action: "lookup" | "change", admin = true) {
    if (pending.current || !ready || !valid()) return;
    const target = id.trim();
    const controller = new AbortController();
    pending.current = controller;
    setBusy(true); setFailure(null); setPhase("loading");
    retry.current = () => { void run(action, admin); };
    try {
      const signal = withTimeout(controller.signal);
      if (action === "lookup") {
        setResult(null);
        const user = await readUser(target, signal, session?.accessToken);
        if (!controller.signal.aborted) { setResult({ id: target, admin: user.admin }); setPhase("lookupResult"); }
      } else {
        if (!session) throw new ApiError("denied");
        await setAdmin(target, admin, signal, session.accessToken);
        if (!controller.signal.aborted) {
          setResult({ id: target, admin }); setPhase("success");
          if (target.toLowerCase() === session.userId.toLowerCase()) refreshIdentity();
        }
      }
    } catch (error) {
      if (!controller.signal.aborted) {
        const kind = error instanceof ApiError ? error.kind : "offline";
        setFailure(kind);
        setPhase(action === "lookup" && kind === "denied" ? "lookupDenied" : action === "lookup" && kind === "notFound" ? "lookupNotFound" : kind);
      }
    } finally {
      if (!controller.signal.aborted) { pending.current = null; setBusy(false); }
    }
  }
  function change() {
    if (!valid()) return;
    if (result?.admin && result.id.toLowerCase() === session?.userId.toLowerCase()) {
      setFailure(null); setPhase("confirmSelfRevoke");
    } else void run("change", !result?.admin);
  }
  const state = phase || (!ready || identity === "loading" ? "loading" : !session ? "anonymous" : identity === "admin" ? "admin" : "nonAdmin");
  return <main className="wrap main" data-screen="S8" data-state={`AdminUsers.${state}`}>
    <h1>管理</h1>
    <form className="open-id admin-lookup" aria-busy={busy} onSubmit={event => { event.preventDefault(); void run("lookup"); }}>
      <div><label htmlFor="lookup-id">ID</label><input id="lookup-id" className={`mono ${phase === "invalid" || failure === "badRequest" ? "invalid" : ""}`} value={id} disabled={busy} spellCheck={false} autoCapitalize="none" aria-invalid={phase === "invalid" || failure === "badRequest"} aria-describedby={phase === "invalid" ? "lookup-id-error" : undefined} onChange={event => {
        setId(event.target.value); setResult(null); setFailure(null); setPhase("");
      }} />{phase === "invalid" && <p id="lookup-id-error" role="alert">IDをたしかめてください</p>}</div>
      <button className="btn line" type="submit" disabled={!ready || busy}>調べる</button>
    </form>
    {result && <section className="sheet admin-result" aria-busy={busy}>
      <span className={`avatar big ${result.admin ? "administrator" : "member"}`} aria-hidden="true">{result.id.slice(0, 2)}</span>
      <div className="admin-person"><div className="admin-tags"><span className={`tag ${result.admin ? "admin-tag" : "draft"}`}>{result.admin ? "管理者" : "なし"}</span>{phase === "success" && <strong className="stamp success" role="status" data-screen="P2" data-state="Stamp.ok.done">できました</strong>}</div><span className="mono">{result.id}</span></div>
      <button ref={revokeButton} className={`btn line ${result.admin ? "danger" : ""}`} type="button" disabled={busy || confirm} onClick={change}>{result.admin ? "管理者を外す" : "管理者にする"}</button>
      {confirm && <div className="delete-confirm" role="group" aria-label="自分を管理者から外しますか?">
        <p>自分を管理者から外しますか?</p><button className="btn danger" type="button" disabled={busy} onClick={() => void run("change", false)}>外す</button><button className="btn line" type="button" onClick={() => { setPhase("lookupResult"); requestAnimationFrame(() => revokeButton.current?.focus()); }}>やめる</button>
      </div>}
    </section>}
    {!result && id.trim() && phase !== "invalid" && <button className="btn line admin-direct" type="button" disabled={!ready || busy} onClick={change}>管理者にする</button>}
    {busy && <ResponseState status="loading" retry={() => {}} />}
    {failure && (failure === "denied" ? <div role="alert"><strong className="stamp" data-screen="P2" data-state={phase === "lookupDenied" ? "Stamp.denied.read" : "Stamp.denied.act"}>{phase === "lookupDenied" ? "見られません" : "できません"}</strong></div> : <ResponseState status={failure} retry={() => retry.current()} />)}
  </main>;
}
