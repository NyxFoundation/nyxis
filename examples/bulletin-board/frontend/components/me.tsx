"use client";

import Link from "next/link";
import { useRouter } from "next/navigation";
import { useEffect, useRef, useState } from "react";
import { ApiError, registerUser, withTimeout, type Failure } from "../lib/api";
import { useAuth } from "./auth";
import { ResponseState, uuidPattern } from "./posts";

export function Me() {
  const { ready, session, expired, logout, identity, refreshIdentity } = useAuth();
  const router = useRouter();
  const [busy, setBusy] = useState(false);
  const [failure, setFailure] = useState<Failure | null>(null);
  const [copyNotice, setCopyNotice] = useState("");
  const [showDraft, setShowDraft] = useState(false);
  const [draftId, setDraftId] = useState("");
  const [invalidId, setInvalidId] = useState(false);
  const pending = useRef<AbortController | null>(null);
  useEffect(() => () => { pending.current?.abort(); }, []);
  async function register() {
    if (!session || pending.current) return;
    const controller = new AbortController();
    pending.current = controller;
    setBusy(true); setFailure(null);
    try {
      await registerUser(session.userId, withTimeout(controller.signal), session.accessToken);
      if (!controller.signal.aborted) refreshIdentity();
    } catch (error) {
      if (!controller.signal.aborted) setFailure(error instanceof ApiError ? error.kind : "offline");
    } finally {
      if (!controller.signal.aborted) { pending.current = null; setBusy(false); }
    }
  }
  async function copy() {
    if (!session) return;
    try { await navigator.clipboard.writeText(session.userId); setCopyNotice("Copied"); }
    catch { setCopyNotice("Couldn't copy. Select the ID and copy it"); }
  }
  const state = !ready ? "loading" : !session ? expired ? "expired" : "anonymous" : identity;
  const admin = state === "admin";
  const unknown = state === "unregistered" || state === "offline";
  const capabilities = [
    ["View published posts", "yes"],
    ["Create posts", session ? "yes" : "no"],
    [admin ? "Edit, publish, and delete everyone's posts" : "Edit, publish, and delete your posts", session ? "yes" : "no"],
    ["Choose admins", unknown ? "unknown" : admin ? "yes" : "no"],
  ];
  return <main className="wrap main" data-screen="S7" data-state={`Me.${state}`}>
    <h1>You</h1>
    {state === "loading" ? <section className="sheet"><ResponseState status="loading" retry={() => {}} /></section> : <>
      <section className="sheet me-identity">
        <span className={`avatar big ${!session ? "guest" : admin ? "administrator" : state === "unregistered" ? "unregistered" : "member"}`} aria-hidden="true">{session?.userId.slice(0, 2)}</span>
        <div className="me-info"><strong>{!session ? "Guest" : state === "unregistered" ? "Not registered" : "Signed in"}</strong>
          {admin && <span className="tag admin-tag">Admin</span>}
          {session && <div className="me-id"><span className="mono">{session.userId}</span><button type="button" className="text-button" onClick={() => void copy()}>Copy</button></div>}
          {copyNotice && <p role="status">{copyNotice}</p>}
        </div>
        {session ? <button type="button" className="btn line" onClick={() => { void logout(); router.replace("/"); }}>Sign out</button> : <Link className="btn google" href="/login?next=/me"><img src="/google-g.png" width="20" height="20" alt="" />Sign in with Google</Link>}
        {state === "unregistered" && <button type="button" className="btn" disabled={busy} onClick={() => void register()}>{busy ? "Registering" : "Register"}</button>}
      </section>
      {state === "offline" && <ResponseState status="offline" retry={refreshIdentity} />}
      {state === "denied" && <strong className="stamp" role="alert">Can't view</strong>}
      {["badRequest", "conflict"].includes(state) && <ResponseState status={state} retry={refreshIdentity} />}
      {failure && <div aria-busy={busy}>{failure === "denied" ? <strong className="stamp" role="alert">Not allowed</strong> : <ResponseState status={failure} retry={() => void register()} />}</div>}
      <section className="me-section" aria-labelledby="capabilities"><h2 id="capabilities" className="cap">What you can do</h2>
        <div className="capabilities">{capabilities.map(([label, permission]) => <div key={label} className={permission}>
          <span>{label}</span><span className="capability-mark" role="img" aria-label={permission === "yes" ? "Can" : permission === "no" ? "Can't" : "Unknown"}>{permission === "yes" ? "○" : permission === "no" ? "×" : "?"}</span>
        </div>)}</div>
      </section>
      <section className="me-section" aria-labelledby="try-it"><h2 id="try-it" className="cap">Try it</h2>
        <div className="me-actions"><button className="btn line" type="button" aria-expanded={showDraft} aria-controls="try-draft" onClick={() => setShowDraft(value => !value)}>Open someone else's draft</button><Link className="btn line" href="/admin">Open the admin page</Link></div>
        {showDraft && <form id="try-draft" className="open-id" onSubmit={event => {
          event.preventDefault();
          if (!uuidPattern.test(draftId.trim())) { setInvalidId(true); return; }
          router.push(`/posts/${encodeURIComponent(draftId.trim())}`);
        }}><div><label htmlFor="draft-id">Draft ID</label><input id="draft-id" value={draftId} onChange={event => { setDraftId(event.target.value); setInvalidId(false); }} aria-invalid={invalidId} aria-describedby={invalidId ? "draft-id-error" : undefined} className={invalidId ? "invalid" : ""} />{invalidId && <p id="draft-id-error">Check the ID</p>}</div><button className="btn line" type="submit">Open</button></form>}
      </section>
    </>}
  </main>;
}
