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
    try { await navigator.clipboard.writeText(session.userId); setCopyNotice("コピーしました"); }
    catch { setCopyNotice("コピーできませんでした。IDを選んでコピーしてください"); }
  }
  const state = !ready ? "loading" : !session ? expired ? "expired" : "anonymous" : identity;
  const admin = state === "admin";
  const unknown = state === "unregistered" || state === "offline";
  const capabilities = [
    ["公開中の投稿を見る", "yes"],
    ["投稿する", session ? "yes" : "no"],
    [admin ? "みんなの投稿を直す・公開する・消す" : "自分の投稿を直す・公開する・消す", session ? "yes" : "no"],
    ["管理者を決める", unknown ? "unknown" : admin ? "yes" : "no"],
  ];
  return <main className="wrap main" data-screen="S7" data-state={`Me.${state}`}>
    <h1>あなた</h1>
    {state === "loading" ? <section className="sheet"><ResponseState status="loading" retry={() => {}} /></section> : <>
      <section className="sheet me-identity">
        <span className={`avatar big ${!session ? "guest" : admin ? "administrator" : state === "unregistered" ? "unregistered" : "member"}`} aria-hidden="true">{session?.userId.slice(0, 2)}</span>
        <div className="me-info"><strong>{!session ? "ゲスト" : state === "unregistered" ? "利用登録まだ" : "ログイン中"}</strong>
          {admin && <span className="tag admin-tag">管理者</span>}
          {session && <div className="me-id"><span className="mono">{session.userId}</span><button type="button" className="text-button" onClick={() => void copy()}>コピー</button></div>}
          {copyNotice && <p role="status">{copyNotice}</p>}
        </div>
        {session ? <button type="button" className="btn line" onClick={() => { void logout(); router.replace("/"); }}>ログアウト</button> : <Link className="btn google" href="/login?next=/me"><img src="/google-g.png" width="20" height="20" alt="" />Googleでログイン</Link>}
        {state === "unregistered" && <button type="button" className="btn" disabled={busy} onClick={() => void register()}>{busy ? "登録中" : "利用登録する"}</button>}
      </section>
      {state === "offline" && <ResponseState status="offline" retry={refreshIdentity} />}
      {state === "denied" && <strong className="stamp" role="alert">見られません</strong>}
      {["badRequest", "conflict"].includes(state) && <ResponseState status={state} retry={refreshIdentity} />}
      {failure && <div aria-busy={busy}>{failure === "denied" ? <strong className="stamp" role="alert">できません</strong> : <ResponseState status={failure} retry={() => void register()} />}</div>}
      <section className="me-section" aria-labelledby="capabilities"><h2 id="capabilities" className="cap">できること</h2>
        <div className="capabilities">{capabilities.map(([label, permission]) => <div key={label} className={permission}>
          <span>{label}</span><span className="capability-mark" role="img" aria-label={permission === "yes" ? "できる" : permission === "no" ? "できない" : "未確認"}>{permission === "yes" ? "○" : permission === "no" ? "×" : "?"}</span>
        </div>)}</div>
      </section>
      <section className="me-section" aria-labelledby="try-it"><h2 id="try-it" className="cap">ためす</h2>
        <div className="me-actions"><button className="btn line" type="button" aria-expanded={showDraft} aria-controls="try-draft" onClick={() => setShowDraft(value => !value)}>ほかの人の下書きを開く</button><Link className="btn line" href="/admin">管理の画面を開く</Link></div>
        {showDraft && <form id="try-draft" className="open-id" onSubmit={event => {
          event.preventDefault();
          if (!uuidPattern.test(draftId.trim())) { setInvalidId(true); return; }
          router.push(`/posts/${encodeURIComponent(draftId.trim())}`);
        }}><div><label htmlFor="draft-id">下書きのID</label><input id="draft-id" value={draftId} onChange={event => { setDraftId(event.target.value); setInvalidId(false); }} aria-invalid={invalidId} aria-describedby={invalidId ? "draft-id-error" : undefined} className={invalidId ? "invalid" : ""} />{invalidId && <p id="draft-id-error">IDをたしかめてください</p>}</div><button className="btn line" type="submit">開く</button></form>}
      </section>
    </>}
  </main>;
}
