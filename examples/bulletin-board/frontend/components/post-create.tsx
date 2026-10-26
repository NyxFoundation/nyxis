"use client";

import Link from "next/link";
import { useRouter } from "next/navigation";
import { useEffect, useRef, useState, type FormEvent } from "react";
import { ApiError, createPost, withTimeout } from "../lib/api";
import { useAuth } from "./auth";

export function PostCreate() {
  const { ready, session } = useAuth();
  const router = useRouter();
  const [id, setId] = useState("");
  const [title, setTitle] = useState("");
  const [body, setBody] = useState("");
  const [published, setPublished] = useState(false);
  const [invalid, setInvalid] = useState(false);
  const [failure, setFailure] = useState<ApiError | null>(null);
  const [busy, setBusy] = useState(false);
  const pending = useRef<AbortController | null>(null);
  useEffect(() => {
    setId(crypto.randomUUID());
    return () => { pending.current?.abort(); };
  }, []);
  async function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (pending.current || !session || !id) return;
    setFailure(null);
    if (!title.trim() || !body.trim()) { setInvalid(true); return; }
    setInvalid(false);
    const controller = new AbortController();
    pending.current = controller;
    setBusy(true);
    try {
      await createPost(id, { title, body, published }, withTimeout(controller.signal), session.accessToken);
      if (!controller.signal.aborted) router.push(`/posts/${encodeURIComponent(id)}?created=${published ? "published" : "draft"}`);
    } catch (error) {
      if (!controller.signal.aborted) {
        setFailure(error instanceof ApiError ? error : new ApiError("offline"));
        pending.current = null;
        setBusy(false);
      }
    }
  }
  const state = !ready ? "loading" : !session ? "anonymous" : busy ? "submitting" : failure?.kind || (invalid ? "invalid" : "editing");
  return <main className="wrap main" data-screen="S3" data-state={`PostCreate.${state}`}>
    <h1>投稿</h1>
    {!ready ? <div className="skeleton" role="status" aria-label="読み込み中"><i /><i /><i /></div> : !session ? <><p>投稿するにはログインが必要です</p><Link className="btn line" href="/login?next=%2Fposts%2Fnew">Googleでログイン</Link></> :
      <form className="sheet compose" onSubmit={submit} noValidate>
        {failure?.kind === "denied" && <div role="alert"><strong className="stamp">できません</strong><p>ログインしなおしてください</p><Link href="/login?next=%2Fposts%2Fnew">ログインへ</Link></div>}
        {failure?.kind === "offline" && <div className="offline" role="alert"><span>つながりません</span><button type="submit" disabled={busy}>もう一度</button></div>}
        {failure?.kind === "notFound" && <p className="empty" role="alert">見つかりません</p>}
        {failure?.kind === "badRequest" && <p className="invalid" role="alert">入力をたしかめてください{failure.message !== "badRequest" && <>: {failure.message}</>}</p>}
        <label className="sr-only" htmlFor="post-title">題名</label>
        <input id="post-title" className={`compose-title ${invalid && !title.trim() || failure?.kind === "badRequest" ? "invalid" : ""}`} placeholder="題名" value={title} onChange={e => setTitle(e.target.value)} disabled={busy} aria-invalid={invalid && !title.trim()} aria-describedby={invalid && !title.trim() ? "title-error" : undefined} />
        {invalid && !title.trim() && <p id="title-error" className="invalid" role="alert">題名を入れてください</p>}
        <label className="sr-only" htmlFor="post-body">本文</label>
        <textarea id="post-body" className={invalid && !body.trim() ? "invalid" : ""} placeholder="本文" value={body} onChange={e => setBody(e.target.value)} disabled={busy} aria-invalid={invalid && !body.trim()} aria-describedby={invalid && !body.trim() ? "body-error" : undefined} />
        {invalid && !body.trim() && <p id="body-error" className="invalid" role="alert">本文を入れてください</p>}
        <div className="compose-actions">
          <div className="toggle" role="group" aria-label="公開の設定"><button type="button" aria-pressed={!published} className={`btn ${published ? "line" : ""}`} onClick={() => setPublished(false)} disabled={busy}>下書き</button><button type="button" aria-pressed={published} className={`btn ${published ? "" : "line"}`} onClick={() => setPublished(true)} disabled={busy}>公開する</button></div>
          <Link href="/">やめる</Link><button className="btn" type="submit" disabled={busy || !id}>{busy ? "保存中" : "保存"}</button>
        </div>
        <div className="compose-id"><span className="mono">ID</span><span className="mono" style={failure?.kind === "conflict" ? { textDecoration: "line-through" } : undefined}>{id}</span><button type="button" className="text-button" disabled={busy} onClick={() => { setId(crypto.randomUUID()); setFailure(null); }}>新しいIDに</button></div>
        {failure?.kind === "conflict" && <p role="alert">このIDはすでにあります</p>}
      </form>}
  </main>;
}
