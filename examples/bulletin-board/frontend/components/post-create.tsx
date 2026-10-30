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
    <h1>New post</h1>
    {!ready ? <div className="skeleton" role="status" aria-label="Loading"><i /><i /><i /></div> : !session ? <><p>Sign in to post</p><Link className="btn line" href="/login?next=%2Fposts%2Fnew">Sign in with Google</Link></> :
      <form className="sheet compose" onSubmit={submit} noValidate>
        {failure?.kind === "denied" && <div role="alert"><strong className="stamp">Not allowed</strong><p>Please sign in again</p><Link href="/login?next=%2Fposts%2Fnew">Go to sign-in</Link></div>}
        {failure?.kind === "offline" && <div className="offline" role="alert"><span>Can't connect</span><button type="submit" disabled={busy}>Try again</button></div>}
        {failure?.kind === "notFound" && <p className="empty" role="alert">Not found</p>}
        {failure?.kind === "badRequest" && <p className="invalid" role="alert">Check your input{failure.message !== "badRequest" && <>: {failure.message}</>}</p>}
        <label className="sr-only" htmlFor="post-title">Title</label>
        <input id="post-title" className={`compose-title ${invalid && !title.trim() || failure?.kind === "badRequest" ? "invalid" : ""}`} placeholder="Title" value={title} onChange={e => setTitle(e.target.value)} disabled={busy} aria-invalid={invalid && !title.trim()} aria-describedby={invalid && !title.trim() ? "title-error" : undefined} />
        {invalid && !title.trim() && <p id="title-error" className="invalid" role="alert">Enter a title</p>}
        <label className="sr-only" htmlFor="post-body">Body</label>
        <textarea id="post-body" className={invalid && !body.trim() ? "invalid" : ""} placeholder="Body" value={body} onChange={e => setBody(e.target.value)} disabled={busy} aria-invalid={invalid && !body.trim()} aria-describedby={invalid && !body.trim() ? "body-error" : undefined} />
        {invalid && !body.trim() && <p id="body-error" className="invalid" role="alert">Enter the body</p>}
        <div className="compose-actions">
          <div className="toggle" role="group" aria-label="Visibility"><button type="button" aria-pressed={!published} className={`btn ${published ? "line" : ""}`} onClick={() => setPublished(false)} disabled={busy}>Draft</button><button type="button" aria-pressed={published} className={`btn ${published ? "" : "line"}`} onClick={() => setPublished(true)} disabled={busy}>Publish</button></div>
          <Link href="/">Cancel</Link><button className="btn" type="submit" disabled={busy || !id}>{busy ? "Saving" : "Save"}</button>
        </div>
        <div className="compose-id"><span className="mono">ID</span><span className="mono" style={failure?.kind === "conflict" ? { textDecoration: "line-through" } : undefined}>{id}</span><button type="button" className="text-button" disabled={busy} onClick={() => { setId(crypto.randomUUID()); setFailure(null); }}>New ID</button></div>
        {failure?.kind === "conflict" && <p role="alert">This ID already exists</p>}
      </form>}
  </main>;
}
