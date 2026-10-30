"use client";

import Link from "next/link";
import { useRouter } from "next/navigation";
import { useEffect, useRef, useState, type FormEvent } from "react";
import { ApiError, editPost, setPostPublished, withTimeout, type Failure, type Post } from "../lib/api";
import { useAuth } from "./auth";
import { parsePost, ResponseState, useRead } from "./posts";

export function PostEdit({ id }: { id: string }) {
  const { session, identity } = useAuth();
  const admin = identity === "admin";
  const [actionState, setActionState] = useState<string | null>(null);
  const [result, retry] = useRead(`/posts/${encodeURIComponent(id)}`, parsePost);
  const identityPending = result.status === "ready" && !!session && identity === "loading";
  const state = result.status === "ready" ? !session ? "anonymous" : identityPending ? "loading" : `editing.${admin ? "admin" : result.data.author === session.userId ? "author" : "nonAuthor"}` : result.status === "denied" ? "loadDenied" : result.status;
  return <main className="wrap main" data-screen="S4" data-state={`PostEdit.${actionState || state}`}>
    <h1>Edit</h1>
    {result.status !== "ready" ? <ResponseState status={result.status} retry={retry} /> : !session ? <><p>Sign in to edit</p><Link className="btn line" href={`/login?next=${encodeURIComponent(`/posts/${id}/edit`)}`}>Sign in with Google</Link></> : identityPending ? <ResponseState status="loading" retry={retry} /> :
      <EditForm key={id} id={id} post={result.data} token={session.accessToken} onStateChange={setActionState} />}
    <Link href={`/posts/${encodeURIComponent(id)}`}>Back to post</Link>
  </main>;
}

function EditForm({ id, post, token, onStateChange }: { id: string; post: Post; token: string; onStateChange: (state: string | null) => void }) {
  const router = useRouter();
  const [title, setTitle] = useState(post.title);
  const [body, setBody] = useState(post.body);
  const [invalid, setInvalid] = useState(false);
  const [failure, setFailure] = useState<ApiError | null>(null);
  const [activity, setActivity] = useState<"save" | "publish" | null>(null);
  const busy = activity !== null;
  const [published, setPublished] = useState(post.published);
  const [publishFailure, setPublishFailure] = useState<Failure | null>(null);
  const [notice, setNotice] = useState("");
  useEffect(() => {
    if (!notice) return;
    const timer = setTimeout(() => setNotice(""), 2000);
    return () => clearTimeout(timer);
  }, [notice]);
  const pending = useRef<AbortController | null>(null);
  useEffect(() => () => { pending.current?.abort(); }, []);
  const state = publishFailure === "denied" ? "publishDenied" : publishFailure || (failure?.kind === "denied" ? "saveDenied" : failure?.kind || (invalid ? "invalid" : null));
  useEffect(() => { onStateChange(state); }, [state, onStateChange]);
  // The parent must not keep this form's last failure after the form is gone (logout, reload).
  useEffect(() => () => onStateChange(null), [onStateChange]);
  async function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (pending.current) return;
    setFailure(null);
    setPublishFailure(null);
    setNotice("");
    if (!title.trim() || !body.trim()) { setInvalid(true); return; }
    setInvalid(false);
    const controller = new AbortController();
    pending.current = controller;
    setActivity("save");
    try {
      await editPost(id, { title, body }, withTimeout(controller.signal), token);
      if (!controller.signal.aborted) router.push(`/posts/${encodeURIComponent(id)}?saved=1`);
    } catch (error) {
      if (!controller.signal.aborted) {
        setFailure(error instanceof ApiError ? error : new ApiError("offline"));
        pending.current = null;
        setActivity(null);
      }
    }
  }
  async function togglePublished() {
    if (pending.current) return;
    const controller = new AbortController();
    pending.current = controller;
    setActivity("publish");
    setFailure(null);
    setPublishFailure(null);
    setNotice("");
    const nextPublished = !published;
    try {
      await setPostPublished(id, nextPublished, withTimeout(controller.signal), token);
      if (!controller.signal.aborted) {
        setPublished(nextPublished);
        setNotice(nextPublished ? "Published" : "Moved to draft");
      }
    } catch (error) {
      if (!controller.signal.aborted) setPublishFailure(error instanceof ApiError ? error.kind : "offline");
    } finally {
      if (!controller.signal.aborted) {
        pending.current = null;
        setActivity(null);
      }
    }
  }
  return <><form className="sheet compose" onSubmit={submit} noValidate>
    {failure?.kind === "denied" && <div role="alert"><strong className="stamp" data-screen="P2" data-state="Stamp.denied.act">Not allowed</strong></div>}
    {failure?.kind === "offline" && <div className="offline" role="alert"><span>Can't connect</span><button type="submit" disabled={busy}>Try again</button></div>}
    {failure?.kind === "notFound" && <p className="empty" role="alert">Not found</p>}
    {failure?.kind === "conflict" && <p role="alert">Already changed <Link href={`/posts/${encodeURIComponent(id)}`}>Reload</Link></p>}
    {failure?.kind === "badRequest" && <p className="invalid" role="alert">Check your input{failure.message !== "badRequest" && <>: {failure.message}</>}</p>}
    <label className="sr-only" htmlFor="edit-title">Title</label>
    <input id="edit-title" className={`compose-title ${invalid && !title.trim() || failure?.kind === "badRequest" ? "invalid" : ""}`} value={title} onChange={e => setTitle(e.target.value)} disabled={busy} aria-invalid={invalid && !title.trim()} aria-describedby={invalid && !title.trim() ? "edit-title-error" : undefined} />
    {invalid && !title.trim() && <p id="edit-title-error" className="invalid" role="alert">Enter a title</p>}
    <label className="sr-only" htmlFor="edit-body">Body</label>
    <textarea id="edit-body" className={invalid && !body.trim() ? "invalid" : ""} value={body} onChange={e => setBody(e.target.value)} disabled={busy} aria-invalid={invalid && !body.trim()} aria-describedby={invalid && !body.trim() ? "edit-body-error" : undefined} />
    {invalid && !body.trim() && <p id="edit-body-error" className="invalid" role="alert">Enter the body</p>}
    <div className="compose-actions"><Link href={`/posts/${encodeURIComponent(id)}`}>Cancel</Link><button className="btn" type="submit" disabled={busy}>{activity === "save" ? "Saving" : "Save"}</button></div>
  </form>
    <div className="publication-actions" aria-busy={busy}>
      <strong>Now</strong><span className={`tag ${published ? "pub" : "draft"}`}>{published ? "Published" : "Draft"}</span>
      <button className="btn line" type="button" disabled={busy} onClick={togglePublished}>{activity === "publish" ? "Changing" : published ? "Back to draft" : "Publish"}</button>
      {notice && <p className="success-notice" role="status" data-screen={notice === "Published" ? "P2" : undefined} data-state={notice === "Published" ? "Stamp.ok.published" : undefined}>{notice}</p>}
      {publishFailure === "denied" && <div role="alert"><strong className="stamp" data-screen="P2" data-state="Stamp.denied.act">Not allowed</strong></div>}
      {publishFailure === "offline" && <div className="offline" role="alert"><span>Can't connect</span><button type="button" disabled={busy} onClick={togglePublished}>Try again</button></div>}
      {publishFailure === "notFound" && <p className="empty" role="alert">Not found</p>}
      {publishFailure === "conflict" && <p role="alert">Already changed <Link href={`/posts/${encodeURIComponent(id)}`}>Reload</Link></p>}
      {publishFailure === "badRequest" && <p className="invalid" role="alert">Check your input</p>}
    </div>
  </>;
}
