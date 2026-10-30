"use client";

import Link from "next/link";
import { useRouter } from "next/navigation";
import { useEffect, useRef, useState } from "react";
import { ApiError, deletePost, isEntry, isPost, readApi, setPostPublished, withTimeout, type Failure, type Post, type PostEntry } from "../lib/api";

import { useAuth } from "./auth";

type Result<T> = { status: "loading" } | { status: "ready"; data: T } | { status: Failure };
export function useRead<T>(path: string, parse: (value: unknown) => T) {
  const { session, ready } = useAuth();
  const [result, setResult] = useState<Result<T>>({ status: "loading" });
  const [attempt, setAttempt] = useState(0);
  useEffect(() => {
    const controller = new AbortController();
    setResult({ status: "loading" });
    if (!ready) return () => controller.abort();
    readApi(path, withTimeout(controller.signal), session?.accessToken).then(parse).then(data => {
      if (!controller.signal.aborted) setResult({ status: "ready", data });
    }).catch(error => {
      if (!controller.signal.aborted) setResult({ status: error instanceof ApiError ? error.kind : "offline" });
    });
    return () => controller.abort();
  // A token rotation for the same person does not reload (so in-progress input is not lost). The token sent is the one current at run time.
  }, [path, parse, attempt, session?.userId, ready]);
  return [result, () => { setResult({ status: "loading" }); setAttempt(n => n + 1); }] as const;
}
function parsePosts(value: unknown): PostEntry[] {
  if (!Array.isArray(value) || !value.every(isEntry)) throw new ApiError("offline");
  return value;
}
export function parsePost(value: unknown): Post {
  if (!isPost(value)) throw new ApiError("offline");
  return value;
}
export const uuidPattern = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
export function ResponseState({ status, retry }: { status: string; retry: () => void }) {
  if (status === "loading") return <div role="status" aria-label="Loading" className="skeleton"><i /><i /><i /></div>;
  if (status === "denied") return <section className="sheet denied" role="alert"><div className="skeleton" aria-hidden="true"><i /><i /><i /></div><strong className="stamp" data-screen="P2" data-state="Stamp.denied.read">Can't view</strong><p>It doesn't exist, or it's a draft. Drafts can be viewed only by their author and admins.</p></section>;
  if (status === "notFound") return <div className="empty" role="alert">Not found</div>;
  if (status === "badRequest") return <div className="invalid" role="alert">Check your input</div>;
  if (status === "conflict") return <div className="empty" role="alert">Already exists</div>;
  return <div className="offline" role="alert"><span>Can't connect</span><button onClick={retry}>Try again</button></div>;
}
export function PostList() {
  const { session, ready, identity } = useAuth();
  const router = useRouter();
  const [result, retry] = useRead("/posts", parsePosts);
  const [notice, setNotice] = useState("");
  useEffect(() => {
    if (!ready || new URLSearchParams(location.search).get("deleted") !== "1") return;
    setNotice("Deleted");
    history.replaceState(history.state, "", location.pathname);
  }, [ready]);
  useEffect(() => {
    if (!notice || result.status !== "ready") return;
    const timer = setTimeout(() => setNotice(""), 2000);
    return () => clearTimeout(timer);
  }, [notice, result.status]);
  const [id, setId] = useState("");
  const [invalid, setInvalid] = useState(false);
  // The rows are shown once the person is known, so the state never passes through `user` for an admin.
  const pending = result.status === "loading" || (result.status === "ready" && !!session && identity === "loading");
  const state = pending ? "loading" : result.status !== "ready" ? result.status : !result.data.length ? "empty" : !session ? "anonymous" : identity === "admin" ? "admin" : identity === "unregistered" ? "unregistered" : "user";
  return <main className="wrap main" data-screen="S1" data-state={`PostList.${state}`}>
    {notice && result.status === "ready" && <p className="success-notice" role="status">{notice}</p>}
    <div className="heading"><h1>Home</h1>{result.status === "ready" && <span className="mono">{result.data.length}</span>}</div>
    {pending ? <ResponseState status="loading" retry={retry} /> : result.status !== "ready" ? <ResponseState status={result.status} retry={retry} /> : result.data.length === 0 ? <div className="empty">No posts yet</div> : <div className="list">{result.data.map((post, i) => <article className="row" key={post.id}>
      <span className="num">{String(i + 1).padStart(2, "0")}</span>
      <Link className="title" href={`/posts/${encodeURIComponent(post.id)}`}>{post.title}</Link>
      <span className={`tag ${post.published ? "pub" : "draft"}`}>{post.published ? "Published" : "Draft"}</span>
      <p className="excerpt">{post.body}</p><span className="by mono">{post.author.slice(0, 8)}</span>
    </article>)}</div>}
    <form className="open-id" onSubmit={event => {
      event.preventDefault();
      if (!uuidPattern.test(id.trim())) { setInvalid(true); return; }
      router.push(`/posts/${encodeURIComponent(id.trim())}`);
    }}>
      <div><label htmlFor="open-id">Open by ID</label><input id="open-id" className={invalid ? "invalid" : ""} value={id} onChange={event => { setId(event.target.value); setInvalid(false); }} placeholder="Post ID" aria-invalid={invalid} aria-describedby={invalid ? "id-error" : undefined} />{invalid && <p id="id-error">Check the ID</p>}</div>
      <button className="btn line" type="submit">Open</button>
    </form>
  </main>;
}
export function PostDetail({ id }: { id: string }) {
  const { session, ready } = useAuth();
  if (!ready) return <main className="wrap main" data-screen="S2" data-state="PostDetail.loading"><ResponseState status="loading" retry={() => {}} /></main>;
  return <PostDetailView key={`${id}:${session?.userId || "anonymous"}`} id={id} />;
}
function PostDetailView({ id }: { id: string }) {
  const { session, identity } = useAuth();
  const admin = identity === "admin";
  const router = useRouter();
  const [confirmDelete, setConfirmDelete] = useState(false);
  const deleteButton = useRef<HTMLButtonElement>(null);
  const [notice, setNotice] = useState("");
  const [failure, setFailure] = useState<Failure | null>(null);
  const [busy, setBusy] = useState(false);
  const [result, retry] = useRead(`/posts/${encodeURIComponent(id)}`, parsePost);
  const pending = useRef<AbortController | null>(null);
  useEffect(() => () => { pending.current?.abort(); }, []);
  useEffect(() => {
    const query = new URLSearchParams(location.search);
    const created = query.get("created");
    if (created !== "published" && created !== "draft" && query.get("saved") !== "1") return;
    setNotice(created === "published" ? "Published" : "Saved");
    history.replaceState(history.state, "", location.pathname);
  }, [id]);
  useEffect(() => {
    if (!notice || result.status !== "ready") return;
    const timer = setTimeout(() => setNotice(""), 2000);
    return () => clearTimeout(timer);
  }, [notice, result.status]);
  function reload() { setConfirmDelete(false); setFailure(null); setNotice(""); retry(); }
  async function togglePublished() {
    if (pending.current || !session || result.status !== "ready") return;
    const controller = new AbortController();
    pending.current = controller;
    setBusy(true);
    setFailure(null);
    setNotice("");
    const next = !result.data.published;
    try {
      await setPostPublished(id, next, withTimeout(controller.signal), session.accessToken);
      if (!controller.signal.aborted) {
        retry();
        setNotice(next ? "Published" : "Moved to draft");
      }
    } catch (error) {
      if (!controller.signal.aborted) setFailure(error instanceof ApiError ? error.kind : "offline");
    } finally {
      if (!controller.signal.aborted) { pending.current = null; setBusy(false); }
    }
  }
  async function removePost() {
    if (pending.current || !confirmDelete || !session || result.status !== "ready") return;
    const controller = new AbortController();
    pending.current = controller;
    setBusy(true);
    setFailure(null);
    setNotice("");
    let completed = false;
    try {
      await deletePost(id, withTimeout(controller.signal), session.accessToken);
      if (!controller.signal.aborted) {
        router.replace("/?deleted=1");
        completed = true;
      }
    } catch (error) {
      if (!controller.signal.aborted) {
        setConfirmDelete(false);
        setFailure(error instanceof ApiError ? error.kind : "offline");
      }
    } finally {
      if (!controller.signal.aborted && !completed) { pending.current = null; setBusy(false); }
    }
  }
  // Action failures keep the post visible, so their IDs stay distinct from the load failures.
  const actionState = failure === "denied" ? "actionDenied" : failure === "conflict" ? "actionConflict" : failure === "notFound" ? "actionNotFound" : failure === "offline" ? "actionOffline" : failure === "badRequest" ? "actionBadRequest" : null;
  const identityPending = result.status === "ready" && !!session && identity === "loading";
  const state = result.status !== "ready" ? result.status : identityPending ? "loading" : actionState || (confirmDelete ? "confirmDelete" : null) || (admin ? "any.admin" : `${result.data.published ? "published" : "draft"}.${session ? result.data.author === session.userId ? "author" : "user" : "anonymous"}`);
  return <main className="wrap main" data-screen="S2" data-state={`PostDetail.${state}`}>
    {notice && result.status === "ready" && <p className="success-notice" role="status" data-screen={notice === "Published" || notice === "Saved" ? "P2" : undefined} data-state={notice === "Published" ? "Stamp.ok.published" : notice === "Saved" ? "Stamp.ok.saved" : undefined}>{notice}</p>}
    {result.status !== "ready" ? <ResponseState status={result.status} retry={reload} /> : identityPending ? <ResponseState status="loading" retry={reload} /> : <><article className="sheet">
      <span className={`tag ${result.data.published ? "pub" : "draft"}`}>{result.data.published ? "Published" : "Draft"}</span>
      <p className="mono post-id">{id}</p><h1>{result.data.title}</h1><p className="body">{result.data.body}</p>
      <p className="mono by">{result.data.author.slice(0, 8)}</p>
    </article>
      {session && (result.data.author === session.userId || admin) && <div className="detail-actions" aria-busy={busy}>
        <Link className="btn line" href={`/posts/${encodeURIComponent(id)}/edit`}>Edit</Link>
        <button className="btn line" type="button" disabled={busy || confirmDelete} onClick={togglePublished}>{busy && !confirmDelete ? "Changing" : result.data.published ? "Back to draft" : "Publish"}</button>
        <button ref={deleteButton} className="btn line danger" type="button" disabled={busy || confirmDelete} onClick={() => { setFailure(null); setNotice(""); setConfirmDelete(true); }}>Delete</button>
        {confirmDelete && <div className="delete-confirm" role="group" aria-labelledby="delete-question">
          <p id="delete-question">Delete this post?</p>
          <button className="btn danger" type="button" disabled={busy} onClick={removePost}>{busy ? "Deleting" : "Delete"}</button>
          <button className="btn line" type="button" disabled={busy} autoFocus onClick={() => { setConfirmDelete(false); requestAnimationFrame(() => deleteButton.current?.focus()); }}>Cancel</button>
        </div>}
        {failure === "denied" && <strong className="stamp" role="alert" data-screen="P2" data-state="Stamp.denied.act">Not allowed</strong>}
        {failure === "conflict" && <p role="alert">Already changed <button type="button" onClick={reload}>Reload</button></p>}
        {failure === "notFound" && <p className="empty" role="alert">Not found</p>}
        {failure === "badRequest" && <p className="invalid" role="alert">Check your input</p>}
        {failure === "offline" && <div className="offline" role="alert"><span>Can't connect</span><button type="button" disabled={busy} onClick={reload}>Try again</button></div>}
      </div>}
    </>}
    <Link href="/">Back to home</Link>
  </main>;
}
