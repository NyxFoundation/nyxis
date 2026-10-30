"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { createContext, useCallback, useContext, useEffect, useRef, useState, type ReactNode } from "react";
import { AuthError, beginLogin, finishLogin, refreshSession, resetLogin, revokeSession, safeNext, saveSession, storedSession, type Session } from "../lib/auth";
import { ApiError, readUser, registerUser, withTimeout, type Failure } from "../lib/api";

// Who you are viewing as right now, determined by the user row. Failure means fetching the row failed (whether you are an admin is unknown).
export type Identity = "loading" | "anonymous" | "user" | "admin" | "unregistered" | Failure;
type Auth = { acceptSession: (value: Session) => void; identity: Identity; refreshIdentity: () => void; ready: boolean; session: Session | null; notice: string; expired: boolean; logout: () => Promise<void> };
const Context = createContext<Auth | null>(null);
export function useAuth() { const auth = useContext(Context); if (!auth) throw new Error("AuthProvider missing"); return auth; }
const retryAfter = 30000;
export function AuthProvider({ children }: { children: ReactNode }) {
  const pathname = usePathname();
  const [session, setSession] = useState<Session | null>(null);
  const [ready, setReady] = useState(false);
  const [notice, setNotice] = useState("");
  const [expired, setExpired] = useState(false);
  const [identity, setIdentity] = useState<Identity>("loading");
  const [identityVersion, setIdentityVersion] = useState(0);
  const [restoreAttempt, setRestoreAttempt] = useState(0);
  const refreshIdentity = useCallback(() => { setIdentity("loading"); setIdentityVersion(n => n + 1); }, []);
  useEffect(() => {
    const controller = new AbortController();
    setIdentity(!ready ? "loading" : !session ? "anonymous" : "loading");
    if (ready && session) readUser(session.userId, withTimeout(controller.signal), session.accessToken).then(user => {
      if (!controller.signal.aborted) setIdentity(user.admin ? "admin" : "user");
    }).catch(error => { if (!controller.signal.aborted) setIdentity(error instanceof ApiError ? error.kind === "notFound" ? "unregistered" : error.kind : "offline"); });
    return () => controller.abort();
  }, [ready, session?.userId, identityVersion]);
  const revision = useRef(0);
  const restore = useRef<Promise<Session> | null>(null);
  const acceptSession = useCallback((value: Session) => { saveSession(value); revision.current++; setSession(value); setReady(true); setNotice(""); setExpired(false); }, []);
  // Only Auth's refusal ends a session. Unreachable Auth keeps the session and retries.
  const expire = useCallback(() => { revision.current++; setSession(null); try { saveSession(null); } catch {} setExpired(true); setNotice("Your sign-in has expired"); setReady(true); }, []);
  async function logout() {
    revision.current++;
    resetLogin();
    const current = session;
    setSession(null); setReady(true); setExpired(false); setNotice("Signed out");
    try { saveSession(null); } catch { setNotice("Signed out. Couldn't clear the data saved in the browser"); }
    if (current) try { await revokeSession(current); } catch (error) {
      // A refused revocation (already expired or revoked) is a completed logout.
      if (error instanceof AuthError && error.kind === "offline") setNotice("Signed out. Can't connect. Couldn't complete the sign-out on the server");
    }
    if (location.pathname === "/auth/callback") location.replace("/login");
  }
  useEffect(() => {
    if (!notice.startsWith("Signed out")) return;
    const timer = setTimeout(() => setNotice(""), 4000);
    return () => clearTimeout(timer);
  }, [notice]);
  useEffect(() => {
    if (location.pathname === "/auth/callback") { setReady(true); return; }
    const saved = storedSession();
    if (!saved) { setReady(true); return; }
    const version = revision.current;
    let active = true;
    let retry: ReturnType<typeof setTimeout> | undefined;
    // One refresh per stored token, shared by Strict Mode's repeated effects (refresh tokens rotate).
    const pending = restore.current ??= refreshSession(saved);
    pending.then(value => { if (active && version === revision.current) acceptSession(value); }).catch(error => {
      if (!active || version !== revision.current) return;
      restore.current = null;
      if (error instanceof AuthError && error.kind === "offline") {
        setNotice("Can't connect. Couldn't check your sign-in"); setReady(true);
        retry = setTimeout(() => setRestoreAttempt(n => n + 1), retryAfter);
      } else expire();
    });
    return () => { active = false; clearTimeout(retry); };
  }, [restoreAttempt, acceptSession, expire]);
  useEffect(() => {
    if (!session) return;
    const version = revision.current;
    let active = true;
    let pending = false;
    let retry: ReturnType<typeof setTimeout> | undefined;
    async function refresh() {
      if (pending || !active || version !== revision.current) return;
      pending = true;
      try { const value = await refreshSession(session!); if (active && version === revision.current) acceptSession(value); }
      catch (error) {
        if (!active || version !== revision.current) return;
        pending = false;
        if (error instanceof AuthError && error.kind === "offline") {
          setNotice("Can't connect. Couldn't renew your sign-in");
          retry = setTimeout(() => void refresh(), retryAfter);
        } else expire();
      }
    }
    const timer = setTimeout(refresh, Math.max(1000, session.expiresAt - Date.now() - 60000));
    const visible = () => { if (document.visibilityState === "visible" && Date.now() >= session.expiresAt - 60000) void refresh(); };
    document.addEventListener("visibilitychange", visible);
    return () => { active = false; clearTimeout(timer); clearTimeout(retry); document.removeEventListener("visibilitychange", visible); };
  }, [session, acceptSession, expire]);
  // Private content remounts when the person changes (login, logout, another account), not when
  // a token rotates. The callback owns the exchange and must stay mounted when it publishes the session.
  return <Context.Provider value={{ ready, session, notice, expired, logout, identity, refreshIdentity, acceptSession }}><div key={pathname === "/auth/callback" ? "callback" : session?.userId ?? "anonymous"}>{children}</div></Context.Provider>;
}
export function Header() {
  const pathname = usePathname();
  const { ready, session, logout, notice, identity: storedIdentity } = useAuth();
  const identity = !ready ? "loading" : !session ? "anonymous" : storedIdentity;
  // State IDs follow design/screens.md: checking while the row loads, adminUnknown when it could not be read.
  const state = identity === "loading" ? "checking" : ["anonymous", "user", "admin", "unregistered"].includes(identity) ? identity : "adminUnknown";
  return <><header className="wrap header" data-screen="P1" data-state={`Header.${state}`}>
    <Link className="wordmark" href="/"><i aria-hidden="true" />Nyxis Board</Link>
    <nav aria-label="Menu"><Link href="/" aria-current={pathname === "/" ? "page" : undefined}>Home</Link>{ready && session && <Link href="/posts/new" aria-current={pathname === "/posts/new" ? "page" : undefined}>New post</Link>}{identity === "admin" && <Link href="/admin" aria-current={pathname === "/admin" ? "page" : undefined}>Admin</Link>}</nav>
    <Link className="who" href="/me" aria-label="You" aria-current={pathname === "/me" ? "page" : undefined}><span className={`avatar ${!session ? "guest" : identity === "admin" ? "administrator" : identity === "unregistered" ? "unregistered" : "member"}`} aria-hidden="true">{session?.userId.slice(0, 2)}</span>{identity === "admin" ? <span className="tag admin-tag">Admin</span> : !ready ? "Checking" : session ? "Signed in" : "Guest"}</Link>
    {ready && (session ? <button className="btn line" onClick={() => void logout()}>Sign out</button> : <Link className="btn line" href={`/login?next=${encodeURIComponent(pathname)}`}>Sign in with Google</Link>)}
  </header>{notice && <p className="wrap" role="status">{notice}</p>}</>;
}
export function Login() {
  const { ready, session, logout } = useAuth();
  const [failure, setFailure] = useState("");
  const [busy, setBusy] = useState(false);
  const [next, setNext] = useState("/");
  useEffect(() => { const query = new URLSearchParams(location.search); setFailure(query.get("error") || ""); setNext(safeNext(query.get("next"))); }, []);
  async function start() {
    setBusy(true); setFailure("");
    try { await beginLogin(next); } catch (error) { setFailure(error instanceof AuthError ? error.kind : "oauth"); setBusy(false); }
  }
  return <main className="wrap main auth-main" data-screen="S5" data-state={`Login.${session ? "alreadyLoggedIn" : failure === "offline" ? "authOffline" : failure ? "oauthError" : "anonymous"}`}>
    <i className="brand-square" aria-hidden="true" /><h1>Nyxis Board</h1>
    {failure && <p className={failure === "offline" ? "offline" : ""} role="alert">{failure === "offline" ? "Can't connect" : "Couldn't sign in"}</p>}
    {session ? <><p>You're signed in</p><Link className="btn" href="/">Go home</Link><button className="btn line" onClick={() => void logout()}>Sign out</button></> : <><button className="btn google" disabled={busy || !ready} onClick={() => void start()}><img src="/google-g.png" width="20" height="20" alt="" />Sign in with Google</button><Link href={next}>Browse without signing in</Link></>}
  </main>;
}
type Exchange = Awaited<ReturnType<typeof finishLogin>>;
export function AuthCallback() {
  const { acceptSession, session } = useAuth();
  const [phase, setPhase] = useState("exchanging");
  const [failure, setFailure] = useState("");
  const [attempt, setAttempt] = useState(0);
  // The exchange happens once per visit; retries only repeat the registration with the current session.
  const exchange = useRef<Promise<Exchange> | null>(null);
  const current = useRef(session);
  useEffect(() => { current.current = session; }, [session]);
  useEffect(() => {
    let active = true;
    const controller = new AbortController();
    async function run() {
      if (!exchange.current) {
        const query = new URL(location.href).searchParams;
        if (!query.has("code") && !query.has("error")) { location.replace("/login"); return; }
        exchange.current = finishLogin();
      }
      let result: Exchange;
      try { result = await exchange.current; }
      catch (error) { if (active) location.replace(`/login?error=${error instanceof AuthError && error.kind === "offline" ? "offline" : "oauth"}`); return; }
      if (!active) return;
      let live = current.current;
      if (live?.userId !== result.session.userId) {
        try { acceptSession(result.session); } catch { location.replace("/login?error=storage"); return; }
        live = result.session;
      }
      setPhase("registering"); setFailure("");
      try {
        const outcome = await registerUser(result.session.userId, withTimeout(controller.signal), live.accessToken);
        if (!active || storedSession()?.userId !== result.session.userId) return;
        setPhase(outcome);
      } catch (error) {
        if (active) setFailure(error instanceof ApiError ? error.kind : "offline");
        return;
      }
      if (active) location.replace(result.next);
    }
    void run();
    return () => { active = false; controller.abort(); };
  }, [attempt, acceptSession]);
  async function proceed() {
    try { location.replace((await exchange.current!).next); } catch { location.replace("/login?error=oauth"); }
  }
  return <main className="wrap main auth-main" data-screen="S6" data-state={`AuthCallback.${failure ? failure === "denied" ? "registerDenied" : failure === "badRequest" ? "registerBadRequest" : "registerOffline" : phase}`} aria-live="polite">
    <i className="brand-square" aria-hidden="true" /><h1>Signing in</h1>
    <ol className="auth-steps" aria-label="Progress"><li className={phase !== "exchanging" ? "done" : ""}>Google</li><li className={phase === "registered" || phase === "alreadyRegistered" ? "done" : ""}>Registration</li><li>Go home</li></ol>
    {failure && <><p className={failure === "offline" ? "offline" : "stamp"} role="alert">{failure === "offline" ? "Can't connect" : "Not allowed"}</p><button className="btn" disabled={!session} onClick={() => setAttempt(n => n + 1)}>Try again</button><button className="btn line" disabled={!session} onClick={() => void proceed()}>Continue without registering</button></>}
  </main>;
}
