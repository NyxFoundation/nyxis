// Supabase Auth REST only. Application rows always use the nyxis API.
export type Session = { accessToken: string; refreshToken: string; expiresAt: number; userId: string };
// oauth: Auth refused a code exchange or a token; offline: Auth unreachable or failing; configuration: missing public values;
// sendRefused: Auth would not send the sign-in email; codeRefused: Auth did not accept the one-time code.
export class AuthError extends Error {
  constructor(public kind: "oauth" | "offline" | "configuration" | "sendRefused" | "codeRefused") { super(kind); }
}
const sessionKey = "nyxis.auth.session";
const pendingKey = "nyxis.auth.pending";
// The emailed link usually opens in a new tab, which cannot see the sessionStorage of the tab that asked for the email.
const emailPendingKey = "nyxis.auth.pendingEmail";
const pendingTtl = 600000;
// The emailed link and code stay valid for as long as Auth's OTP expiry (one hour by default).
const emailPendingTtl = 3600000;
export const emailPattern = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
export const codePattern = /^\d{6,10}$/;
function config() {
  const base = process.env.NEXT_PUBLIC_SUPABASE_URL;
  const key = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY;
  if (!base || !key) throw new AuthError("configuration");
  const url = new URL(base);
  if (url.protocol !== "https:" && !(url.protocol === "http:" && ["localhost", "127.0.0.1"].includes(url.hostname))) throw new AuthError("configuration");
  return { base: url.href.replace(/\/$/, "") + "/auth/v1", key };
}
export function safeNext(value: unknown) {
  if (typeof value !== "string" || !value.startsWith("/") || value.startsWith("//") || /[\\\x00-\x20]/.test(value)) return "/";
  const url = new URL(value, "https://nyxis.invalid");
  if (url.origin !== "https://nyxis.invalid" || ["/login", "/auth/callback"].includes(url.pathname)) return "/";
  return url.pathname + url.search + url.hash;
}
// `refused` is the error for a 4xx answer; 429 (rate limiting) counts as unavailable unless `rateLimited` names another kind.
async function authRequest(path: string, init: RequestInit = {}, refused: AuthError["kind"] = "oauth", rateLimited: AuthError["kind"] = "offline") {
  const { base, key } = config();
  let response: Response;
  try {
    response = await fetch(base + path, { ...init, cache: "no-store", credentials: "omit", signal: AbortSignal.timeout(15000), headers: { apikey: key, "Content-Type": "application/json", ...init.headers } });
  } catch { throw new AuthError("offline"); }
  // 5xx is not a refusal. Keep the session and retry later.
  if (!response.ok) throw new AuthError(response.status >= 500 ? "offline" : response.status === 429 ? rateLimited : refused);
  return response;
}
// A malformed body with a 2xx from Auth is an Auth-side failure (treated like a network failure).
async function authJson(response: Response): Promise<Record<string, unknown>> {
  let data: unknown;
  try { data = await response.json(); } catch { throw new AuthError("offline"); }
  if (!data || typeof data !== "object") throw new AuthError("offline");
  return data as Record<string, unknown>;
}
function base64url(bytes: Uint8Array) {
  return btoa(String.fromCharCode(...bytes)).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}
// Browser Web Crypto supplies the random verifier and SHA-256 implementation.
async function pkce() {
  const verifier = base64url(crypto.getRandomValues(new Uint8Array(32)));
  const challenge = base64url(new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(verifier))));
  return { verifier, challenge };
}
export async function beginLogin(next: string) {
  const { base, key } = config();
  const { verifier, challenge } = await pkce();
  sessionStorage.setItem(pendingKey, JSON.stringify({ verifier, next: safeNext(next), at: Date.now() }));
  const url = new URL(base + "/authorize");
  url.search = new URLSearchParams({ provider: "google", redirect_to: location.origin + "/auth/callback", code_challenge: challenge, code_challenge_method: "s256", apikey: key }).toString();
  location.assign(url.href);
}
// Asks Auth to email a sign-in link and a one-time code. The link returns to /auth/callback with a PKCE code,
// so the verifier is kept where a new tab can read it; a first-time address becomes a new Auth user.
export async function beginEmailLogin(email: string, next: string) {
  const { verifier, challenge } = await pkce();
  localStorage.setItem(emailPendingKey, JSON.stringify({ verifier, next: safeNext(next), at: Date.now() }));
  await authRequest("/otp?" + new URLSearchParams({ redirect_to: location.origin + "/auth/callback" }), { method: "POST", body: JSON.stringify({ email, create_user: true, code_challenge: challenge, code_challenge_method: "s256" }) }, "sendRefused", "sendRefused");
}
async function sessionOf(response: Response): Promise<Session> {
  const data = await authJson(response);
  const { access_token, refresh_token, token_type, expires_in } = data;
  if (typeof access_token !== "string" || !access_token || typeof refresh_token !== "string" || !refresh_token || typeof token_type !== "string" || token_type.toLowerCase() !== "bearer" || typeof expires_in !== "number" || !Number.isFinite(expires_in) || expires_in <= 0) throw new AuthError("oauth");
  const user = await authJson(await authRequest("/user", { headers: { Authorization: "Bearer " + access_token } }));
  if (typeof user.id !== "string" || !user.id) throw new AuthError("oauth");
  return { accessToken: access_token, refreshToken: refresh_token, expiresAt: Date.now() + expires_in * 1000, userId: user.id };
}
function tokenSession(grant: string, body: Record<string, string>): Promise<Session> {
  return authRequest("/token?grant_type=" + grant, { method: "POST", body: JSON.stringify(body) }).then(sessionOf);
}
// The authorization code can be exchanged once. The promise is shared by React Strict Mode's
// repeated effects and lives as long as this module; `resetLogin` (logout) discards it so a
// later visit to /auth/callback cannot resurrect the exchanged session.
let callback: Promise<{ session: Session; next: string }> | undefined;
export function finishLogin() {
  return callback ??= (async () => {
    const url = new URL(location.href);
    history.replaceState(null, "", "/auth/callback");
    const fromTab = sessionStorage.getItem(pendingKey);
    const raw = fromTab ?? localStorage.getItem(emailPendingKey);
    sessionStorage.removeItem(pendingKey);
    localStorage.removeItem(emailPendingKey);
    if (url.searchParams.has("error") || !url.searchParams.get("code") || !raw) throw new AuthError("oauth");
    let pending: Record<string, unknown>;
    try { pending = JSON.parse(raw); } catch { throw new AuthError("oauth"); }
    const ttl = fromTab ? pendingTtl : emailPendingTtl;
    if (!pending || typeof pending !== "object" || typeof pending.verifier !== "string" || !/^[A-Za-z0-9_-]{43}$/.test(pending.verifier) || typeof pending.at !== "number" || !Number.isFinite(pending.at) || Date.now() - pending.at > ttl || pending.at > Date.now()) throw new AuthError("oauth");
    const session = await tokenSession("pkce", { auth_code: url.searchParams.get("code")!, code_verifier: pending.verifier });
    return { session, next: safeNext(pending.next) };
  })();
}
// The one-time code gets the session straight from Auth; the result is handed to /auth/callback for registration.
export async function verifyEmailCode(email: string, code: string, next: string) {
  const session = await sessionOf(await authRequest("/verify", { method: "POST", body: JSON.stringify({ type: "email", email, token: code }) }, "codeRefused", "codeRefused"));
  localStorage.removeItem(emailPendingKey);
  callback = Promise.resolve({ session, next: safeNext(next) });
}
export function pendingLogin() { return callback !== undefined; }
export function resetLogin() { callback = undefined; }
export function saveSession(session: Session | null) {
  if (!session) { sessionStorage.removeItem(sessionKey); sessionStorage.removeItem(pendingKey); localStorage.removeItem(emailPendingKey); return; }
  sessionStorage.setItem(sessionKey, JSON.stringify({ ...session, authBase: config().base }));
}
export function storedSession(): Session | null {
  try {
    const raw = sessionStorage.getItem(sessionKey);
    if (!raw) return null;
    const data = JSON.parse(raw);
    if (!data || typeof data !== "object" || data.authBase !== config().base || typeof data.accessToken !== "string" || typeof data.refreshToken !== "string" || typeof data.userId !== "string" || !Number.isFinite(data.expiresAt)) return null;
    return { accessToken: data.accessToken, refreshToken: data.refreshToken, expiresAt: data.expiresAt, userId: data.userId };
  } catch { return null; }
}
export function refreshSession(session: Pick<Session, "refreshToken">) { return tokenSession("refresh_token", { refresh_token: session.refreshToken }); }
export async function revokeSession(session: Pick<Session, "accessToken">) {
  await authRequest("/logout?scope=local", { method: "POST", headers: { Authorization: "Bearer " + session.accessToken } });
}
