// Supabase Auth REST only. Application rows always use the nyxis API.
export type Session = { accessToken: string; refreshToken: string; expiresAt: number; userId: string };
export class AuthError extends Error {
  constructor(public kind: "oauth" | "offline" | "configuration") { super(kind); }
}
const sessionKey = "nyxis.auth.session";
const pendingKey = "nyxis.auth.pending";
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
async function authRequest(path: string, init: RequestInit = {}) {
  const { base, key } = config();
  let response: Response;
  try {
    response = await fetch(base + path, { ...init, cache: "no-store", credentials: "omit", signal: AbortSignal.timeout(15000), headers: { apikey: key, "Content-Type": "application/json", ...init.headers } });
  } catch { throw new AuthError("offline"); }
  // 5xx and 429 (rate limiting) are not refusals. Keep the session and retry later.
  if (!response.ok) throw new AuthError(response.status >= 500 || response.status === 429 ? "offline" : "oauth");
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
export async function beginLogin(next: string) {
  const { base, key } = config();
  // Browser Web Crypto supplies the random verifier and SHA-256 implementation.
  const verifier = base64url(crypto.getRandomValues(new Uint8Array(32)));
  const challenge = base64url(new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(verifier))));
  sessionStorage.setItem(pendingKey, JSON.stringify({ verifier, next: safeNext(next), at: Date.now() }));
  const url = new URL(base + "/authorize");
  url.search = new URLSearchParams({ provider: "google", redirect_to: location.origin + "/auth/callback", code_challenge: challenge, code_challenge_method: "s256", apikey: key }).toString();
  location.assign(url.href);
}
async function tokenSession(grant: string, body: Record<string, string>): Promise<Session> {
  const data = await authJson(await authRequest("/token?grant_type=" + grant, { method: "POST", body: JSON.stringify(body) }));
  const { access_token, refresh_token, token_type, expires_in } = data;
  if (typeof access_token !== "string" || !access_token || typeof refresh_token !== "string" || !refresh_token || typeof token_type !== "string" || token_type.toLowerCase() !== "bearer" || typeof expires_in !== "number" || !Number.isFinite(expires_in) || expires_in <= 0) throw new AuthError("oauth");
  const user = await authJson(await authRequest("/user", { headers: { Authorization: "Bearer " + access_token } }));
  if (typeof user.id !== "string" || !user.id) throw new AuthError("oauth");
  return { accessToken: access_token, refreshToken: refresh_token, expiresAt: Date.now() + expires_in * 1000, userId: user.id };
}
// The authorization code can be exchanged once. The promise is shared by React Strict Mode's
// repeated effects and lives as long as this module; `resetLogin` (logout) discards it so a
// later visit to /auth/callback cannot resurrect the exchanged session.
let callback: Promise<{ session: Session; next: string }> | undefined;
export function finishLogin() {
  return callback ??= (async () => {
    const url = new URL(location.href);
    history.replaceState(null, "", "/auth/callback");
    const raw = sessionStorage.getItem(pendingKey);
    sessionStorage.removeItem(pendingKey);
    if (url.searchParams.has("error") || !url.searchParams.get("code") || !raw) throw new AuthError("oauth");
    let pending: Record<string, unknown>;
    try { pending = JSON.parse(raw); } catch { throw new AuthError("oauth"); }
    if (!pending || typeof pending !== "object" || typeof pending.verifier !== "string" || !/^[A-Za-z0-9_-]{43}$/.test(pending.verifier) || typeof pending.at !== "number" || !Number.isFinite(pending.at) || Date.now() - pending.at > 600000 || pending.at > Date.now()) throw new AuthError("oauth");
    const session = await tokenSession("pkce", { auth_code: url.searchParams.get("code")!, code_verifier: pending.verifier });
    return { session, next: safeNext(pending.next) };
  })();
}
export function resetLogin() { callback = undefined; }
export function saveSession(session: Session | null) {
  if (!session) { sessionStorage.removeItem(sessionKey); sessionStorage.removeItem(pendingKey); return; }
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
