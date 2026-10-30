// App data is fetched only from the nyxis HTTP API.
export type Post = { title: string; body: string; author: string; published: boolean };
export type PostEntry = Post & { id: string };
export type User = { admin: boolean };
export type Failure = "denied" | "notFound" | "badRequest" | "conflict" | "offline";
export class ApiError extends Error {
  // Only on 400, message holds the backend's plain-text sentence (the screen shows what was wrong with the input).
  constructor(public kind: Failure, message: string = kind) { super(message); }
}
export const requestTimeout = 15000;
export function withTimeout(signal: AbortSignal) { return AbortSignal.any([signal, AbortSignal.timeout(requestTimeout)]); }
export async function apiRequest(path: string, signal: AbortSignal, token?: string, init: RequestInit = {}, accepted: number[] = []): Promise<Response> {
  const base = process.env.NEXT_PUBLIC_NYXIS_API_URL || "http://127.0.0.1:8080";
  let response: Response;
  try { response = await fetch(base.replace(/\/$/, "") + path, { ...init, signal, cache: "no-store", credentials: "omit", headers: { ...(init.body ? { "Content-Type": "application/json" } : {}), ...init.headers, ...(token ? { Authorization: `Bearer ${token}` } : {}) } }); }
  catch (error) {
    if (signal.aborted) throw error;
    throw new ApiError("offline");
  }
  if (!response.ok && !accepted.includes(response.status)) {
    const kinds: Record<number, Failure> = { 400: "badRequest", 403: "denied", 404: "notFound", 409: "conflict" };
    const kind = kinds[response.status] || "offline";
    throw new ApiError(kind, kind === "badRequest" ? (await response.text().catch(() => "")).trim() || kind : kind);
  }
  return response;
}
export async function readApi(path: string, signal: AbortSignal, token?: string): Promise<unknown> {
  const response = await apiRequest(path, signal, token);
  try { return await response.json(); } catch { throw new ApiError("offline"); }
}
export function isPost(value: unknown): value is Post {
  if (!value || typeof value !== "object") return false;
  const row = value as Record<string, unknown>;
  return typeof row.title === "string" && typeof row.body === "string" && typeof row.author === "string" && typeof row.published === "boolean";
}
export function isEntry(value: unknown): value is PostEntry {
  return isPost(value) && "id" in value && typeof value.id === "string";
}
export function isUser(value: unknown): value is User {
  return !!value && typeof value === "object" && "admin" in value && typeof (value as Record<string, unknown>).admin === "boolean";
}
export type NewPost = Pick<Post, "title" | "body" | "published">;
export async function createPost(id: string, post: NewPost, signal: AbortSignal, token: string) {
  // Only content is sent. The backend derives the author from the verified JWT.
  const response = await apiRequest(`/posts/${encodeURIComponent(id)}`, signal, token, {
    method: "POST", body: JSON.stringify({ title: post.title, body: post.body, published: post.published })
  });
  if (response.status !== 201) throw new ApiError("offline");
}
export async function editPost(id: string, post: Pick<Post, "title" | "body">, signal: AbortSignal, token: string) {
  const response = await apiRequest(`/posts/${encodeURIComponent(id)}`, signal, token, {
    method: "PATCH", body: JSON.stringify({ title: post.title, body: post.body })
  });
  if (response.status !== 204) throw new ApiError("offline");
}
export async function setPostPublished(id: string, published: boolean, signal: AbortSignal, token: string) {
  const response = await apiRequest(`/posts/${encodeURIComponent(id)}/${published ? "publish" : "unpublish"}`, signal, token, { method: "POST" });
  if (response.status !== 204) throw new ApiError("offline");
}
export async function deletePost(id: string, signal: AbortSignal, token: string) {
  const response = await apiRequest(`/posts/${encodeURIComponent(id)}`, signal, token, { method: "DELETE" });
  if (response.status !== 204) throw new ApiError("offline");
}
// The user row. Only the user themselves and admins can read it; an unregistered user is notFound.
export async function readUser(id: string, signal: AbortSignal, token?: string): Promise<User> {
  const value = await readApi(`/users/${encodeURIComponent(id)}`, signal, token);
  if (!isUser(value)) throw new ApiError("offline");
  return value;
}
// Registers your own row as a non-admin. If it already exists, the 409 is treated as success.
export async function registerUser(id: string, signal: AbortSignal, token: string): Promise<"registered" | "alreadyRegistered"> {
  const response = await apiRequest(`/users/${encodeURIComponent(id)}`, signal, token, { method: "POST", body: JSON.stringify({ admin: false }) }, [409]);
  if (response.status === 201) return "registered";
  if (response.status === 409) return "alreadyRegistered";
  throw new ApiError("offline");
}
export async function setAdmin(id: string, admin: boolean, signal: AbortSignal, token: string) {
  const response = await apiRequest(`/users/${encodeURIComponent(id)}/admin`, signal, token, { method: "PUT", body: JSON.stringify({ admin }) });
  if (response.status !== 204) throw new ApiError("offline");
}
