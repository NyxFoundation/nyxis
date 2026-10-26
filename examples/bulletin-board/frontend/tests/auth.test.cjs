// Run with Node >=22. Compile into a disposable directory; no extra dependency.
const { test, before, after, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const { mkdtempSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const path = require('node:path');
const dir = mkdtempSync(path.join(tmpdir(), 'nyxis-auth-test-'));
let auth, api, requests, values, navigated;
const sessionResponse = { access_token: 'test-access', refresh_token: 'test-refresh', token_type: 'bearer', expires_in: 3600 };
before(() => {
  execFileSync(process.execPath, ['node_modules/typescript/bin/tsc', 'lib/auth.ts', 'lib/api.ts', '--outDir', dir, '--module', 'commonjs', '--target', 'ES2022', '--skipLibCheck'], { stdio: 'pipe', cwd: path.resolve(__dirname, '..') });
  process.env.NEXT_PUBLIC_SUPABASE_URL = 'http://127.0.0.1:55321';
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY = 'public-test-key';
  process.env.NEXT_PUBLIC_NYXIS_API_URL = 'http://127.0.0.1:8080';
});
after(() => rmSync(dir, { recursive: true, force: true }));
beforeEach(() => {
  delete require.cache[require.resolve(path.join(dir, 'auth.js'))];
  auth = require(path.join(dir, 'auth.js')); api = require(path.join(dir, 'api.js'));
  values = new Map(); requests = []; navigated = null;
  global.sessionStorage = { getItem: key => values.get(key) ?? null, setItem: (key, value) => values.set(key, value), removeItem: key => values.delete(key) };
  global.location = { origin: 'http://127.0.0.1:3000', href: 'http://127.0.0.1:3000/auth/callback?code=one-use', assign: value => navigated = value };
  global.history = { replaceState: (_a, _b, url) => location.href = location.origin + url };
  global.fetch = async (url, init) => { requests.push({ url, init }); return Response.json(url.endsWith('/user') ? { id: 'verified-user' } : sessionResponse); };
});
test('external, backslash, control and auth-loop destinations are refused', () => {
  for (const dest of ['https://bad.invalid', '//bad.invalid', '/\\bad.invalid', '/\n/evil', '/login', '/auth/callback?code=other', '/a/../login', null]) assert.equal(auth.safeNext(dest), '/');
  assert.equal(auth.safeNext('/posts/draft1?x=1#body'), '/posts/draft1?x=1#body');
});
test('PKCE uses browser SHA-256, fresh verifier and fixed same-origin callback', async () => {
  await auth.beginLogin('/posts/draft1');
  const first = JSON.parse(values.get('nyxis.auth.pending'));
  const url = new URL(navigated);
  const digest = Buffer.from(await crypto.subtle.digest('SHA-256', new TextEncoder().encode(first.verifier))).toString('base64url');
  assert.equal(url.searchParams.get('code_challenge'), digest);
  assert.equal(url.searchParams.get('code_challenge_method'), 's256');
  assert.equal(url.searchParams.get('redirect_to'), location.origin + '/auth/callback');
  assert.equal(url.searchParams.get('provider'), 'google');
  assert.ok(!navigated.includes(first.verifier));
  await auth.beginLogin('//bad.invalid');
  const second = JSON.parse(values.get('nyxis.auth.pending'));
  assert.notEqual(second.verifier, first.verifier); assert.equal(second.next, '/');
});
test('callback exchanges only once, removes code/verifier and uses Auth /user identity', async () => {
  await auth.beginLogin('/posts/draft1');
  const pending = JSON.parse(values.get('nyxis.auth.pending'));
  const [a, b] = await Promise.all([auth.finishLogin(), auth.finishLogin()]);
  assert.deepEqual(a, b); assert.equal(a.session.userId, 'verified-user'); assert.equal(a.next, '/posts/draft1');
  assert.equal(requests.length, 2); assert.ok(requests[0].url.endsWith('/token?grant_type=pkce'));
  assert.deepEqual(JSON.parse(requests[0].init.body), { auth_code: 'one-use', code_verifier: pending.verifier });
  assert.equal(requests[1].init.headers.Authorization, 'Bearer test-access');
  assert.equal(values.has('nyxis.auth.pending'), false); assert.equal(location.href, location.origin + '/auth/callback');
});
test('missing and stale PKCE state cannot exchange', async () => {
  await assert.rejects(auth.finishLogin()); assert.equal(requests.length, 0);
});
test('expired PKCE state is consumed without sending a token request', async () => {
  values.set('nyxis.auth.pending', JSON.stringify({ verifier: 'a'.repeat(43), at: Date.now() - 600001, next: '/' }));
  await assert.rejects(auth.finishLogin()); assert.equal(requests.length, 0); assert.equal(values.size, 0);
});
test('OAuth error cannot create a session', async () => {
  await auth.beginLogin('/'); location.href += '&error=access_denied';
  await assert.rejects(auth.finishLogin()); assert.equal(requests.length, 0);
});
test('refresh rotates token, validates user, persists only within this Auth base', async () => {
  const session = await auth.refreshSession({ refreshToken: 'old-refresh' });
  assert.deepEqual(JSON.parse(requests[0].init.body), { refresh_token: 'old-refresh' });
  assert.equal(session.userId, 'verified-user'); assert.equal(session.refreshToken, 'test-refresh');
  auth.saveSession(session); assert.equal(auth.storedSession().accessToken, 'test-access');
  process.env.NEXT_PUBLIC_SUPABASE_URL = 'https://other.invalid'; assert.equal(auth.storedSession(), null);
  process.env.NEXT_PUBLIC_SUPABASE_URL = 'http://127.0.0.1:55321';
  auth.saveSession(null); assert.equal(values.size, 0);
});
test('Auth denial, unavailable Auth and unverified identity fail closed', async () => {
  global.fetch = async () => new Response('', { status: 400 });
  await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'oauth');
  for (const status of [429, 503]) {
    global.fetch = async () => new Response('', { status });
    await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'offline');
  }
  global.fetch = async () => { throw new Error('network'); };
  await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'offline');
  global.fetch = async url => Response.json(url.endsWith('/user') ? {} : sessionResponse);
  await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'oauth');
});
test('logout revokes current session only; nyxis sends bearer only when supplied', async () => {
  await auth.revokeSession({ accessToken: 'test-access' });
  assert.ok(requests[0].url.endsWith('/logout?scope=local'));
  await api.readApi('/posts', new AbortController().signal, 'test-access');
  assert.equal(requests[1].url, 'http://127.0.0.1:8080/posts');
  assert.equal(requests[1].init.headers.Authorization, 'Bearer test-access');
  await api.readApi('/posts', new AbortController().signal);
  assert.equal(requests[2].init.headers.Authorization, undefined);
  assert.equal(requests[2].init.credentials, 'omit');
});
test('registration conflict is accepted; backend denial stays distinct', async () => {
  global.fetch = async () => new Response('', { status: 409 });
  assert.equal((await api.apiRequest('/users/self', new AbortController().signal, 'test-access', { method: 'POST', body: '{"admin":false}' }, [409])).status, 409);
  global.fetch = async () => new Response('', { status: 403 });
  await assert.rejects(api.readApi('/posts/draft1', new AbortController().signal, 'test-access'), error => error.kind === 'denied');
});
test('post creation sends content and JWT without trusting a supplied author', async () => {
  global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 201 }); };
  for (const published of [false, true]) {
    await api.createPost('post/id', { title: '題名', body: '本文', published, author: 'other-user' }, new AbortController().signal, 'test-access');
    const request = requests.at(-1);
    assert.equal(request.url, 'http://127.0.0.1:8080/posts/post%2Fid');
    assert.equal(request.init.method, 'POST');
    assert.equal(request.init.headers.Authorization, 'Bearer test-access');
    assert.equal(request.init.headers['Content-Type'], 'application/json');
    assert.equal(request.init.credentials, 'omit');
    assert.deepEqual(JSON.parse(request.init.body), { title: '題名', body: '本文', published });
  }
});
test('creation distinguishes denial, conflict, bad input and unavailable backend', async () => {
  for (const [status, kind] of [[403, 'denied'], [409, 'conflict'], [400, 'badRequest'], [503, 'offline'], [200, 'offline'], [204, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.createPost('post', { title: 'a', body: 'b', published: false }, new AbortController().signal, 'test-access'), error => error.kind === kind);
  }
  global.fetch = async () => { throw new Error('network'); };
  await assert.rejects(api.createPost('post', { title: 'a', body: 'b', published: true }, new AbortController().signal, 'test-access'), error => error.kind === 'offline');
});
test('editing sends only title/body; author and publication cannot ride along', async () => {
  global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 204 }); };
  await api.editPost('post/id', { title: '新しい題名', body: '新しい本文', author: 'other', published: true }, new AbortController().signal, 'test-access');
  const request = requests.at(-1);
  assert.equal(request.url, 'http://127.0.0.1:8080/posts/post%2Fid');
  assert.equal(request.init.method, 'PATCH');
  assert.equal(request.init.headers.Authorization, 'Bearer test-access');
  assert.equal(request.init.credentials, 'omit');
  assert.deepEqual(JSON.parse(request.init.body), { title: '新しい題名', body: '新しい本文' });
});
test('editing keeps refusal, absence, conflict, invalid input and connection failure distinct', async () => {
  for (const [status, kind] of [[403, 'denied'], [404, 'notFound'], [409, 'conflict'], [400, 'badRequest'], [503, 'offline'], [200, 'offline'], [201, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.editPost('post', { title: 'a', body: 'b' }, new AbortController().signal, 'test-access'), error => error.kind === kind);
  }
  global.fetch = async () => { throw new Error('network'); };
  await assert.rejects(api.editPost('post', { title: 'a', body: 'b' }, new AbortController().signal, 'test-access'), error => error.kind === 'offline');
});

test('publication uses independent bodyless endpoints and requires 204', async () => {
  for (const published of [true, false]) {
    global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 204 }); };
    await api.setPostPublished('post/id', published, new AbortController().signal, 'test-access');
    const request = requests.at(-1);
    assert.equal(request.url, `http://127.0.0.1:8080/posts/post%2Fid/${published ? 'publish' : 'unpublish'}`);
    assert.equal(request.init.method, 'POST');
    assert.equal(request.init.body, undefined);
    assert.equal(request.init.headers.Authorization, 'Bearer test-access');
    assert.equal(request.init.credentials, 'omit');
    for (const [status, kind] of [[403, 'denied'], [404, 'notFound'], [409, 'conflict'], [400, 'badRequest'], [503, 'offline'], [200, 'offline'], [201, 'offline']]) {
      global.fetch = async () => new Response(null, { status });
      await assert.rejects(api.setPostPublished('post', published, new AbortController().signal, 'test-access'), error => error.kind === kind);
    }
    global.fetch = async () => { throw new Error('network'); };
    await assert.rejects(api.setPostPublished('post', published, new AbortController().signal, 'test-access'), error => error.kind === 'offline');
  }
});

test('deletion encodes the ID, sends bodyless DELETE and accepts only 204', async () => {
  global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 204 }); };
  const signal = new AbortController().signal;
  await api.deletePost('post/id', signal, 'test-access');
  const request = requests.at(-1);
  assert.equal(request.url, 'http://127.0.0.1:8080/posts/post%2Fid');
  assert.equal(request.init.method, 'DELETE');
  assert.equal(request.init.body, undefined);
  assert.equal(request.init.headers.Authorization, 'Bearer test-access');
  assert.equal(request.init.credentials, 'omit');
  assert.equal(request.init.signal, signal);
  for (const [status, kind] of [[403, 'denied'], [404, 'notFound'], [409, 'conflict'], [400, 'badRequest'], [503, 'offline'], [200, 'offline'], [201, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.deletePost('post', signal, 'test-access'), error => error.kind === kind);
  }
  global.fetch = async () => { throw new Error('network'); };
  await assert.rejects(api.deletePost('post', signal, 'test-access'), error => error.kind === 'offline');
});

test('user registration, lookup and admin change use the documented routes and statuses', async () => {
  global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 201 }); };
  assert.equal(await api.registerUser('user/id', new AbortController().signal, 'test-access'), 'registered');
  let request = requests.at(-1);
  assert.equal(request.url, 'http://127.0.0.1:8080/users/user%2Fid');
  assert.equal(request.init.method, 'POST');
  assert.equal(request.init.headers.Authorization, 'Bearer test-access');
  assert.deepEqual(JSON.parse(request.init.body), { admin: false });
  global.fetch = async () => new Response(null, { status: 409 });
  assert.equal(await api.registerUser('user', new AbortController().signal, 'test-access'), 'alreadyRegistered');
  for (const [status, kind] of [[403, 'denied'], [400, 'badRequest'], [503, 'offline'], [200, 'offline'], [204, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.registerUser('user', new AbortController().signal, 'test-access'), error => error.kind === kind);
  }
  global.fetch = async (url, init) => { requests.push({ url, init }); return Response.json({ admin: true }); };
  assert.deepEqual(await api.readUser('user/id', new AbortController().signal), { admin: true });
  request = requests.at(-1);
  assert.equal(request.url, 'http://127.0.0.1:8080/users/user%2Fid');
  assert.equal(request.init.headers.Authorization, undefined);
  for (const body of [{}, { admin: 'true' }, [], null, 'x']) {
    global.fetch = async () => Response.json(body);
    await assert.rejects(api.readUser('user', new AbortController().signal, 'test-access'), error => error.kind === 'offline');
  }
  for (const [status, kind] of [[403, 'denied'], [404, 'notFound'], [503, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.readUser('user', new AbortController().signal, 'test-access'), error => error.kind === kind);
  }
  global.fetch = async (url, init) => { requests.push({ url, init }); return new Response(null, { status: 204 }); };
  await api.setAdmin('user/id', false, new AbortController().signal, 'test-access');
  request = requests.at(-1);
  assert.equal(request.url, 'http://127.0.0.1:8080/users/user%2Fid/admin');
  assert.equal(request.init.method, 'PUT');
  assert.equal(request.init.headers.Authorization, 'Bearer test-access');
  assert.deepEqual(JSON.parse(request.init.body), { admin: false });
  for (const [status, kind] of [[403, 'denied'], [404, 'notFound'], [400, 'badRequest'], [503, 'offline'], [200, 'offline']]) {
    global.fetch = async () => new Response(null, { status });
    await assert.rejects(api.setAdmin('user', true, new AbortController().signal, 'test-access'), error => error.kind === kind);
  }
});
test('a 2xx without JSON is unavailable; 400 carries the backend sentence; aborts pass through unchanged', async () => {
  global.fetch = async () => new Response('not json', { status: 200 });
  await assert.rejects(api.readApi('/posts', new AbortController().signal), error => error.kind === 'offline');
  global.fetch = async () => new Response('title and body expected', { status: 400 });
  await assert.rejects(api.readApi('/posts', new AbortController().signal), error => error.kind === 'badRequest' && error.message === 'title and body expected');
  global.fetch = async () => new Response('', { status: 400 });
  await assert.rejects(api.readApi('/posts', new AbortController().signal), error => error.kind === 'badRequest' && error.message === 'badRequest');
  const controller = new AbortController();
  const aborted = new Error('aborted'); aborted.name = 'AbortError';
  global.fetch = async () => { controller.abort(); throw aborted; };
  await assert.rejects(api.readApi('/posts', controller.signal), error => error === aborted);
});
test('token responses with a wrong type, missing refresh token, invalid expiry or non-JSON body fail closed', async () => {
  for (const body of [{ ...sessionResponse, token_type: 'mac' }, { ...sessionResponse, refresh_token: '' }, { ...sessionResponse, expires_in: 0 }, { ...sessionResponse, expires_in: '3600' }, null, 'text']) {
    global.fetch = async url => url.endsWith('/user') ? Response.json({ id: 'verified-user' }) : Response.json(body);
    await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === (body && typeof body === 'object' ? 'oauth' : 'offline'));
  }
  global.fetch = async () => new Response('<html>', { status: 200 });
  await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'offline');
});
test('Auth configuration must be HTTPS or a local HTTP address', async () => {
  for (const base of ['http://auth.example.test', 'ftp://127.0.0.1', '']) {
    process.env.NEXT_PUBLIC_SUPABASE_URL = base;
    await assert.rejects(auth.refreshSession({ refreshToken: 'old' }), error => error.kind === 'configuration');
  }
  process.env.NEXT_PUBLIC_SUPABASE_URL = 'http://127.0.0.1:55321';
});
test('implicit-flow fragments, malformed pending state and future timestamps cannot exchange', async () => {
  values.set('nyxis.auth.pending', JSON.stringify({ verifier: 'a'.repeat(43), at: Date.now(), next: '/' }));
  location.href = 'http://127.0.0.1:3000/auth/callback#access_token=leaked&token_type=bearer';
  await assert.rejects(auth.finishLogin(), error => error.kind === 'oauth'); assert.equal(requests.length, 0);
  auth.resetLogin();
  values.set('nyxis.auth.pending', '{not json');
  location.href = 'http://127.0.0.1:3000/auth/callback?code=one-use';
  await assert.rejects(auth.finishLogin(), error => error.kind === 'oauth'); assert.equal(requests.length, 0);
  auth.resetLogin();
  values.set('nyxis.auth.pending', JSON.stringify({ verifier: 'a'.repeat(43), at: Date.now() + 60000, next: '/' }));
  location.href = 'http://127.0.0.1:3000/auth/callback?code=one-use';
  await assert.rejects(auth.finishLogin(), error => error.kind === 'oauth'); assert.equal(requests.length, 0);
  auth.resetLogin();
  values.set('nyxis.auth.pending', JSON.stringify({ verifier: 'a'.repeat(42), at: Date.now(), next: '/' }));
  location.href = 'http://127.0.0.1:3000/auth/callback?code=one-use';
  await assert.rejects(auth.finishLogin(), error => error.kind === 'oauth'); assert.equal(requests.length, 0);
});
test('a non-string destination in pending state falls back to home', async () => {
  values.set('nyxis.auth.pending', JSON.stringify({ verifier: 'a'.repeat(43), at: Date.now(), next: { evil: true } }));
  assert.equal((await auth.finishLogin()).next, '/');
});
test('logout discards the exchange so a later callback visit exchanges afresh', async () => {
  await auth.beginLogin('/');
  const first = await auth.finishLogin();
  auth.resetLogin();
  await assert.rejects(auth.finishLogin());
  assert.equal(first.session.userId, 'verified-user');
});
test('corrupt or incomplete stored sessions are ignored', () => {
  for (const raw of ['{not json', 'null', '"x"', JSON.stringify({ authBase: 'http://127.0.0.1:55321/auth/v1', accessToken: 'a' }), JSON.stringify({ authBase: 'http://127.0.0.1:55321/auth/v1', accessToken: 'a', refreshToken: 'r', userId: 'u', expiresAt: 'soon' })]) {
    values.set('nyxis.auth.session', raw);
    assert.equal(auth.storedSession(), null);
  }
  values.set('nyxis.auth.session', JSON.stringify({ authBase: 'http://127.0.0.1:55321/auth/v1', accessToken: 'a', refreshToken: 'r', userId: 'u', expiresAt: 1, extra: 'dropped' }));
  assert.deepEqual(auth.storedSession(), { accessToken: 'a', refreshToken: 'r', userId: 'u', expiresAt: 1 });
});
