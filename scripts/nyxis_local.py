"""Shared pieces of the local verification harnesses (not a check by itself).

Every check script imports this first: it refuses to run with assertions disabled, makes
SIGTERM/SIGHUP unwind `finally` blocks (the IDD hook timeout must still stop children and
drop test databases), and provides the child-process helpers that the checks used to copy.
Nothing here prints credentials or child diagnostics.
"""
import os
import signal
import socket
import subprocess
import time

if not __debug__:
    raise SystemExit('assertions disabled')


def interrupted(signum, frame):
    raise KeyboardInterrupt(f'signal {signum}')


for _signal in (signal.SIGTERM, signal.SIGHUP):
    signal.signal(_signal, interrupted)


def scrub_docker_env(env):
    """Use only the local Docker Desktop context, never a caller's remote daemon."""
    for name in ('DOCKER_HOST', 'DOCKER_TLS_VERIFY', 'DOCKER_CERT_PATH'):
        env.pop(name, None)
    env['DOCKER_CONTEXT'] = 'desktop-linux'
    return env


def require_free_port(port):
    with socket.socket() as probe:
        assert probe.connect_ex(('127.0.0.1', port)) != 0, 'test port already in use'


def wait_ready(proc, ready, what='server', attempts=100, interval=0.05):
    """Poll `ready()` (which may raise OSError while the port is closed) until it is true."""
    for _ in range(attempts):
        assert proc.poll() is None, f'{what} exited before ready'
        try:
            if ready():
                return
        except OSError:
            pass
        time.sleep(interval)
    raise AssertionError(f'{what} startup timeout')


def stop(proc, timeout=5):
    """Terminate, then kill; always reap."""
    proc.terminate()
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()


def stop_output(proc, timeout=5):
    """Like `stop`, returning captured (stdout, stderr) for leak checks."""
    proc.terminate()
    try:
        return proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        return proc.communicate()


def popen_group(args, **keywords):
    """Start a process in its own session so that `stop_group` reaches its descendants (npm → next)."""
    return subprocess.Popen(args, start_new_session=True, **keywords)


def stop_group(proc, port=None, timeout=20):
    """Terminate the whole process group and, when given, wait until `port` is closed again."""
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
    if port is not None:
        for _ in range(40):
            with socket.socket() as probe:
                if probe.connect_ex(('127.0.0.1', port)) != 0:
                    return
            time.sleep(0.25)
        raise AssertionError('child port remains open')


# ---------------------------------------------------------------------------
# Local Supabase Auth and the test-only HTTPS relay of its public JWKS.

import http.server
import json
import ssl
import tempfile
import threading
import uuid
from contextlib import contextmanager
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import ProxyHandler, Request, build_opener

LOCAL_AUTH = 'http://127.0.0.1:55321'
JWKS_PATH = '/auth/v1/.well-known/jwks.json'
JWKS_LIMIT = 65536
_opener = build_opener(ProxyHandler({}))


@contextmanager
def tls_material(prefix='nyxis-tls-'):
    """A throwaway self-signed certificate for `localhost`, in a temporary directory."""
    with tempfile.TemporaryDirectory(prefix=prefix) as tmp:
        cert, key = Path(tmp) / 'cert.pem', Path(tmp) / 'key.pem'
        subprocess.run(['openssl', 'req', '-x509', '-newkey', 'rsa:2048', '-nodes',
                        '-keyout', str(key), '-out', str(cert), '-days', '1',
                        '-subj', '/CN=localhost', '-addext', 'subjectAltName=DNS:localhost'],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        yield cert, key


@contextmanager
def tls_server(handler, cert, key, port=0):
    """Serve `handler` over TLS on 127.0.0.1 in a daemon thread; stop and close on exit."""
    server = http.server.ThreadingHTTPServer(('127.0.0.1', port), handler)
    try:
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(cert, key)
        server.socket = context.wrap_socket(server.socket, server_side=True)
        worker = threading.Thread(target=server.serve_forever, daemon=True)
        worker.start()
        try:
            yield server
        finally:
            server.shutdown()
            worker.join(timeout=5)
    finally:
        server.server_close()


def local_jwks():
    """The public JWKS of the fixed local Auth, with the same size limit the sample enforces."""
    with _opener.open(LOCAL_AUTH + JWKS_PATH, timeout=5) as response:
        raw = response.read(JWKS_LIMIT + 1)
        assert response.status == 200 and 0 < len(raw) <= JWKS_LIMIT
        return raw


STORAGE_SIGN_PREFIXES = ('/storage/v1/object/upload/sign/', '/storage/v1/object/sign/')


def relay_handler(document, status=lambda: 200, trace=None, storage=None):
    """A request handler that serves `document()` at the JWKS path only.

    `trace`, when given, receives (path, Authorization, Cookie) per request so a check can
    assert that the sample forwards neither credentials nor request-chosen URLs.

    `storage`, when given, is a callback `storage(path, authorization, body) -> (status, bytes)`
    for POST requests to the Storage signing endpoints (the sample reaches local Storage only through
    this HTTPS relay, like the JWKS). Every other POST is 404.
    """
    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def do_GET(self):
            if trace is not None:
                trace((self.path, self.headers.get('Authorization'), self.headers.get('Cookie')))
            if self.path != JWKS_PATH:
                self.send_error(404)
                return
            try:
                raw = document()
            except Exception:
                self.send_error(502, 'Local Auth unavailable')
                return
            self.send_response(status())
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

        def do_POST(self):
            length = int(self.headers.get('Content-Length') or 0)
            body = self.rfile.read(length) if length else b''
            if storage is None or not self.path.startswith(STORAGE_SIGN_PREFIXES):
                if trace is not None:
                    trace((self.path, self.headers.get('Authorization'), self.headers.get('Cookie')))
                self.send_error(404)
                return
            try:
                code, raw = storage(self.path, self.headers.get('Authorization'), body)
            except Exception:
                self.send_error(502, 'Local Storage unavailable')
                return
            self.send_response(code)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
    return Handler


def storage_request(method, path, body=None, *, key, headers=None, base=LOCAL_AUTH):
    """One call to the local Storage API (`/storage/v1/...`). Returns (status, bytes); never raises on 4xx/5xx."""
    request = Request(base + path, data=body, method=method,
                      headers={'Authorization': 'Bearer ' + key, 'apikey': key, **(headers or {})})
    try:
        with _opener.open(request, timeout=10) as response:
            return response.status, response.read()
    except HTTPError as error:
        return error.code, error.read()


def read_dotenv(path, keys):
    """The named variables of a `.env` file: `export` prefix and quotes allowed, comments only on their own line, no expansion."""
    values = {}
    if not Path(path).exists():
        return values
    import shlex
    for line in Path(path).read_text().splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            continue
        key, sep, raw = stripped.removeprefix('export ').partition('=')
        key = key.strip()
        if not sep or key not in keys:
            continue
        parsed = shlex.split(raw)
        if len(parsed) != 1:
            raise ValueError('dotenv format')
        values[key] = parsed[0]
    return values


def auth_request(method, path, body=None, *, key, bearer=None, base=LOCAL_AUTH):
    """One call to the local Auth REST API; returns the decoded JSON (or None)."""
    request = Request(base + '/auth/v1' + path,
                      data=None if body is None else json.dumps(body).encode(),
                      headers={'apikey': key, 'Authorization': 'Bearer ' + (bearer or key),
                               'Content-Type': 'application/json'}, method=method)
    with _opener.open(request, timeout=10) as response:
        raw = response.read()
        return json.loads(raw) if raw else None


@contextmanager
def auth_sessions(names, prefix='nyxis-auth-test-'):
    """Fresh local Auth users with magic-link sessions, removed on exit.

    Yields {name: {'id', 'email', 'access_token', 'refresh_token', 'expires_in'}}. Requires the
    fixed local Auth and its keys in the environment; never contacts a remote project. Tokens stay
    in memory. Cleanup verifies each user is gone (404) and raises if any remains.
    """
    assert os.environ.get('NYXIS_SUPABASE_URL') == LOCAL_AUTH, 'nyxis local Auth required'
    anon = os.environ.get('NYXIS_SUPABASE_ANON_KEY')
    service = os.environ.get('NYXIS_SUPABASE_SERVICE_ROLE_KEY')
    assert anon and service, 'local Auth keys required'
    created = []
    sessions = {}
    try:
        for name in names:
            email = prefix + uuid.uuid4().hex + '@example.com'
            user = auth_request('POST', '/admin/users', {'email': email, 'email_confirm': True}, key=service)
            uid = str(uuid.UUID(user['id']))
            created.append(uid)
            assert user['email'] == email, 'unexpected Auth user'
            link = auth_request('POST', '/admin/generate_link', {'type': 'magiclink', 'email': email}, key=service)
            assert link['id'] == uid, 'magic link user differs'
            session = auth_request('POST', '/verify', {'type': 'email', 'token_hash': link['hashed_token']}, key=anon)
            assert session['user']['id'] == uid and session['token_type'] == 'bearer', 'unexpected Auth session'
            assert auth_request('GET', '/user', key=anon, bearer=session['access_token'])['id'] == uid, \
                'Auth-issued JWT identity differs'
            sessions[name] = {'id': uid, 'email': email, 'access_token': session['access_token'],
                              'refresh_token': session['refresh_token'], 'expires_in': session['expires_in']}
        yield sessions
    finally:
        failed = False
        for uid in created:
            try:
                auth_request('DELETE', '/admin/users/' + uid, key=service)
                try:
                    auth_request('GET', '/admin/users/' + uid, key=service)
                    failed = True
                except HTTPError as error:
                    if error.code != 404:
                        failed = True
            except Exception:
                failed = True
        if failed:
            raise RuntimeError('local test user cleanup failed (diagnostics withheld)')
