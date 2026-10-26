#!/usr/bin/env python3
"""HTTP connection boundary only: injected backend and actual libpq refusal, no Supabase."""
import http.client
import os
from pathlib import Path
import socket
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
PORT = int(os.environ.get('NYXIS_POSTGRES_HTTP_PORT', '18112'))
checks = 0


def request(method, path, body=b'', headers=None):
    conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
    try:
        if isinstance(headers, list):
            conn.putrequest(method, path)
            conn.putheader('Content-Length', str(len(body)))
            for key, value in headers:
                conn.putheader(key, value)
            conn.endheaders(body)
        else:
            conn.request(method, path, body, headers or {})
        res = conn.getresponse()
        return res.status, res.read().decode('utf-8'), res.getheader('Content-Type')
    finally:
        conn.close()


def expect(method, path, status, body=None, data=b'', headers=None):
    global checks
    got, text, content_type = request(method, path, data, headers)
    assert got == status, (method, path, got, status, text)
    if body is not None:
        assert text == body, (method, path, text, body)
    assert content_type == 'text/plain; charset=utf-8', content_type
    checks += 1
    return text


def start(mode):
    nyxis_local.require_free_port(PORT)
    proc = subprocess.Popen([str(ROOT / 'examples/bulletin-board/backend/.lake/build/bin/servePostgresHttp'), str(PORT), mode],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        nyxis_local.wait_ready(proc, lambda: request('GET', '/health')[0] == 200)
        return proc
    except BaseException:
        stop(proc)
        raise


stop = nyxis_local.stop


proc = start('injected')
try:
    expect('GET', '/health?ignored=1', 200, 'ok')
    expect('GET', '/calls', 200, '0')  # health never called backend
    expect('POST', '/probe?subject=root', 201, 'POST|/probe|hello|anonymous', b'hello',
           {'Authorization': 'Bearer forged-root', 'X-Principal': 'root'})
    public = expect('GET', '/posts/pub1', 200)
    assert '"title":"public"' in public
    expect('GET', '/posts/draft1', 403)
    expect('PATCH', '/posts/draft1', 403, data=b'{"title":"stolen"}')
    expect('POST', '/posts/new1', 403, data=b'{"title":"t","body":"b"}')
    expect('DELETE', '/posts/pub1', 403)
    expect('PUT', '/users/bob/admin', 403, data=b'{"admin":true}')
    expect('GET', '/failure', 503, 'backend unavailable')
    # Health keeps working after failure, and the server continues accepting requests.
    expect('GET', '/health', 200, 'ok')
    before = int(expect('GET', '/calls', 200))
    expect('POST', '/probe', 400, 'request body unreadable', b'\xff')
    expect('POST', '/probe', 400, 'request body unreadable', b'x' * (1024 * 1024 + 1))
    expect('GET', '/calls', 200, str(before + 1))  # unreadable bodies never called backend
    expect('POST', '/health', 503, 'backend unavailable')  # only GET bypasses backend
    expect('POST', '/probe', 201, 'POST|/probe||anonymous')
finally:
    stop(proc)

# Opaque test credentials exercise HTTP->verifier->model wiring only. These are
# neither JWTs nor evidence of the cryptographic/local-Supabase integration.
proc = start('auth')
try:
    expect('GET', '/health', 200, 'ok', headers={'Authorization': 'Bearer verifier-error'})
    expect('GET', '/authcalls', 200, '0')  # health did not authenticate
    for token, draft_status in [('test-alice', 200), ('test-bob', 403), ('test-root', 200)]:
        auth = {'Authorization': 'bEaReR ' + token}
        expect('GET', '/posts/pub1', 200, headers=auth)
        expect('GET', '/posts/draft1', draft_status, headers=auth)
        expect('PATCH', '/posts/draft1', 204 if draft_status == 200 else 403,
               data=b'{"title":"changed"}', headers=auth)
    invalid = [None, 'Bearer forged-root', 'Bearer empty-subject', 'Bearer verifier-error',
               'Basic test-root', 'Bearer test-root extra', 'Bearer test-root,test-alice']
    for credential in invalid:
        auth = {'X-Principal': 'root'}
        if credential is not None:
            auth['Authorization'] = credential
        expect('GET', '/posts/draft1?subject=root', 403, headers=auth)
        expect('PATCH', '/posts/draft1', 403, data=b'{"title":"stolen","principal":"root"}',
               headers=auth)
    before = int(expect('GET', '/authcalls', 200))
    for values in [('test-root', 'test-alice'), ('test-root', 'test-root')]:
        duplicate = [('Authorization', 'Bearer ' + values[0]),
                     ('authorization', 'Bearer ' + values[1])]
        expect('GET', '/posts/draft1', 403, headers=duplicate)
        expect('PATCH', '/posts/draft1', 403, data=b'{"title":"stolen"}', headers=duplicate)
    expect('POST', '/posts/new', 400, 'request body unreadable', b'\xff',
           {'Authorization': 'Bearer test-root'})
    expect('GET', '/authcalls', 200, str(before))  # ambiguity/body error bypass verifier
    expect('GET', '/posts/draft1', 200, headers={'Authorization': 'Bearer test-root'})
    expect('GET', '/posts/draft1', 403)  # authenticated subject does not persist
finally:
    stop(proc)

proc = start('connection')
try:
    expect('GET', '/health', 200, 'ok')
    expect('GET', '/posts/pub1', 503, 'backend unavailable')
    expect('GET', '/posts/draft1', 503, 'backend unavailable')
    expect('POST', '/posts/new1', 503, 'backend unavailable', b'{"title":"t","body":"b"}')
    expect('GET', '/health', 200, 'ok')
finally:
    stop(proc)
print(f'check-postgres-http: {checks} HTTP checks passed (injected backend/verifier + libpq refusal; no JWT/Supabase)')
