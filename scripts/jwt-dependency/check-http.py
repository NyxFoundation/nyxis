#!/usr/bin/env python3
"""Real JWT -> HTTP -> fixture model and actual libpq refusal; no Supabase."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
import nyxis_local
import http.client
from pathlib import Path
import socket
import subprocess
import sys
import time

work = Path(sys.argv[1])
checks = 0
# Let the OS choose a free port. Startup still fails if another process takes it.
with socket.socket() as probe:
    probe.bind(('127.0.0.1', 0))
    port = probe.getsockname()[1]


def request(method, path, token=None, body=b''):
    conn = http.client.HTTPConnection('127.0.0.1', port, timeout=10)
    try:
        headers = {'X-Principal': 'root'}
        if token is not None:
            headers['Authorization'] = 'Bearer ' + token
        conn.request(method, path, body, headers)
        res = conn.getresponse()
        return res.status, res.read().decode()
    finally:
        conn.close()


def expect(method, path, status, token=None, body=b'', text=None):
    global checks
    actual, content = request(method, path, token, body)
    assert actual == status, (method, path, actual, status)
    if text is not None:
        assert content == text, (method, path, 'unexpected response')
    checks += 1


# Run this first, while the short-lived token is still valid. The same running
# server must stop authenticating it after expiry without restarting or reloading.
proc = subprocess.Popen([str(work / 'check/.lake/build/bin/serveJwtHttp'),
                         str(work), str(port), 'clock'],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
try:
    nyxis_local.wait_ready(proc, lambda: request('GET', '/health') == (200, 'ok'), 'Wall-clock JWT server')
    valid = (work / 'clock-valid.jwt').read_text()
    expect('GET', '/principal', 200, valid, text='alice')
    expect('GET', '/posts/draft1', 200, valid)
    expect('PATCH', '/posts/draft1', 204, valid, b'{"title":"changed"}')
    for name in ['clock-expired', 'alice']:
        token = (work / (name + '.jwt')).read_text()
        expect('GET', '/principal', 200, token, text='anonymous')
        expect('GET', '/posts/draft1', 403, token)
        expect('PATCH', '/posts/draft1', 403, token, b'{"title":"stolen"}')
    transition = (work / 'clock-transition.jwt').read_text()
    expect('GET', '/principal', 200, transition, text='alice')
    deadline = time.monotonic() + 15
    while request('GET', '/principal', transition) != (200, 'anonymous'):
        assert time.monotonic() < deadline, 'Server cached time or ignored expiry'
        time.sleep(0.1)
    expect('GET', '/posts/draft1', 403, transition)
    expect('PATCH', '/posts/draft1', 403, transition, b'{"title":"stolen"}')
finally:
    nyxis_local.stop(proc)
print(f'JWT wall-clock boundary: {checks} checks passed (OpenSSL/JWKS + fixture model; no Supabase)')
checks = 0

proc = subprocess.Popen([str(work / 'check/.lake/build/bin/serveJwtHttp'), str(work), str(port)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
try:
    nyxis_local.wait_ready(proc, lambda: request('GET', '/health') == (200, 'ok'), 'JWT test server')
    for subject, status in [('alice', 200), ('bob', 403), ('root', 200)]:
        token = (work / (subject + '.jwt')).read_text()
        expect('GET', '/principal', 200, token, text=subject)
        expect('GET', '/posts/draft1', status, token)
        expect('PATCH', '/posts/draft1', 204 if status == 200 else 403, token,
               b'{"title":"changed"}')
    for name in ['bad-signature', 'expired', 'expiry-boundary', 'wrong-issuer',
                 'wrong-audience', 'none', 'missing-subject', 'empty-subject']:
        token = (work / (name + '.jwt')).read_text()
        expect('GET', '/principal', 200, token, text='anonymous')
        expect('GET', '/posts/draft1?subject=root', 403, token)
        expect('PATCH', '/posts/draft1', 403, token, b'{"title":"stolen"}')
        expect('GET', '/posts/pub1', 200, token)
    expect('GET', '/principal', 200, text='anonymous')
    expect('GET', '/posts/draft1', 403)
    expect('PATCH', '/posts/draft1', 403, body=b'{"title":"stolen"}')
    # Change the trusted public document while the same server keeps running.
    # A valid signature under a removed key must no longer authenticate.
    jwks_path = work / 'test-jwks.json'
    original = jwks_path.read_text()
    alice = (work / 'alice.jwt').read_text()
    try:
        for document in ['{"keys":[]}', 'not json', original.replace('"test"', '"rotated"'), None]:
            if document is None:
                jwks_path.unlink()
            else:
                jwks_path.write_text(document)
            expect('GET', '/principal', 200, alice, text='anonymous')
            expect('GET', '/posts/draft1', 403, alice)
            expect('PATCH', '/posts/draft1', 403, alice, b'{"title":"stolen"}')
            expect('GET', '/posts/pub1', 200, alice)
        jwks_path.write_text(original)
        expect('GET', '/principal', 200, alice, text='alice')
        expect('GET', '/posts/draft1', 200, alice)
        expect('PATCH', '/posts/draft1', 204, alice, b'{"title":"restored"}')
    finally:
        jwks_path.write_text(original)
finally:
    nyxis_local.stop(proc)
print(f'JWT HTTP boundary: {checks} checks passed (OpenSSL/JWKS + fixture model; no Supabase)')

# The core authenticated PostgreSQL entry must use libpq, including after an
# invalid JWT becomes anonymous. A failed DB connection must never return fixture
# data, a model response, a subject probe, or connection/verification diagnostics.
checks = 0
with socket.socket() as probe:
    probe.bind(('127.0.0.1', 0))
    port = probe.getsockname()[1]
proc = subprocess.Popen([str(work / 'check/.lake/build/bin/serveJwtHttp'),
                         str(work), str(port), 'connection'],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
try:
    nyxis_local.wait_ready(proc, lambda: request('GET', '/health') == (200, 'ok'), 'JWT PostgreSQL test server')
    expect('GET', '/health', 200, (work / 'alice.jwt').read_text(), text='ok')
    tokens = [None] + [(work / (name + '.jwt')).read_text() for name in
                      ['alice', 'bob', 'root', 'bad-signature', 'expired',
                       'expiry-boundary', 'wrong-issuer', 'wrong-audience',
                       'none', 'missing-subject', 'empty-subject']]
    for token in tokens:
        expect('GET', '/posts/draft1?subject=root', 503, token, text='backend unavailable')
        expect('PATCH', '/posts/draft1', 503, token, b'{"title":"changed"}',
               text='backend unavailable')
    alice = (work / 'alice.jwt').read_text()
    expect('POST', '/posts/new', 400, alice, b'\xff', text='request body unreadable')
    expect('POST', '/posts/new', 400, alice, b'x' * (1024 * 1024 + 1),
           text='request body unreadable')
    expect('GET', '/principal', 503, alice, text='backend unavailable')
    expect('POST', '/health', 503, alice, text='backend unavailable')
    expect('GET', '/health', 200, text='ok')
finally:
    nyxis_local.stop(proc)
print(f'JWT PostgreSQL boundary: {checks} checks passed (OpenSSL/JWKS + libpq refusal; no Supabase)')
