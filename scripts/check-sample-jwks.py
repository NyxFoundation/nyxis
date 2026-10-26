#!/usr/bin/env python3
"""Actual sample -> fixed HTTPS JWKS endpoint; no live project or database.
Verifies launcher wiring and refresh/failure behavior, not the full JWT/DB integration.
"""
import http.client
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
PORT = int(os.environ.get('NYXIS_SAMPLE_JWKS_PORT', '18117'))
checks = 0
state = {'status': 200, 'requests': []}
handler = nyxis_local.relay_handler(lambda: b'{"keys":[]}', status=lambda: state['status'],
                                     trace=state['requests'].append)
with nyxis_local.tls_material('nyxis-sample-jwks-') as (cert, key), \
        nyxis_local.tls_server(handler, cert, key) as server:
    issuer = f'https://localhost:{server.server_port}/auth/v1'
    env = os.environ.copy()
    for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
        env.pop(name, None)
    env.update(NYXIS_DATABASE_URL='host=127.0.0.1 port=1 connect_timeout=1 password=sample-jwks-secret',
               NYXIS_SUPABASE_ISSUER=issuer, CURL_CA_BUNDLE=str(cert))
    nyxis_local.require_free_port(PORT)
    proc = None
    try:
        proc = subprocess.Popen([str(ROOT / 'examples/bulletin-board/backend/.lake/build/bin/sample'), str(PORT)], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        def request(path, status, text, *, headers=None, body=b'', fetches=0):
            global checks
            before = len(state['requests'])
            conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
            try:
                conn.request('GET', path, body, headers or {})
                res = conn.getresponse()
                assert (res.status, res.read().decode()) == (status, text)
                assert len(state['requests']) - before == fetches, 'JWKS refresh wiring'
                checks += 1
            finally:
                conn.close()
        nyxis_local.wait_ready(proc, lambda: request('/health', 200, 'ok') or True, 'sample')
        request('/posts/pub1', 503, 'backend unavailable')
        request('/posts/draft1', 503, 'backend unavailable',
                headers={'Authorization': 'Basic ignored'})
        headers = {'Authorization': 'Bearer opaque-test-token', 'Cookie': 'secret-cookie',
                   'X-Principal': 'root', 'X-Jwks-Url': 'https://invalid.example/keys'}
        request('/posts/draft1?issuer=https://invalid.example&principal=root',
                503, 'backend unavailable', headers=headers, fetches=1)
        request('/posts/draft1', 503, 'backend unavailable', headers=headers, fetches=1)
        state['status'] = 503
        request('/posts/draft1', 503, 'backend unavailable', headers=headers, fetches=1)
        state['status'] = 200
        request('/posts/draft1', 503, 'backend unavailable', headers=headers, fetches=1)
        request('/health', 200, 'ok', headers=headers)
        request('/posts/draft1', 400, 'request body unreadable', headers=headers, body=b'\xff')
        assert state['requests'] == [('/auth/v1/.well-known/jwks.json', None, None)] * 4
    finally:
        if proc is not None:
            out, err = nyxis_local.stop_output(proc)
            assert b'sample-jwks-secret' not in out + err and err == b'', 'diagnostic leak'
print(f'check-sample-jwks: {checks} checks passed (actual launcher, TLS refresh, libpq refusal; no Supabase)')
