#!/usr/bin/env python3
"""Actual sample executable: startup validation + libpq refusal, not Supabase integration."""
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
BINARY = ROOT / 'examples/bulletin-board/backend/.lake/build/bin/sample'
PORT = int(os.environ.get('NYXIS_SAMPLE_CHECK_PORT', '18113'))
checks = 0
# Never use inherited credentials or contact an actual project in this test.
ENV = {k: v for k, v in os.environ.items()
       if k not in ('NYXIS_DATABASE_URL', 'NYXIS_SUPABASE_ISSUER')}
ISSUER = 'https://localhost:1/auth/v1'
SENTINEL = 'startup-secret-must-not-appear'
REFUSED = f'host=127.0.0.1 port=1 connect_timeout=1 password={SENTINEL}'


def rejected(args, config=None, message='', issuer=ISSUER):
    global checks
    env = dict(ENV)
    if config is not None:
        env['NYXIS_DATABASE_URL'] = config
    if issuer is not None:
        env['NYXIS_SUPABASE_ISSUER'] = issuer
    run = subprocess.run([str(BINARY), *args], env=env, capture_output=True, timeout=10)
    output = (run.stdout + run.stderr).decode('utf-8')
    assert run.returncode != 0, 'invalid startup accepted'
    assert message in output, 'missing expected startup diagnostic'
    assert SENTINEL not in output, 'credentials leaked during startup'
    checks += 1


rejected([], message='NYXIS_DATABASE_URL is required')
rejected([], '', 'NYXIS_DATABASE_URL is invalid')
rejected([], ' \t ', 'NYXIS_DATABASE_URL is invalid')
for port in ['0', '65536', '-1', SENTINEL]:
    rejected([port], REFUSED, 'port')
rejected(['8080', SENTINEL], REFUSED, 'usage: sample [port]')
rejected([], REFUSED, 'NYXIS_SUPABASE_ISSUER is required', issuer=None)
for issuer in ['', ' \t ', 'http://localhost/auth/v1',
               'https://localhost/auth/v1/', 'https://localhost/auth/v1?secret=' + SENTINEL,
               'https://user:' + SENTINEL + '@localhost/auth/v1']:
    rejected([], REFUSED, 'NYXIS_SUPABASE_ISSUER is invalid', issuer=issuer)


def request(method, path, status, body, data=b'', headers=None):
    global checks
    conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
    try:
        conn.request(method, path, data, headers or {})
        res = conn.getresponse()
        text = res.read().decode('utf-8')
        assert (res.status, text) == (status, body), (method, path, res.status, text)
        assert SENTINEL not in text
        checks += 1
    finally:
        conn.close()


nyxis_local.require_free_port(PORT)
proc = subprocess.Popen([str(BINARY), str(PORT)],
                        env={**ENV, 'NYXIS_DATABASE_URL': REFUSED,
                             'NYXIS_SUPABASE_ISSUER': ISSUER},
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
try:
    nyxis_local.wait_ready(proc, lambda: request('GET', '/health', 200, 'ok') or True, 'sample')
    # A Store fallback would return 403/404 here; the actual sample must attempt PostgreSQL.
    request('GET', '/posts/pub1', 503, 'backend unavailable')
    request('GET', '/posts/draft1?principal=root', 503, 'backend unavailable',
            headers={'Authorization': 'Bearer forged', 'X-Principal': 'root'})
    request('POST', '/posts/new1', 503, 'backend unavailable', b'{"title":"t","body":"b"}')
    request('GET', '/nope', 503, 'backend unavailable')
    request('POST', '/health', 503, 'backend unavailable')
    request('POST', '/posts/new1', 400, 'request body unreadable', b'\xff')
    request('GET', '/health?ignored=1', 200, 'ok')
finally:
    out, err = nyxis_local.stop_output(proc)
    assert SENTINEL.encode() not in out + err, 'credentials leaked in sample logs'
print(f'check-sample-startup: {checks} checks passed (actual sample + libpq refusal; no Supabase)')
