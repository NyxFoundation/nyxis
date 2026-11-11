#!/usr/bin/env python3
"""CORS: actual sample, isolated local Supabase DB, fixed preflight/no DB sessions.
Run after lake build with the local credential wrapper. No cloud operations.
"""
import http.client
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('db', ROOT / 'scripts/check-local-postgres-http.py')
db = importlib.util.module_from_spec(spec)
spec.loader.exec_module(db)
ALLOWED = 'http://127.0.0.1:3000'
SECOND = 'https://example.test'
db.ENV['NYXIS_CORS_ORIGINS'] = ALLOWED + ', ' + SECOND
checks = 0


def request(method, path, origin=None, body=b'', extra=()):
    global checks
    conn = http.client.HTTPConnection('127.0.0.1', db.PORT, timeout=5)
    try:
        conn.putrequest(method, path)
        conn.putheader('Content-Length', str(len(body)))
        if origin is not None:
            conn.putheader('Origin', origin)
        for name, value in extra:
            conn.putheader(name, value)
        conn.endheaders(body)
        res = conn.getresponse()
        status, data, headers = res.status, res.read(), res.getheaders()
        allowed = origin in (ALLOWED, SECOND) and not any(n.lower() == 'origin' for n, _ in extra)
        cors = {n.lower(): v for n, v in headers if n.lower().startswith('access-control-')}
        expected = {'access-control-allow-origin': origin} if allowed else {}
        if method == 'OPTIONS' and allowed:
            expected.update({'access-control-allow-methods': 'GET, POST, PUT, PATCH, DELETE, OPTIONS',
                             'access-control-allow-headers':
                                 'Authorization, Content-Type, Accept, Accept-Language, If-Match, If-None-Match'})
        elif allowed:
            expected['access-control-expose-headers'] = 'ETag, Location'
        assert cors == expected, (method, path, origin, cors)
        assert any(n.lower() == 'vary' and 'Origin' in v for n, v in headers)
        if method == 'OPTIONS':
            assert (status, data) == (204, b''), (status, data)
        checks += 1
        return status, data
    finally:
        conn.close()


def stats():
    # Observe from postgres, not the isolated database, so observation adds no
    # connections or statements to the target's counters. Closed sessions flush.
    return tuple(map(int, db.sql("SELECT sessions, xact_commit, xact_rollback, "
                                "tup_returned, tup_inserted, tup_updated, tup_deleted "
                                "FROM pg_stat_database WHERE datname = '" + db.DATABASE + "';").split('|')))


def verify():
    time.sleep(1.2)
    before = stats()
    origins = [ALLOWED, SECOND, 'http://localhost:3000', 'http://127.0.0.1:3000.evil',
               'http://127.0.0.1:3001', 'null', '*', None,
               ALLOWED + ', ' + SECOND, ALLOWED + '/']
    for origin in origins:
        for path in ['/posts', '/posts/pub1', '/posts/draft1', '/users/root/admin', '/unknown', '/health']:
            request('OPTIONS', path, origin, b'\xff',
                    [('Authorization', 'Bearer forged'),
                     ('Access-Control-Request-Method', 'PATCH'),
                     ('Access-Control-Request-Headers', 'Authorization, Content-Type, If-Match')])
    request('OPTIONS', '/posts', ALLOWED, extra=[('Origin', SECOND)])
    # Unsupported requested methods/headers get exactly the same fixed grant;
    # browsers reject what is absent from that fixed allow list.
    request('OPTIONS', '/posts', ALLOWED,
            extra=[('Access-Control-Request-Method', 'TRACE'),
                   ('Access-Control-Request-Headers', 'X-Principal')])
    time.sleep(1.2)
    assert stats() == before, 'OPTIONS issued a DB connection/transaction/operation'
    for origin in origins:
        assert request('GET', '/posts/pub1', origin)[0] == 200
        assert request('GET', '/posts/draft1', origin)[0] == 403
        assert request('GET', '/health', origin) == (200, b'ok')
    assert request('GET', '/posts/pub1', ALLOWED, extra=[('Origin', SECOND)])[0] == 200
    assert request('POST', '/posts/new', ALLOWED, b'\xff')[0] == 400
    time.sleep(1.2)
    assert stats()[0] > before[0], 'DB-session positive control failed'
    print(f'check-cors: {checks} HTTP checks; OPTIONS added zero DB sessions/transactions/rows; '
          'GET positive control, public 200/private 403, duplicate/no/opaque origins, fixed grants passed', flush=True)


def main():
    # Invalid configuration must fail closed without echoing values.
    env = {**os.environ, 'NYXIS_DATABASE_URL': 'host=127.0.0.1 port=1 connect_timeout=1',
           'NYXIS_SUPABASE_ISSUER': 'https://localhost:1/auth/v1'}
    for value in ['*', 'null', 'https://example.test/', 'http://a@b',
                  'http://localhost:3000,', 'https://example.test?x=1', 'http://a\nsecret-marker']:
        run = subprocess.run([str(ROOT / 'examples/bulletin-board/backend/.lake/build/bin/sample')],
                             env={**env, 'NYXIS_CORS_ORIGINS': value}, capture_output=True, timeout=5)
        assert run.returncode != 0
        assert b'NYXIS_CORS_ORIGINS is invalid' in run.stderr
        assert b'secret-marker' not in run.stdout + run.stderr
    db.main(verify=verify)
    # Empty/unset configuration grants nothing, including to previously allowed origins.
    db.ENV.pop('NYXIS_CORS_ORIGINS')
    def disabled():
        conn = http.client.HTTPConnection('127.0.0.1', db.PORT, timeout=5)
        try:
            conn.request('OPTIONS', '/posts', headers={'Origin': ALLOWED})
            res = conn.getresponse()
            assert (res.status, res.read()) == (204, b'')
            assert not any(n.lower().startswith('access-control-') for n, _ in res.getheaders())
        finally:
            conn.close()
    db.main(verify=disabled)
    print('check-cors: invalid startup 7 cases and default-deny passed; isolated DBs removed')


if __name__ == '__main__':
    main()
