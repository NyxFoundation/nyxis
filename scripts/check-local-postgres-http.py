#!/usr/bin/env python3
"""Real local-Supabase DB/HTTP checks for the anonymous sample path only.

Run after lake build via python3 scripts/local-supabase.py --exec python3 <this script>.
Only a newly created, uniquely named local test database is seeded and removed.
Existing application/Auth databases are never changed. Credentials are never printed.
"""
import http.client
import json
import os
from pathlib import Path
import subprocess
import sys
from urllib.parse import urlsplit, urlunsplit
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
from nyxis_local import stop  # re-exported: other checks call db.stop

PORT = int(os.environ.get('NYXIS_LOCAL_HTTP_PORT', '18116'))
DATABASE = 'nyxis_http_test_' + uuid.uuid4().hex
ENV = nyxis_local.scrub_docker_env(os.environ.copy())
checks = 0


def sql(statement, database='postgres'):
    result = subprocess.run(
        ['docker', '--context', 'desktop-linux', 'exec', '-i', 'supabase_db_nyxis',
         'psql', '-X', '-U', 'postgres', '-d', database, '-At', '-v', 'ON_ERROR_STOP=1'],
        input=statement.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=ENV, timeout=30)
    if result.returncode:
        raise RuntimeError('local test SQL failed (diagnostics withheld)')
    return result.stdout.decode().strip()


def run_binary(name, env):
    result = subprocess.run([str(ROOT / 'examples/bulletin-board/backend/.lake/build/bin' / name)], env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    if result.returncode:
        raise RuntimeError('sample provisioning failed (diagnostics withheld)')


def request(method, path, data=None, headers=None):
    conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
    try:
        conn.request(method, path, None if data is None else json.dumps(data), headers or {})
        res = conn.getresponse()
        return res.status, res.read().decode()
    finally:
        conn.close()


def expect(method, path, status, data=None, headers=None):
    global checks
    got, body = request(method, path, data, headers)
    assert got == status, (method, path, got, status)
    checks += 1
    return body


def snapshot():
    return sql('''SELECT jsonb_build_object(
        'users', (SELECT jsonb_agg(to_jsonb(u) ORDER BY "_nyxis_id") FROM public."User" u),
        'posts', (SELECT jsonb_agg(to_jsonb(p) ORDER BY "_nyxis_id") FROM public."Post" p));''', DATABASE)


def main(server_command=None, verify=None, *, issuer='https://localhost:1/auth/v1'):
    global checks
    # Endpoint check happens before any SQL or child startup.
    endpoint = urlsplit(os.environ.get('NYXIS_DATABASE_URL', ''))
    assert endpoint.scheme in ('postgres', 'postgresql'), 'local DB URL required'
    assert endpoint.hostname in ('127.0.0.1', 'localhost', '::1'), 'local DB required'
    assert endpoint.port == 55322 and endpoint.path == '/postgres', 'nyxis local DB required'
    assert not endpoint.query and not endpoint.fragment, 'unexpected DB URL options'
    context = subprocess.run(['docker', 'context', 'inspect', 'desktop-linux'], env=ENV,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    assert context.returncode == 0, 'Docker context unavailable'
    assert json.loads(context.stdout)[0]['Endpoints']['docker']['Host'].startswith('unix:///'), 'local Docker required'
    nyxis_local.require_free_port(PORT)
    env = ENV.copy()
    env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + DATABASE))
    # Anonymous checks never need keys; do not inherit an actual project's issuer.
    env['NYXIS_SUPABASE_ISSUER'] = issuer
    created = False
    proc = None
    try:
        sql('CREATE DATABASE "' + DATABASE + '";')
        created = True
        run_binary('initSampleDatabase', env)
        sql('''INSERT INTO public."User" VALUES
            ('alice', '["bool",false]'), ('bob', '["bool",false]'), ('root', '["bool",true]');
        INSERT INTO public."Post" ("_nyxis_id", author, title, body, published) VALUES
            ('pub1', '["entity",[],"User","alice"]', '["string","public"]',
             '["string","public body"]', '["bool",true]'),
            ('draft1', '["entity",[],"User","alice"]', '["string","draft"]',
             '["string","private body"]', '["bool",false]');''', DATABASE)
        initial = snapshot()
        proc = subprocess.Popen(server_command or [str(ROOT / 'examples/bulletin-board/backend/.lake/build/bin/sample'), str(PORT)],
                                env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        nyxis_local.wait_ready(proc, lambda: request('GET', '/health')[0] == 200, 'sample')
        if verify is not None:
            verify()
            return
        expect('GET', '/health', 200)
        public = json.loads(expect('GET', '/posts/pub1', 200))
        assert public == dict(author='alice', title='public', body='public body', published=True)
        for headers in ({}, {'Authorization': 'Bearer forged-root', 'X-Principal': 'root'}):
            expect('GET', '/posts/draft1?subject=root', 403, headers=headers)
            for post in ('pub1', 'draft1'):
                expect('PATCH', '/posts/' + post, 403, {'title': 'stolen'}, headers)
                expect('DELETE', '/posts/' + post, 403, headers=headers)
                for action in ('publish', 'unpublish'):
                    expect('POST', '/posts/' + post + '/' + action, 403, headers=headers)
            for published in (False, True):
                expect('POST', '/posts/new' + str(published), 403,
                       dict(title='new', body='new', published=published, author='root'), headers)
            expect('PUT', '/users/bob/admin', 403, {'admin': True}, headers)
            expect('PUT', '/users/root/admin', 403, {'admin': False}, headers)
            assert snapshot() == initial, 'denied requests changed persistent rows'
            checks += 1
        # A separate connection changes the current DB row. The next HTTP request must
        # observe it; there is no fixture-store or stale in-memory authorization fallback.
        sql('UPDATE public."Post" SET published = \'["bool",false]\' WHERE "_nyxis_id" = \'pub1\';', DATABASE)
        expect('GET', '/posts/pub1', 403)
        sql('UPDATE public."Post" SET published = \'["bool",true]\', title = \'["string","fresh"]\' WHERE "_nyxis_id" = \'pub1\';', DATABASE)
        assert json.loads(expect('GET', '/posts/pub1', 200))['title'] == 'fresh'
        expect('GET', '/health', 200)
    finally:
        if proc is not None:
            stop(proc)
        if created:
            # No FORCE or IF EXISTS: remove only the database this invocation created.
            sql('DROP DATABASE "' + DATABASE + '";')
    print(f'check-local-postgres-http: {checks} checks passed (real local DB, anonymous HTTP; authenticated paths are checked by check-sample-jwt-db.py)')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-local-postgres-http interrupted (cleanup attempted)')
    except Exception:
        # Exceptions from URL/SQL/process code can carry credentials; do not print them.
        raise SystemExit('check-local-postgres-http failed (diagnostics withheld)')
