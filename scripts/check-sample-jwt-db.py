#!/usr/bin/env python3
"""Actual sample -> HTTPS JWKS/ES256/real clock -> isolated local Supabase DB.

Default JWTs use the approved Lean/OpenSSL fixtures. --local-auth uses actual
Supabase Auth magic-link sessions and proxies its public JWKS over test TLS.
Only this run's new DB is modified and removed. No real project is contacted.
Run after lake build via python3 scripts/local-supabase.py --exec python3 <this script>.
"""
from contextlib import ExitStack
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import tomllib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
spec = importlib.util.spec_from_file_location(
    'matrix', ROOT / 'scripts/jwt-dependency/check-local-db.py')
matrix = importlib.util.module_from_spec(spec)
spec.loader.exec_module(matrix)


def main():
    assert sys.argv[1:] in ([], ['--local-auth']), 'expected optional --local-auth'
    real_auth = bool(sys.argv[1:])
    with ExitStack() as resources:
        tmp = resources.enter_context(tempfile.TemporaryDirectory(prefix='nyxis-sample-jwt-db-'))
        work = Path(tmp)
        cert, key = resources.enter_context(nyxis_local.tls_material('nyxis-sample-jwt-db-'))
        subprocess.run([sys.executable, str(ROOT / 'scripts/jwt-dependency/make-fixture.py'), tmp],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        state = {'document': (work / 'test-jwks.json').read_bytes(), 'status': 200,
                 'requests': []}

        subjects = None
        auth_tokens = None
        if real_auth:
            created = resources.enter_context(nyxis_local.auth_sessions(('alice', 'bob', 'root')))
            auth_tokens = {name: info['access_token'] for name, info in created.items()}
            subjects = {name: info['id'] for name, info in created.items()}
            state['document'] = None
        state['upstream'] = 0

        def document():
            if state['document'] is not None:
                return state['document']
            # Fixed local public endpoint; never forward request headers or tokens.
            raw = nyxis_local.local_jwks()
            state['upstream'] += 1
            return raw

        handler = nyxis_local.relay_handler(document, status=lambda: state['status'],
                                             trace=state['requests'].append)
        server = resources.enter_context(nyxis_local.tls_server(handler, cert, key,
                                                                 port=55325 if real_auth else 0))
        issuer = f'https://localhost:{server.server_port}/auth/v1'
        if real_auth:
            config = tomllib.loads((ROOT / 'supabase/config.toml').read_text())
            assert config['auth']['jwt_issuer'] == issuer, 'local Auth issuer differs'
        subprocess.run([str(ROOT / '.lake/build/bin/checkJwtDependency'), tmp, issuer],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        rejected = ('bad-signature', 'expired', 'wrong-issuer')
        tokens = {name: (work / ('issuer-' + name + '.jwt')).read_text()
                  for name in ('alice', 'bob', 'root') + rejected}
        if real_auth:
            tokens = auth_tokens
            rejected = ()
        # Trust this ephemeral CA only in the test child environment. No runtime
        # API/HTTP parameter or command replacement is introduced.
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            matrix.db.ENV.pop(name, None)
        matrix.db.ENV['CURL_CA_BUNDLE'] = str(cert)

        def verify_refresh():
            initial = matrix.db.snapshot()
            original = state['document']
            removed = json.loads(document())
            for jwk in removed['keys']:
                jwk['kid'] = 'removed-' + jwk['kid']
            headers = {'Authorization': 'Bearer ' + tokens['root'], 'Cookie': 'test-secret'}
            for status, payload in [(503, original), (200, b'{"keys":[]}'),
                                     (200, b'not-json'),
                                     (200, json.dumps(removed).encode())]:
                state.update(status=status, document=payload)
                before = len(state['requests'])
                matrix.db.expect('GET', '/posts/pub1', 200, headers=headers)
                matrix.db.expect('GET', '/posts/draft1', 403, headers=headers)
                matrix.db.expect('PATCH', '/posts/draft1', 403, {'title': 'stolen'}, headers)
                assert matrix.db.snapshot() == initial, 'failed refresh changed rows'
                assert len(state['requests']) == before + 3, 'refresh was skipped'
                state.update(status=200, document=original)
                matrix.db.expect('GET', '/posts/draft1', 200, headers=headers)
            assert all(req == ('/auth/v1/.well-known/jwks.json', None, None)
                       for req in state['requests']), 'JWKS path/header boundary failed'

        def verify_lists():
            ids = subjects or {name: name for name in ('alice', 'bob', 'root')}
            headers = {name: {'Authorization': 'Bearer ' + tokens[name]}
                       for name in ('alice', 'bob', 'root')}
            headers[None] = {'X-Principal': ids['root']}
            matrix.db.expect('POST', '/posts/bob-draft', 201,
                             {'title': 'bob draft', 'body': 'bob private'}, headers['bob'])
            stages = 0

            def compare(admins=('root',)):
                nonlocal stages
                before = matrix.db.snapshot()
                posts = json.loads(before)['posts'] or []
                for subject in (None, 'alice', 'bob', 'root'):
                    expected = {}
                    for post in posts:
                        key = post['_nyxis_id']
                        allowed = (post['published'][-1] or subject in admins or
                                   (subject is not None and post['author'][-1] == ids[subject]))
                        body = matrix.db.expect('GET', '/posts/' + key,
                                                200 if allowed else 403, headers=headers[subject])
                        if allowed:
                            expected[key] = dict(json.loads(body), id=key)
                    rows = json.loads(matrix.db.expect('GET', '/posts?subject=' + ids['root'],
                                                      200, headers=headers[subject]))
                    assert isinstance(rows, list), 'list must be a JSON array'
                    assert len(rows) == len(expected), 'missing/duplicate/extra list rows'
                    assert {row['id']: row for row in rows} == expected, 'list/readPost mismatch'
                assert matrix.db.snapshot() == before, 'listing changed persistent rows'
                stages += 1

            compare()
            # Every request must observe current publication and administrator state.
            matrix.db.expect('POST', '/posts/draft1/publish', 204, headers=headers['alice'])
            compare()
            matrix.db.expect('POST', '/posts/draft1/unpublish', 204, headers=headers['alice'])
            matrix.db.expect('PUT', '/users/' + ids['bob'] + '/admin', 204,
                             {'admin': True}, headers['root'])
            compare(('root', 'bob'))
            matrix.db.expect('PUT', '/users/' + ids['bob'] + '/admin', 204,
                             {'admin': False}, headers['root'])
            compare()
            for token in rejected:
                rows = json.loads(matrix.db.expect('GET', '/posts', 200,
                                  headers={'Authorization': 'Bearer ' + tokens[token]}))
                assert [row['id'] for row in rows] == ['pub1'], 'invalid JWT leaked drafts'
            # Empty authorized result and empty table both produce [], never an error.
            matrix.db.expect('POST', '/posts/pub1/unpublish', 204, headers=headers['alice'])
            compare()
            matrix.db.sql('DELETE FROM public."Post";', matrix.db.DATABASE)
            compare()
            print(f'listPosts: {stages} stages x 4 subjects; exact readPost rows/IDs, '
                  'publication, grant/revoke, empty and unchanged DB passed', flush=True)

        def verify_users():
            ids = subjects or {name: name for name in ('alice', 'bob', 'root')}
            headers = {name: {'Authorization': 'Bearer ' + tokens[name]}
                       for name in ('alice', 'bob', 'root')}
            headers[None] = {'X-Principal': ids['root']}
            initial = matrix.db.snapshot()
            initial_users = json.loads(initial)['users']
            requests = 0
            row_checks = 0

            def check(subject, method, target, status, data=None, expected=None, row=None):
                nonlocal requests, row_checks
                before = matrix.db.snapshot()
                body = matrix.db.expect(method, '/users/' + target + '?subject=' + ids['root'],
                                        status, data, headers[subject])
                if row is not None:
                    assert json.loads(body) == row, 'readUser returned wrong row/attributes'
                assert json.loads(matrix.db.snapshot()) == json.loads(expected or before), \
                    'user request changed unauthorized persistent rows'
                requests += 1
                row_checks += 1

            # Existing users: permission matrix and no overwrites, including admin self-registration.
            for subject in (None, 'alice', 'bob', 'root'):
                for target in ('alice', 'bob', 'root'):
                    allowed = subject == target or subject == 'root'
                    check(subject, 'GET', ids[target], 200 if allowed else 403,
                          row={'admin': target == 'root'} if allowed else None)
                    check(subject, 'POST', ids[target], 409 if subject == target else 403, {})
                    check(subject, 'POST', ids[target], 403, {'admin': True})
                check(subject, 'GET', 'missing-user', 404 if subject == 'root' else 403)
                check(subject, 'POST', 'missing-user', 403, {'admin': False})

            # Remove just a dedicated test DB row, leaving the actual Auth session valid.
            # Each subject must be able to bootstrap without already having a User entity.
            for subject in ('alice', 'bob', 'root'):
                uid = ids[subject]
                matrix.db.sql('DELETE FROM public."User" WHERE "_nyxis_id" = '
                              + matrix.quote(uid) + ';', matrix.db.DATABASE)
                try:
                    check(subject, 'GET', uid, 404)
                    check(None, 'GET', uid, 403)
                    for other in ('alice', 'bob', 'root'):
                        if other != subject:
                            check(other, 'POST', uid, 403, {'admin': False})
                    check(None, 'POST', uid, 403, {})
                    check(subject, 'POST', uid, 403, {'admin': True})
                    check(subject, 'POST', 'missing-user', 403, {})
                    check(subject, 'POST', uid, 400, {'admin': 'false'})
                    check(subject, 'POST', uid, 400, [])
                    expected = json.loads(matrix.db.snapshot())
                    expected['users'].append({'_nyxis_id': uid, 'admin': ['bool', False]})
                    expected['users'].sort(key=lambda row: row['_nyxis_id'])
                    data = {'admin': False} if subject == 'bob' else {}
                    check(subject, 'POST', uid, 201, data, json.dumps(expected))
                    check(subject, 'GET', uid, 200, row={'admin': False})
                    check(subject, 'POST', uid, 409, {})
                    check(subject, 'POST', uid, 403, {'admin': True})
                    check(subject, 'PUT', uid + '/admin', 403, {'admin': True})
                    for other in ('alice', 'bob', 'root'):
                        if other != subject:
                            allowed = other == 'root'
                            check(other, 'GET', uid, 200 if allowed else 403,
                                  row={'admin': False} if allowed else None)
                finally:
                    statements = ['DELETE FROM public."User";']
                    for row in initial_users:
                        statements.append('INSERT INTO public."User" VALUES (' +
                            matrix.quote(row['_nyxis_id']) + ', ' +
                            matrix.quote(json.dumps(row['admin'])) + ');')
                    matrix.db.sql('\n'.join(statements), matrix.db.DATABASE)
            for token in rejected:
                bad = {'Authorization': 'Bearer ' + tokens[token]}
                before = matrix.db.snapshot()
                for method, target, data in [('GET', ids['alice'], None),
                                              ('POST', ids['alice'], {}),
                                              ('POST', 'missing-user', {'admin': False})]:
                    matrix.db.expect(method, '/users/' + target, 403, data, bad)
                    requests += 1
                assert matrix.db.snapshot() == before, 'invalid JWT changed user rows'
            assert matrix.db.snapshot() == initial, 'user test did not restore its fixtures'
            print(f'users: {requests} HTTP / {row_checks} full-row checks; four subjects, '
                  '3 unregistered Auth subjects, self-only/non-admin 201, duplicate 409, '
                  'read permissions/404, malformed 400, invalid JWTs and DB invariance passed', flush=True)

        def verify_all():
            def released():
                query = ("SELECT count(*) FROM pg_stat_activity WHERE datname = '"
                         + matrix.db.DATABASE + "';")
                for _ in range(40):
                    count = int(matrix.db.sql(query))
                    if count == 0:
                        return
                    time.sleep(0.05)
                raise AssertionError('sample retains database sessions')

            if subjects is not None:
                for name, uid in subjects.items():
                    matrix.db.sql('UPDATE public."User" SET "_nyxis_id" = ' + matrix.quote(uid)
                                  + ' WHERE "_nyxis_id" = ' + matrix.quote(name) + ';', matrix.db.DATABASE)
                author = json.dumps(['entity', [], 'User', subjects['alice']])
                matrix.db.sql('UPDATE public."Post" SET author = ' + matrix.quote(author) + ';',
                              matrix.db.DATABASE)
            matrix.verify(tokens, subjects, rejected_tokens=rejected)
            released()
            verify_refresh()
            released()
            # The same sample stays alive through the matrix, refresh failures,
            # and more successful DB requests than the server's connection cap.
            limit = int(matrix.db.sql('SHOW max_connections;'))
            assert 0 < limit < 10000, 'unexpected local connection limit'
            initial = matrix.db.snapshot()
            root = {'Authorization': 'Bearer ' + tokens['root']}
            for index in range(limit + 1):
                matrix.db.expect('GET', '/posts/draft1', 200, headers=root)
                if index % 20 == 0:
                    released()
            released()
            assert matrix.db.snapshot() == initial, 'repeated reads changed rows'
            print(f'sample-lifetime: {limit + 1} successful authenticated reads '
                  f'(max_connections={limit}); 0 sessions while sample alive', flush=True)
            verify_users()
            released()
            verify_lists()
            released()

        matrix.db.main(verify=verify_all, issuer=issuer)
        if real_auth:
            assert state['upstream'] > 100, 'live Auth JWKS proxy was skipped'

    print(f'check-sample-jwt-db: {matrix.db.checks} HTTP + {matrix.checks} persistent-row checks; '
          f'{len(state["requests"])} HTTPS JWKS requests; test DB removed '
          f'(actual sample, real clock/DB; '
          f'{"3 Auth magic-link sessions/users removed, live public JWKS upstream " + str(state["upstream"]) if real_auth else "approved ES256 fixtures"})')


if __name__ == '__main__':
    try:
        main()
    except Exception:
        raise SystemExit('check-sample-jwt-db failed (diagnostics withheld)')
