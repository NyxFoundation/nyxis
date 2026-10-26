#!/usr/bin/env python3
"""Approved fixture ES256 -> HTTP -> real local Supabase DB; not Auth-issued JWTs."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
helper_path = Path(__file__).resolve().parents[1] / 'check-local-postgres-http.py'
spec = importlib.util.spec_from_file_location('local_db', helper_path)
db = importlib.util.module_from_spec(spec)
spec.loader.exec_module(db)
checks = 0


def quote(value):
    return "'" + value.replace("'", "''") + "'"


def verify(tokens, subjects=None, rejected_tokens=()):
    subjects = subjects or {name: name for name in ('alice', 'bob', 'root')}
    global checks
    initial = json.loads(db.snapshot())

    def reset():
        # Only this invocation's newly created test DB, never application/Auth data.
        statements = []
        for table, rows in [('Post', initial['posts']), ('User', initial['users'])]:
            statements.append(f'DELETE FROM public."{table}";')
            for row in rows:
                columns = ','.join('"' + col + '"' for col in row)
                values = ','.join(quote(value if col == '_nyxis_id' else json.dumps(value))
                                  for col, value in row.items())
                statements.append(f'INSERT INTO public."{table}" ({columns}) VALUES ({values});')
        db.sql('\n'.join(statements), db.DATABASE)

    def check(subject, method, path, success, allowed, data=None, change=None):
        global checks
        reset()
        expected = json.loads(json.dumps(initial))
        headers = {'X-Principal': subjects['root']}
        if subject is not None:
            headers['Authorization'] = 'Bearer ' + tokens[subject]
        content = db.expect(method, path + '?subject=' + subjects['root'], success if allowed else 403,
                            data, headers)
        if allowed and change:
            change(expected)
        if method == 'GET' and allowed:
            row = next(p for p in expected['posts'] if p['_nyxis_id'] == path.split('/')[-1])
            assert json.loads(content) == {
                key: value[-1] for key, value in row.items() if key != '_nyxis_id'}
        assert json.loads(db.snapshot()) == expected, 'persistent rows differ from authorized effect'
        checks += 1

    for subject in [None, 'alice', 'bob', 'root']:
        manage = subject in ('alice', 'root')
        for post in ['pub1', 'draft1']:
            def update(state, column, value, post=post):
                next(p for p in state['posts'] if p['_nyxis_id'] == post)[column] = value
            check(subject, 'GET', '/posts/' + post, 200, post == 'pub1' or manage)
            check(subject, 'PATCH', '/posts/' + post, 204, manage, {'title': "changed ' title"},
                  lambda state: update(state, 'title', ['string', "changed ' title"]))
            for action, published in [('publish', True), ('unpublish', False)]:
                check(subject, 'POST', '/posts/' + post + '/' + action, 204, manage,
                      change=lambda state, value=published: update(state, 'published', ['bool', value]))
            check(subject, 'DELETE', '/posts/' + post, 204, manage,
                  change=lambda state, post=post: state['posts'].__setitem__(
                      slice(None), [p for p in state['posts'] if p['_nyxis_id'] != post]))
        for published in [False, True]:
            def insert(state, published=published):
                state['posts'].append(dict(_nyxis_id='new', author=['entity', [], 'User', subjects[subject]],
                    title=['string', 'new'], body=['string', 'new body'], published=['bool', published]))
                state['posts'].sort(key=lambda p: p['_nyxis_id'])
            check(subject, 'POST', '/posts/new', 201, subject is not None,
                  dict(title='new', body='new body', published=published, author=subjects['root']), insert)
        for target, admin in [('bob', True), ('root', False)]:
            def grant(state, target=target, admin=admin):
                next(u for u in state['users'] if u['_nyxis_id'] == subjects[target])['admin'] = ['bool', admin]
            check(subject, 'PUT', '/users/' + subjects[target] + '/admin', 204, subject == 'root',
                  {'admin': admin}, grant)
    for token in rejected_tokens:
        check(token, 'GET', '/posts/pub1', 200, True)
        check(token, 'GET', '/posts/draft1', 200, False)
        check(token, 'PATCH', '/posts/draft1', 204, False, {'title': 'stolen'})
    # Authorization follows persisted grants/revocations on the very next request.
    reset()
    root = {'Authorization': 'Bearer ' + tokens['root']}
    bob = {'Authorization': 'Bearer ' + tokens['bob']}
    db.expect('GET', '/posts/draft1', 403, headers=bob)
    db.expect('PUT', '/users/' + subjects['bob'] + '/admin', 204, {'admin': True}, root)
    db.expect('GET', '/posts/draft1', 200, headers=bob)
    db.expect('PUT', '/users/' + subjects['bob'] + '/admin', 204, {'admin': False}, root)
    db.expect('GET', '/posts/draft1', 403, headers=bob)

    # Exercise real PGresult errors and checked COMMIT, rather than an injected
    # driver. AFTER triggers run after the row operation; deferred constraint
    # triggers fail at COMMIT. A nontransactional sequence witnesses execution
    # even though every application row must roll back. All DDL is test-DB-only.
    for deferred in (False, True):
        for table, method, path, data, success in [
                ('Post', 'POST', '/posts/fault-new',
                 dict(title='new', body='new body', published=False), 201),
                ('Post', 'PATCH', '/posts/draft1', {'title': 'fault title'}, 204),
                ('Post', 'DELETE', '/posts/draft1', None, 204),
                ('User', 'PUT', '/users/' + subjects['bob'] + '/admin', {'admin': True}, 204)]:
            reset()
            before = db.snapshot()
            constraint = 'CONSTRAINT ' if deferred else ''
            timing = 'DEFERRABLE INITIALLY DEFERRED ' if deferred else ''
            db.sql('''CREATE SEQUENCE public.nyxis_fault_seen;
                CREATE FUNCTION public.nyxis_fault() RETURNS trigger LANGUAGE plpgsql AS $$
                BEGIN
                  PERFORM nextval('public.nyxis_fault_seen');
                  RAISE EXCEPTION 'nyxis private injected database failure';
                END $$;
                CREATE ''' + constraint + '''TRIGGER nyxis_fault
                AFTER INSERT OR UPDATE OR DELETE ON public."''' + table + '''"
                ''' + timing + '''FOR EACH ROW EXECUTE FUNCTION public.nyxis_fault();''', db.DATABASE)
            try:
                content = db.expect(method, path, 503, data, root)
                assert content == 'backend unavailable', 'database diagnostics leaked'
                assert db.sql('SELECT last_value, is_called FROM public.nyxis_fault_seen;',
                              db.DATABASE) == '1|t', 'failure did not reach row/COMMIT trigger'
                assert db.snapshot() == before, 'failed transaction persisted application rows'
                checks += 1
            finally:
                db.sql('DROP TRIGGER nyxis_fault ON public."' + table + '''";
                    DROP FUNCTION public.nyxis_fault();
                    DROP SEQUENCE public.nyxis_fault_seen;''', db.DATABASE)
            # The same running server opens a fresh usable transaction after failure.
            db.expect(method, path, success, data, root)
            assert db.snapshot() != before, 'request did not recover after database failure'
            checks += 1
    reset()
    print('DB faults: 8 statement/COMMIT failures, 8 rollbacks and 8 recoveries passed')


if __name__ == '__main__':
    work = Path(sys.argv[1])
    rejected = ('bad-signature', 'expired', 'wrong-issuer')
    tokens = {name: (work / (name + '.jwt')).read_text()
              for name in ('alice', 'bob', 'root') + rejected}
    try:
        db.main([str(work / 'check/.lake/build/bin/serveJwtHttp'), str(work),
                 str(db.PORT), 'local-db'], lambda: verify(tokens, rejected_tokens=rejected))
    except Exception:
        raise SystemExit('JWT local DB check failed (diagnostics withheld)')
    print(f'JWT local DB: {db.checks} HTTP + {checks} persistent-row checks passed '
          '(four subjects, approved fixture ES256; Supabase Auth JWTs remain)')
