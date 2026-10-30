#!/usr/bin/env python3
"""Decision-material fetching: actual sample (staged path) on an isolated local Supabase DB at 100k-row scale.

The same request sequence is sent against the fixture-only database ("empty"), after adding
100k User rows ("users"), and after also adding 100k Post rows ("posts"). For every request
the rows PostgreSQL read (pg_stat_user_tables: seq_tup_read + idx_tup_read, per table) and
the response time are recorded. From every table that holds the 100k rows, a request may read
at most what it read from that table in the empty state (plus a small slack for index lookups);
non-list requests additionally stay under an absolute ceiling, and list requests are not sent
once the Post table, their own target, is large. Median response times in the loaded states
must stay within twice the empty-state medians.

Approved fixture ES256 JWTs (not Supabase Auth), a test-only TLS JWKS relay, and only this run's
newly created DB, which is removed. Run after lake build via python3 scripts/local-supabase.py --exec python3
<this script>. Credentials and child diagnostics are never printed.
"""
from contextlib import ExitStack
import importlib.util
import json
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import time
import uuid

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
spec = importlib.util.spec_from_file_location('db', ROOT / 'scripts/check-local-postgres-http.py')
db = importlib.util.module_from_spec(spec)
spec.loader.exec_module(db)

SCALE = 100000
REPEATS = 12
SLACK = 2        # rows per large table: index lookups may examine an entry the tiny table's scan did not
BOUND = 16       # rows: absolute ceiling per non-list request in the loaded states (SCALE = 100000)
TABLES = ('User', 'Post')
LARGE = {'empty': (), 'users': ('User',), 'posts': ('User', 'Post')}   # tables holding SCALE rows per phase


def quote(value):
    return "'" + value.replace("'", "''") + "'"


def bulk(statement):
    """Like db.sql on the test DB, with a longer timeout for the bulk inserts."""
    result = subprocess.run(
        ['docker', '--context', db.ENV['DOCKER_CONTEXT'], 'exec', '-i', 'supabase_db_nyxis',
         'psql', '-X', '-U', 'postgres', '-d', db.DATABASE, '-At', '-v', 'ON_ERROR_STOP=1'],
        input=statement.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=db.ENV, timeout=600)
    if result.returncode:
        raise RuntimeError('local test SQL failed (diagnostics withheld)')
    return result.stdout.decode().strip()


def stats():
    """Per-table (seq_tup_read, idx_tup_read) of the test DB. A fresh session each time, so the
    cumulative statistics are current; reading the views touches no user table."""
    # nyxis's reserved outbox exists in every provisioned database; the sample declares no async call, so it
    # is never read or written here and stays outside the per-table comparison.
    rows = db.sql('SELECT t.relname, t.seq_tup_read, coalesce(sum(i.idx_tup_read), 0) '
                  'FROM pg_stat_user_tables t LEFT JOIN pg_stat_user_indexes i ON i.relid = t.relid '
                  "WHERE t.schemaname = 'public' AND t.relname <> '_nyxis_outbox' "
                  'GROUP BY t.relname, t.seq_tup_read ORDER BY t.relname;',
                  db.DATABASE).splitlines()
    out = {name: tuple(map(int, rest)) for name, *rest in (row.split('|') for row in rows)}
    assert set(out) == set(TABLES), 'unexpected tables'
    return out


def released():
    # Closed sessions flush their statistics; wait until the sample holds no session.
    query = ("SELECT count(*) FROM pg_stat_activity WHERE backend_type = 'client backend' "
             "AND datname = '" + db.DATABASE + "';")
    for _ in range(100):
        if int(db.sql(query)) == 0:
            return
        time.sleep(0.05)
    raise AssertionError('sample retains database sessions')


def fixture_rows():
    return bulk('''SELECT jsonb_build_object(
        'users', (SELECT jsonb_agg(to_jsonb(u) ORDER BY "_nyxis_id") FROM public."User" u
                  WHERE "_nyxis_id" IN ('alice', 'bob', 'root')),
        'posts', (SELECT jsonb_agg(to_jsonb(p) ORDER BY "_nyxis_id") FROM public."Post" p
                  WHERE "_nyxis_id" IN ('pub1', 'draft1')));''')


def counts():
    return tuple(int(bulk(f'SELECT count(*) FROM public."{table}";')) for table in TABLES)


def main():
    with ExitStack() as resources:
        tmp = resources.enter_context(tempfile.TemporaryDirectory(prefix='nyxis-materials-scale-'))
        work = Path(tmp)
        cert, key = resources.enter_context(nyxis_local.tls_material('nyxis-materials-scale-'))
        subprocess.run([sys.executable, str(ROOT / 'scripts/jwt-dependency/make-fixture.py'), tmp],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        document = (work / 'test-jwks.json').read_bytes()
        handler = nyxis_local.relay_handler(lambda: document)
        server = resources.enter_context(nyxis_local.tls_server(handler, cert, key))
        issuer = f'https://localhost:{server.server_port}/auth/v1'
        subprocess.run([str(ROOT / '.lake/build/bin/checkJwtDependency'), tmp, issuer],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        tokens = {name: (work / ('issuer-' + name + '.jwt')).read_text() for name in ('alice', 'bob', 'root')}
        # Trust this ephemeral CA only in the test child environment.
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            db.ENV.pop(name, None)
        db.ENV['CURL_CA_BUNDLE'] = str(cert)

        def headers(subject):
            return {} if subject is None else {'Authorization': 'Bearer ' + tokens[subject]}

        fresh = {}

        def new_post():
            fresh['id'] = str(uuid.uuid4())
            return '/posts/' + fresh['id']

        edit = {'title': 'draft', 'body': 'private body'}
        # (name, group, subject, method, path, body, expected status). The sequence restores the
        # fixture rows itself (publish/unpublish, grant/revoke, create/delete pairs).
        catalog = [
            ('read-public-anon', 'point', None, 'GET', '/posts/pub1', None, 200),
            ('read-draft-author', 'point', 'alice', 'GET', '/posts/draft1', None, 200),
            ('read-draft-other', 'point', 'bob', 'GET', '/posts/draft1', None, 403),
            ('read-draft-admin', 'point', 'root', 'GET', '/posts/draft1', None, 200),
            ('read-missing-anon', 'point', None, 'GET', '/posts/missing', None, 403),
            ('edit-author', 'point', 'alice', 'PATCH', '/posts/draft1', edit, 204),
            ('edit-other', 'point', 'bob', 'PATCH', '/posts/draft1', edit, 403),
            ('publish-author', 'point', 'alice', 'POST', '/posts/draft1/publish', None, 204),
            ('unpublish-author', 'point', 'alice', 'POST', '/posts/draft1/unpublish', None, 204),
            ('create-own', 'point', 'bob', 'POST', new_post,
             {'title': 'scale', 'body': 'scale', 'published': False}, 201),
            ('delete-own', 'point', 'bob', 'DELETE', lambda: '/posts/' + fresh['id'], None, 204),
            ('delete-other', 'point', 'bob', 'DELETE', '/posts/draft1', None, 403),
            ('grant-admin', 'point', 'root', 'PUT', '/users/bob/admin', {'admin': True}, 204),
            ('revoke-admin', 'point', 'root', 'PUT', '/users/bob/admin', {'admin': False}, 204),
            ('grant-denied', 'point', 'alice', 'PUT', '/users/bob/admin', {'admin': True}, 403),
            ('read-user-self', 'point', 'alice', 'GET', '/users/alice', None, 200),
            ('read-user-other', 'point', 'bob', 'GET', '/users/alice', None, 403),
            ('read-user-admin', 'point', 'root', 'GET', '/users/bob', None, 200),
            ('read-user-missing-admin', 'point', 'root', 'GET', '/users/missing', None, 404),
            ('register-duplicate', 'point', 'alice', 'POST', '/users/alice', {}, 409),
            ('list-anon', 'list', None, 'GET', '/posts', None, 200),
            ('list-author', 'list', 'alice', 'GET', '/posts', None, 200),
            ('list-admin', 'list', 'root', 'GET', '/posts', None, 200),
        ]
        results = {}   # phase -> name -> {'reads': [per repetition total], 'ms': [...], 'tables': {...}}
        lists_expected = {None: ['pub1'], 'alice': ['draft1', 'pub1'], 'root': ['draft1', 'pub1']}

        def measure(phase, groups):
            record = results[phase] = {}
            initial = fixture_rows()
            released()
            before = stats()
            for _ in range(REPEATS):
                for name, group, subject, method, path, body, status in catalog:
                    if group not in groups:
                        continue
                    target = path() if callable(path) else path
                    started = time.perf_counter()
                    content = db.expect(method, target, status, body, headers(subject))
                    elapsed = (time.perf_counter() - started) * 1000
                    if group == 'list':
                        assert sorted(row['id'] for row in json.loads(content)) == lists_expected[subject], \
                            'list rows differ from the fixture expectation'
                    released()
                    after = stats()
                    delta = {table: tuple(a - b for a, b in zip(after[table], before[table])) for table in TABLES}
                    before = after
                    entry = record.setdefault(name, {'reads': [], 'ms': [], 'tables': {}})
                    entry['reads'].append(sum(d[0] + d[1] for d in delta.values()))
                    entry['ms'].append(elapsed)
                    for table, d in delta.items():
                        entry['tables'].setdefault(table, []).append(d)   # (seq_tup_read, idx_tup_read)
            assert fixture_rows() == initial, 'the request sequence did not restore the fixture rows'

        def load(table, statement):
            bulk(statement)
            bulk(f'ANALYZE public."{table}";')

        def verify():
            base = counts()
            assert base == (3, 2), 'unexpected fixture rows'
            measure('empty', ('point', 'list'))
            load('User', f'''INSERT INTO public."User" ("_nyxis_id", admin)
                SELECT 'scale-user-' || g, '["bool",false]'::jsonb FROM generate_series(1, {SCALE}) g;''')
            assert counts() == (3 + SCALE, 2), 'User scale rows missing'
            measure('users', ('point', 'list'))
            load('Post', f'''INSERT INTO public."Post" ("_nyxis_id", author, title, body, published)
                SELECT 'scale-post-' || g,
                       ('["entity",[],"User","scale-user-' || (g % {SCALE} + 1) || '"]')::jsonb,
                       '["string","scale title"]'::jsonb, '["string","scale body"]'::jsonb,
                       (CASE WHEN g % 2 = 0 THEN '["bool",true]' ELSE '["bool",false]' END)::jsonb
                FROM generate_series(1, {SCALE}) g;''')
            assert counts() == (3 + SCALE, 2 + SCALE), 'Post scale rows missing'
            measure('posts', ('point',))
            assert counts() == (3 + SCALE, 2 + SCALE), 'the request sequence leaked rows'
            # Positive control of the measurement channel: a full scan is visible in the same view
            # (the predicate on an unindexed column keeps this a heap scan, not an index-only one).
            released()
            before = stats()
            assert int(bulk('SELECT count(*) FROM public."Post" WHERE body IS NOT NULL;')) == 2 + SCALE
            assert stats()['Post'][0] - before['Post'][0] >= SCALE, 'statistics view did not record a full scan'

        db.main(verify=verify, issuer=issuer)

    # Evaluate after the sample and the DB are gone; print only counts and milliseconds.
    def worst(entry, table):
        """The repetition that read most (seq_tup_read + idx_tup_read) from `table`."""
        return max(entry['tables'][table], key=lambda d: d[0] + d[1])

    print(f'phase: rows read (max over {REPEATS}) / median ms  [User seq,idx | Post seq,idx]')
    failures = []
    for name, group, *_ in catalog:
        line = f'{name:20}'
        empty = results['empty'][name]
        for phase in ('empty', 'users', 'posts'):
            entry = results[phase].get(name)
            if entry is None:
                line += f'  {phase}: -'.ljust(28)
                continue
            reads, median = max(entry['reads']), statistics.median(entry['ms'])
            tables = ' | '.join(f'{worst(entry, t)[0]},{worst(entry, t)[1]}' for t in TABLES)
            line += f'  {phase}: {reads:>3} / {median:7.1f} ms [{tables}]'
            if phase == 'empty':
                continue
            for table in LARGE[phase]:
                got, base = sum(worst(entry, table)), sum(worst(empty, table))
                if got > base + SLACK:
                    failures.append(f'{name} {phase}: {table} rows read {got} > empty {base} + {SLACK}')
            if group == 'point' and reads > BOUND:
                failures.append(f'{name} {phase}: rows read {reads} > {BOUND}')
            if median > 2 * statistics.median(empty['ms']):
                failures.append(f'{name} {phase}: median {median:.1f} ms > 2 x empty '
                                f'{statistics.median(empty["ms"]):.1f} ms')
        print(line)
    if failures:
        print('\n'.join(failures))
        raise SystemExit('check-materials-scale failed: reads or latency depend on non-target rows')
    print(f'check-materials-scale: {db.checks} HTTP checks over 3 states (fixture; +{SCALE} User; '
          f'+{SCALE} Post), {REPEATS} repetitions, {len(catalog) - 3} point and 3 list request kinds '
          '(lists not sent once Post, their target table, is large); '
          'rows read from the 100k-row tables within empty-state slack, point requests under the '
          'absolute ceiling, medians within 2x; test DB removed')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-materials-scale interrupted (cleanup attempted)')
    except Exception:
        # Exceptions from URL/SQL/process code can carry credentials; do not print them.
        raise SystemExit('check-materials-scale failed (diagnostics withheld)')
