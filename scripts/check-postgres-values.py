#!/usr/bin/env python3
"""Extended values: datetime / decimal / Set / record columns on a real local PostgreSQL (local Supabase).

Run after `lake build` via `python3 scripts/local-supabase.py --exec python3 scripts/check-postgres-values.py`.
For each of nyxis's two real connection paths (snapshot: PostgresRun.handle; staged: PostgresRun.handleStaged,
per-call point lookups) creates a uniquely named local database, runs the core executable
`checkPostgresValues` (Test/PostgresValues.lean: provisions the test schema, then drives the path
for inserts / reads / updates / deletes and the policy comparisons), then checks the JSONB cells
left in the database against the storage format, and drops only the database it created.
Existing application/Auth databases are never touched. Credentials are never printed.
"""
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

DATABASE = 'nyxis_values_test_' + uuid.uuid4().hex
ENV = nyxis_local.scrub_docker_env(os.environ.copy())
checks = 0

USER = lambda name: ['entity', [], 'User', name]
EXPECTED_D1 = {
    '_nyxis_id': 'd1',
    'owner': USER('alice'),
    'viewers': ['set', [USER('bob')]],
    'labels': ['set', [['string', 'public'], ['string', 'x']]],
    'created': ['datetime', '1767225600000'],
    'expires': ['datetime', '1811808000000'],
    'price': ['decimal', '52500'],
    'meta': ['record', [['editor', USER('carol')], ['pinned', ['bool', True]]]],
}


def sql(statement, database='postgres'):
    result = subprocess.run(
        ['docker', '--context', ENV['DOCKER_CONTEXT'], 'exec', '-i', 'supabase_db_nyxis',
         'psql', '-X', '-U', 'postgres', '-d', database, '-At', '-v', 'ON_ERROR_STOP=1'],
        input=statement.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=ENV, timeout=30)
    if result.returncode:
        raise RuntimeError('local test SQL failed (diagnostics withheld)')
    return result.stdout.decode().strip()


def expect(condition, what):
    global checks
    assert condition, what
    checks += 1


def main():
    total = 0
    for path in ('snapshot', 'staged'):
        total += run_path(path)
    print(f'check-postgres-values: both connection paths passed ({total} Lean checks in total; real local DB)')


def run_path(path):
    global checks
    checks = 0
    database = DATABASE + '_' + path
    endpoint = urlsplit(os.environ.get('NYXIS_DATABASE_URL', ''))
    assert endpoint.scheme in ('postgres', 'postgresql'), 'local DB URL required'
    assert endpoint.hostname in ('127.0.0.1', 'localhost', '::1'), 'local DB required'
    assert endpoint.port == 55322 and endpoint.path == '/postgres', 'nyxis local DB required'
    assert not endpoint.query and not endpoint.fragment, 'unexpected DB URL options'
    nyxis_local.require_local_docker(ENV)
    env = ENV.copy()
    env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + database))
    env['NYXIS_VALUES_PATH'] = path
    created = False
    try:
        sql('CREATE DATABASE "' + database + '";')
        created = True
        result = subprocess.run([str(ROOT / '.lake/build/bin/checkPostgresValues')], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
        summary = result.stdout.decode().strip()
        if result.returncode or not summary.startswith('check-postgres-values: '):
            # The executable reports only check names; connection diagnostics are still withheld here.
            tail = result.stderr.decode().strip().splitlines()[-1:] if result.stderr else []
            raise RuntimeError('checkPostgresValues failed: ' + (tail[0] if tail and tail[0].startswith('check-postgres-values') else '(diagnostics withheld)'))
        print(summary)
        lean_checks = int(summary.split()[1])
        assert lean_checks >= 50, 'unexpectedly few Lean checks'
        assert summary.endswith('path=' + path + ')'), 'executable did not report the requested path'
        # The rows left behind use the documented JSONB cell format (tags kept per type).
        expect(sql('SELECT count(*) FROM public."Doc";', database) == '1', 'd3 deleted, d1 remains')
        stored = json.loads(sql('SELECT to_jsonb(d)::text FROM public."Doc" d WHERE "_nyxis_id" = \'d1\';', database))
        expect(stored == EXPECTED_D1, 'd1 JSONB cells')
        expect(sql('SELECT string_agg("_nyxis_id", \',\' ORDER BY "_nyxis_id") FROM public."User";', database)
               == 'alice,bob,carol', 'registered users')
        expect(sql('SELECT DISTINCT admin::text FROM public."User";', database) == '["bool", false]', 'admin cells')
        columns = sql('''SELECT string_agg(column_name || ':' || data_type, ',' ORDER BY ordinal_position)
                         FROM information_schema.columns WHERE table_schema = 'public' AND table_name = 'Doc';''', database)
        expect(columns == '_nyxis_id:text,owner:jsonb,viewers:jsonb,labels:jsonb,created:jsonb,expires:jsonb,price:jsonb,meta:jsonb',
               'Doc columns are nullable JSONB cells per attribute')
        print(f'check-postgres-values [{path}]: {lean_checks} Lean checks and {checks} stored-cell checks passed (real local DB)')
        return lean_checks
    finally:
        if created:
            sql('DROP DATABASE "' + database + '";')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-postgres-values interrupted (cleanup attempted)')
    except Exception as error:
        message = str(error) if isinstance(error, (AssertionError, RuntimeError)) else '(diagnostics withheld)'
        raise SystemExit('check-postgres-values failed: ' + message)
