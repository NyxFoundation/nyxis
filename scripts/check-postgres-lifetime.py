#!/usr/bin/env python3
"""Require release after 12 native calls, while each probe process stays alive.

Run after lake build via python3 scripts/local-supabase.py --exec python3 <this script>.
Uses only a newly created local test database; never contacts a real project.
"""
import importlib.util
import os
from pathlib import Path
import select
import subprocess
import sys
import time
import tempfile
from urllib.parse import urlsplit, urlunsplit

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('db', ROOT / 'scripts/check-local-postgres-http.py')
db = importlib.util.module_from_spec(spec)
spec.loader.exec_module(db)


def verify():
    env = db.ENV.copy()
    endpoint = urlsplit(os.environ['NYXIS_DATABASE_URL'])
    env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + db.DATABASE))
    counts = {}
    for mode in ('raw', 'status', 'transaction'):
        diagnostics = tempfile.TemporaryFile()
        proc = subprocess.Popen([str(ROOT / '.lake/build/bin/checkPostgresLifetime'), mode],
                                env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=diagnostics)
        try:
            assert select.select([proc.stdout], [], [], 20)[0], 'probe readiness timeout'
            assert proc.stdout.readline() == b'ready\n', 'probe failed before ready'
            # Dedicated DB name is generated internally, never request/config text.
            query = "SELECT count(*) FROM pg_stat_activity WHERE datname = '" + db.DATABASE + "';"
            for _ in range(20):
                counts[mode] = int(db.sql(query))
                if counts[mode] == 0:
                    break
                time.sleep(0.05)
            assert proc.poll() is None, 'probe exited before session observation'
            diagnostics.seek(0)
            lines = diagnostics.read().splitlines()
            for created, finalized, expected in [(b'Connection ', b'pq_connection_finalizer ', 12),
                                                  (b'Result ', b'pq_result_finalizer ',
                                                   24 if mode == 'transaction' else 0)]:
                made = sum(line.startswith(created) for line in lines)
                freed = sum(line.startswith(finalized) for line in lines)
                assert made == freed == expected, 'native finalizer count mismatch'
            print(f'postgres-lifetime: {mode}: connection/result finalizers balanced', flush=True)
            print(f'postgres-lifetime: {mode}: {counts[mode]} sessions after 12 calls', flush=True)
            proc.communicate(b'\n', timeout=5)
            assert proc.returncode == 0, 'probe failed on exit'
        finally:
            if proc.poll() is None:
                db.stop(proc)
            proc.stdin.close()
            proc.stdout.close()
            diagnostics.close()
    assert all(n == 0 for n in counts.values()), 'native calls retain database sessions'


if __name__ == '__main__':
    try:
        db.main(verify=verify)
    except Exception:
        raise SystemExit('check-postgres-lifetime failed (diagnostics withheld)')
