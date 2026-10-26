#!/usr/bin/env python3
"""Serve the frontend demo using a disposable local Supabase database.

Run after lake build via python3 scripts/local-supabase.py --exec python3 <this script>.
Reuse the local integration fixture's endpoint validation, provisioning and cleanup.
No existing database or Auth user is modified. Credentials are never printed.
"""
import argparse
from contextlib import contextmanager, nullcontext
import importlib.util
import json
import os
from pathlib import Path
import select
import signal
import sys
import threading
import uuid

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
ISSUER = 'https://localhost:55325/auth/v1'


@contextmanager
def jwks_bridge(db):
    # This bridge serves only public keys from the fixed local Auth endpoint.
    assert os.environ.get('NYXIS_SUPABASE_URL') == nyxis_local.LOCAL_AUTH
    assert os.environ.get('NYXIS_SUPABASE_ANON_KEY'), 'local anon key required'
    assert any(key.get('alg') == 'ES256' for key in json.loads(nyxis_local.local_jwks())['keys'])
    with nyxis_local.tls_material('nyxis-demo-tls-') as (cert, key), \
            nyxis_local.tls_server(nyxis_local.relay_handler(nyxis_local.local_jwks), cert, key, port=55325):
        # The temporary CA belongs only to the sample child, never the OS/browser.
        db.ENV['CURL_CA_BUNDLE'] = str(cert)
        yield


def bootstrap_admin(db, command):
    parts = command.split()
    if len(parts) != 2 or parts[0] != 'admin':
        return False
    try:
        uid = str(uuid.UUID(parts[1]))
    except ValueError:
        return False
    # A canonical UUID is the only variable in this operator-only SQL. Only the
    # disposable DB is reachable; the account must already have registered via HTTP.
    if parts[1] != uid:
        return False
    result = db.sql('UPDATE public."User" SET admin = \'["bool",true]\' '
                    'WHERE "_nyxis_id" = \'' + uid + '\' RETURNING "_nyxis_id";', db.DATABASE)
    return uid in result.splitlines()


def operator_console(db, stopped):
    print('OAuth ready. After login and registration, copy your ID from /me.', flush=True)
    print('First admin: enter admin <UUID> here once. Further grants use /admin. Ctrl-C to stop.', flush=True)
    bootstrapped = False
    input_open = True
    while not stopped.is_set():
        if not input_open:
            stopped.wait(0.25)
            continue
        if not select.select([sys.stdin], [], [], 0.25)[0]:
            continue
        line = sys.stdin.readline()
        if not line:
            input_open = False
            continue
        if not bootstrapped and bootstrap_admin(db, line):
            bootstrapped = True
            print('First admin ready in this demo DB. Reload /me to see the admin menu.', flush=True)
        else:
            print('No change. Use admin <registered UUID> once; further grants use /admin.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oauth', action='store_true', help='bridge local Auth JWKS and enable first-admin console')
    args = parser.parse_args()
    os.environ.setdefault('NYXIS_LOCAL_HTTP_PORT', '8080')
    spec = importlib.util.spec_from_file_location(
        'local_db', ROOT / 'scripts/check-local-postgres-http.py')
    db = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(db)
    db.ENV['NYXIS_CORS_ORIGINS'] = 'http://127.0.0.1:3000,http://localhost:3000'
    stopped = threading.Event()
    previous = {sig: signal.signal(sig, lambda *_: stopped.set())
                for sig in (signal.SIGINT, signal.SIGTERM)}

    def serve():
        initial = db.snapshot()
        rows = json.loads(db.expect('GET', '/posts', 200))
        assert rows == [dict(id='pub1', author='alice', title='public',
                             body='public body', published=True)]
        db.expect('GET', '/posts/pub1', 200)
        db.expect('GET', '/posts/draft1', 403)
        print(f'Ready: http://127.0.0.1:{db.PORT} (isolated local Supabase DB).', flush=True)
        if args.oauth:
            operator_console(db, stopped)
        else:
            print('Anonymous demo: pub1 is public; draft1 is private. Ctrl-C to stop and remove this demo DB.',
                  flush=True)
            stopped.wait()
            assert db.snapshot() == initial, 'anonymous demo changed rows'

    try:
        with jwks_bridge(db) if args.oauth else nullcontext():
            db.main(verify=serve, issuer=ISSUER)
        print('Stopped: sample exited; this demo database was removed.', flush=True)
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


if __name__ == '__main__':
    try:
        main()
    except Exception:
        raise SystemExit('Demo failed (diagnostics withheld). Check local Supabase, lake build, OpenSSL and port availability.')
