#!/usr/bin/env python3
"""Provisioning CLI validation and real libpq refusal; never use inherited DB credentials."""
import os
from pathlib import Path
import subprocess

if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / 'examples/bulletin-board/backend/.lake/build/bin/initSampleDatabase'
ENV = {k: v for k, v in os.environ.items() if k != 'NYXIS_DATABASE_URL'}
SENTINEL = 'init-secret-must-not-appear'
checks = 0


def rejected(args, config, message):
    global checks
    env = dict(ENV)
    if config is not None:
        env['NYXIS_DATABASE_URL'] = config
    run = subprocess.run([str(BINARY), *args], env=env, capture_output=True, timeout=10)
    output = (run.stdout + run.stderr).decode('utf-8')
    assert run.returncode != 0, 'failed initialization reported success'
    assert message in output, 'expected diagnostic missing'
    assert 'database initialized' not in output, 'premature success message'
    assert SENTINEL not in output, 'connection details leaked'
    checks += 1


rejected([], None, 'NYXIS_DATABASE_URL is required')
rejected([], '', 'NYXIS_DATABASE_URL is invalid')
rejected([], ' \t ', 'NYXIS_DATABASE_URL is invalid')
rejected([SENTINEL], None, 'usage: initSampleDatabase')
rejected([], f'host=127.0.0.1 port=1 connect_timeout=1 password={SENTINEL}',
         'sample database initialization failed')
# An unrecognized option would reveal its name through libpq's raw error message.
rejected([], f'{SENTINEL}=invalid', 'sample database initialization failed')
print(f'check-sample-init: {checks} checks passed (CLI + libpq refusal; no Supabase)')
