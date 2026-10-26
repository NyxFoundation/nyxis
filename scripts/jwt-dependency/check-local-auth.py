#!/usr/bin/env python3
"""Local Auth magic-link JWTs -> approved verifier -> HTTP -> isolated real DB.

Only this run's three uniquely named local Auth users and new DB are removed.
JWTs, OTP hashes, service credentials and session responses stay in memory.
The sole file fetched from Auth contains public JWKS, not credentials.
"""
from contextlib import contextmanager
import importlib.util
import json
import os
from pathlib import Path
import sys
import tomllib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import nyxis_local
spec = importlib.util.spec_from_file_location(
    'matrix', Path(__file__).with_name('check-local-db.py'))
matrix = importlib.util.module_from_spec(spec)
spec.loader.exec_module(matrix)


@contextmanager
def sessions():
    """Three fresh magic-link sessions on the fixed local Auth, plus its public ES256 JWKS."""
    with nyxis_local.auth_sessions(('alice', 'bob', 'root')) as created:
        jwks = nyxis_local.auth_request('GET', '/.well-known/jwks.json', key=os.environ['NYXIS_SUPABASE_ANON_KEY'])
        assert jwks['keys'] and all(key.get('kty') == 'EC' and key.get('alg') == 'ES256'
                                    and key.get('crv') == 'P-256' for key in jwks['keys']), 'ES256 JWKS required'
        yield ({name: info['access_token'] for name, info in created.items()},
               {name: info['id'] for name, info in created.items()}, jwks)


def main(work):
    config = tomllib.loads((matrix.db.ROOT / 'supabase/config.toml').read_text())
    issuer = config['auth'].get('jwt_issuer', 'http://127.0.0.1:55321/auth/v1')
    matrix.db.ENV['NYXIS_TEST_AUTH_ISSUER'] = issuer
    public_file = work / 'local-auth-jwks.json'
    try:
        with sessions() as (tokens, subjects, jwks):
            public_file.write_text(json.dumps(jwks))
            def verify():
                # Map only the fresh test DB's fixture rows to actual Auth subjects.
                # Roles remain application DB data, never a client/JWT admin claim.
                for name, uid in subjects.items():
                    matrix.db.sql('UPDATE public."User" SET "_nyxis_id" = ' + matrix.quote(uid)
                                  + ' WHERE "_nyxis_id" = ' + matrix.quote(name) + ';', matrix.db.DATABASE)
                author = json.dumps(['entity', [], 'User', subjects['alice']])
                matrix.db.sql('UPDATE public."Post" SET author = ' + matrix.quote(author) + ';', matrix.db.DATABASE)
                matrix.verify(tokens, subjects)

            matrix.db.main([str(work / 'check/.lake/build/bin/serveJwtHttp'), str(work),
                            str(matrix.db.PORT), 'local-auth'], verify)
    finally:
        public_file.unlink(missing_ok=True)
    print(f'Local Supabase Auth: 3 magic-link sessions, {matrix.db.checks} HTTP + '
          f'{matrix.checks} persistent-row checks passed; 3 test users removed '
          '(ES256/public JWKS/real clock/real DB; separate test launcher)')


if __name__ == '__main__':
    try:
        main(Path(sys.argv[1]))
    except Exception:
        raise SystemExit('local Auth integration failed (diagnostics withheld)')
