#!/usr/bin/env python3
"""External API calls (`@external` + `@effect("call …")`, sync) against a local mock HTTPS API and a real local DB.

Run after `lake build` via `python3 scripts/local-supabase.py --exec python3 scripts/check-external-calls.py`.
Starts a mock HTTPS API on 127.0.0.1 (throwaway self-signed certificate for `localhost`, trusted only by the
child through CURL_CA_BUNDLE), creates a uniquely named local database, runs the core executable
`checkExternalCalls` (Test/ExternalCalls.lean: provisions the test schema and drives the real staged
connection path `PostgresRun.handleStaged` for denied / 2xx / malformed / non-2xx / transport-failure calls),
then checks the mock's record of every request it received (authentication headers equal to the configured
secrets, JSON bodies made of the declared columns and proposed values only, no body on GET, no request for
denied calls), that the secrets never appear in the executable's output or in the database, and the rows the
run left behind. Drops only the database it created. Credentials and secrets are never printed.
"""
import http.server
import json
import os
from pathlib import Path
import ssl
import subprocess
import sys
import time
from urllib.parse import urlsplit, urlunsplit
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local

DATABASE = 'nyxis_external_test_' + uuid.uuid4().hex
ENV = nyxis_local.scrub_docker_env(os.environ.copy())
PAY_SECRET = 'pay-' + uuid.uuid4().hex
MAPS_SECRET = 'maps-' + uuid.uuid4().hex
BINARY = ROOT / '.lake/build/bin/checkExternalCalls'
checks = 0

CHARGE_BODY = {'amount': 1200, 'note': 'first', 'currency': 'jpy'}
# (method, path, authentication, body) in the order Test/ExternalCalls.lean issues them. Denied calls
# (other user / anonymous / currency usd / absent order / http:// endpoint) must not appear.
EXPECTED = (
    [('POST', '/pay/v1/charges/o-ok', 'bearer', CHARGE_BODY),
     ('POST', '/pay/v1/charges/o-extra', 'bearer', CHARGE_BODY)]
    + [('POST', '/pay/v1/charges/' + o, 'bearer', CHARGE_BODY)
       for o in ('o-missing', 'o-wrong', 'o-nested', 'o-text', 'o-402', 'o-500', 'o-slow', 'o-large')]
    + [('GET', '/pay/v1/charges/o-ok', 'bearer', None),
       ('GET', '/maps/geocode/o-ok', 'header', None),
       ('POST', '/hooks/a', 'none', {'note': 'first'})])

RESPONSES = {
    'o-ok': (200, b'{"id":"ch_1","status":"succeeded"}'),
    'o-extra': (200, b'{"id":"ch_2","status":"succeeded","extra":[1,2],"meta":{"n":5,"z":"drop"}}'),
    'o-missing': (200, b'{"id":"ch_3"}'),
    'o-wrong': (200, b'{"id":"ch_4","status":7}'),
    'o-nested': (200, b'{"id":"ch_5","status":"succeeded","meta":{"n":"x"}}'),
    'o-text': (200, b'not json'),
    'o-402': (402, b'{"error":"insufficient"}'),
    'o-500': (500, b'oops'),
    'o-large': (200, b'{"id":"' + b'x' * 70000 + b'","status":"succeeded"}'),
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


def make_handler(record):
    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.1'

        def log_message(self, *args):
            pass

        def authentication(self):
            authorization = self.headers.get('Authorization')
            api_key = self.headers.get('X-API-Key')
            if authorization is not None and api_key is None:
                return 'bearer' if authorization == 'Bearer ' + PAY_SECRET else 'bearer-mismatch'
            if api_key is not None and authorization is None:
                return 'header' if api_key == MAPS_SECRET else 'header-mismatch'
            if authorization is None and api_key is None:
                return 'none'
            return 'both'

        def body(self):
            length = self.headers.get('Content-Length')
            if length is None:
                return None
            raw = self.rfile.read(int(length))
            if self.command == 'POST' and self.headers.get('Content-Type') != 'application/json':
                return 'content-type:' + str(self.headers.get('Content-Type'))
            try:
                return json.loads(raw.decode())
            except ValueError:
                return 'unparsable'

        def respond(self, status, body, *, chunked=False):
            try:
                self.send_response(status)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError, ssl.SSLError):
                pass

        def handle_request(self):
            body = self.body()
            record.append((self.command, self.path, self.authentication(), body,
                           self.headers.get('Cookie') is None and '?' not in self.path))
            name = self.path.rsplit('/', 1)[-1]
            if self.command == 'POST' and self.path.startswith('/pay/v1/charges/'):
                if name == 'o-slow':
                    time.sleep(6)  # beyond the effect's `sync 2s`
                    return self.respond(200, b'{"id":"late","status":"succeeded"}')
                status, payload = RESPONSES.get(name, (404, b'{"error":"unknown"}'))
                return self.respond(status, payload)
            if self.command == 'GET' and self.path == '/pay/v1/charges/o-ok':
                return self.respond(200, b'{"status":"paid","amount":1}')
            if self.command == 'GET' and self.path == '/maps/geocode/o-ok':
                return self.respond(200, b'{"lat":35,"tags":["b","a"],"ok":true,"extra":{"x":1}}')
            if self.command == 'POST' and self.path == '/hooks/a':
                return self.respond(200, b'{"ok":true,"id":9}')
            return self.respond(404, b'{"error":"unknown"}')

        do_GET = handle_request
        do_POST = handle_request
        do_PUT = handle_request
        do_PATCH = handle_request
        do_DELETE = handle_request

    return Handler


def main():
    endpoint = urlsplit(os.environ.get('NYXIS_DATABASE_URL', ''))
    assert endpoint.scheme in ('postgres', 'postgresql'), 'local DB URL required'
    assert endpoint.hostname in ('127.0.0.1', 'localhost', '::1'), 'local DB required'
    assert endpoint.port == 55322 and endpoint.path == '/postgres', 'nyxis local DB required'
    assert not endpoint.query and not endpoint.fragment, 'unexpected DB URL options'
    nyxis_local.require_local_docker(ENV)
    assert BINARY.exists(), 'run lake build first'
    record = []
    with nyxis_local.tls_material('nyxis-external-calls-') as (cert, key), \
            nyxis_local.tls_server(make_handler(record), cert, key) as server:
        env = ENV.copy()
        env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + DATABASE))
        env['NYXIS_CHECK_EXTERNAL_PORT'] = str(server.server_port)
        env['NYXIS_EXT_PAY'] = PAY_SECRET
        env['NYXIS_EXT_MAPS'] = MAPS_SECRET
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            env.pop(name, None)
        env['CURL_CA_BUNDLE'] = str(cert)  # test child only; no runtime parameter is introduced
        created = False
        try:
            sql('CREATE DATABASE "' + DATABASE + '";')
            created = True
            result = subprocess.run([str(BINARY)], env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
            output = result.stdout.decode(errors='replace')
            errors = result.stderr.decode(errors='replace')
            summary = output.strip().splitlines()[-1] if output.strip() else ''
            if result.returncode or not summary.startswith('check-external-calls: '):
                tail = errors.strip().splitlines()[-1:] if errors.strip() else []
                raise RuntimeError('checkExternalCalls failed: ' + (
                    tail[0] if tail and tail[0].startswith('check-external-calls') else '(diagnostics withheld)'))
            lean_checks = int(summary.split()[1])
            expect(lean_checks >= 40, 'unexpectedly few Lean checks')
            # The secrets never reach the executable's output (responses, check names, exception texts).
            expect(PAY_SECRET not in output and MAPS_SECRET not in output, 'secret in stdout')
            expect(PAY_SECRET not in errors and MAPS_SECRET not in errors, 'secret in stderr')
            # The mock saw exactly the permitted calls, in order, each with the configured authentication header
            # and a body made of the declared columns and the proposed values only (none on GET).
            seen = [(m, p, a, b) for (m, p, a, b, clean) in record]
            expect(seen == EXPECTED, 'recorded requests differ from the expected sequence: ' + json.dumps(seen))
            expect(all(clean for (*_, clean) in record), 'a request carried a Cookie or a query string')
            # Rows left behind: the successful charge was marked, malformed and failed responses were rolled back,
            # the non-2xx response kept the update made before the call. No secret is stored anywhere.
            statuses = sql('''SELECT string_agg("_nyxis_id" || '=' || (status #>> '{1}'), ',' ORDER BY "_nyxis_id")
                              FROM public."Order";''', DATABASE)
            expect(statuses == ('o-402=charging,o-500=new,o-bob=new,o-extra=charged,o-hook=new,o-large=new,o-missing=new,'
                                'o-nested=new,o-ok=charged,o-plain=new,o-slow=new,o-text=new,o-wrong=new'),
                   'order statuses: ' + statuses)
            dump = sql('SELECT string_agg(to_jsonb(o)::text, \',\') FROM public."Order" o;', DATABASE)
            expect(PAY_SECRET not in dump and MAPS_SECRET not in dump, 'secret stored in the database')
            # The schema tables plus nyxis's reserved outbox (created with every schema, empty here: no async call).
            tables = sql('''SELECT string_agg(table_name, ',' ORDER BY table_name COLLATE "C")
                            FROM information_schema.tables WHERE table_schema = 'public';''', DATABASE)
            expect(tables == 'Order,User,_nyxis_outbox', 'unexpected tables: ' + tables)
            expect(sql('SELECT count(*) FROM public."_nyxis_outbox";', DATABASE) == '0', 'sync calls must not enqueue')
            print(summary)
            print(f'check-external-calls: {lean_checks} Lean checks, {len(record)} recorded mock requests and '
                  f'{checks} script checks passed (real local DB; mock HTTPS API)')
        finally:
            if created:
                sql('DROP DATABASE "' + DATABASE + '";')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-external-calls interrupted (cleanup attempted)')
    except Exception as error:
        message = str(error) if isinstance(error, (AssertionError, RuntimeError)) else '(diagnostics withheld)'
        raise SystemExit('check-external-calls failed: ' + message)
