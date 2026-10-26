#!/usr/bin/env python3
"""The outbox for `async` external API calls (`_nyxis_outbox` + the internal delivery loop) against a real
local DB and a local mock HTTPS API.

Run after `lake build` via `python3 scripts/local-supabase.py --exec python3 scripts/check-outbox.py`.
Creates a uniquely named local database and starts a mock HTTPS API (throwaway self-signed certificate for
`localhost`, trusted only by the children through CURL_CA_BUNDLE), then drives the core executable
`checkOutbox` (Test/Outbox.lean) in three shapes:

1. `provision`   — the test schema and the reserved table `_nyxis_outbox` are created; the script then installs a
                   deferred constraint trigger that makes the COMMIT of any update to `status = "boom"` fail.
2. `enqueue`     — the real staged connection path records permitted `async` calls in the same transaction as the
                   request. The script checks that nothing was sent, that every expected row is `pending` with
                   attempts 0 and the declared body, that one request with two async calls left two rows
                   (`<request id>-0` / `-1`), that denied calls and the request whose COMMIT failed left no row, and
                   that the destination secret is stored nowhere.
3. `loop` x 2    — two processes run nyxis's internal loop against the same database at the same time (interval 1 s,
                   backoff base 1 s, at most 3 attempts). The mock answers 5xx twice then 2xx for one row (resent and
                   `sent`), 4xx for one row (immediately `failed`), 5xx always for one row (`failed` after the
                   maximum attempts), 2xx for the rest, with a small delay so the two loops overlap. The script
                   checks the rows' final states and counters, that the mock saw every row exactly once per attempt
                   (no double delivery across the two processes), that the authentication header and bodies are the
                   stored ones, and that the processes' counts add up to the mock's record.

Drops only the database it created. Credentials and secrets are never printed.
"""
import http.server
import json
import os
from pathlib import Path
import re
import ssl
import subprocess
import sys
import threading
import time
from urllib.parse import urlsplit, urlunsplit
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local

DATABASE = 'nyxis_outbox_test_' + uuid.uuid4().hex
ENV = nyxis_local.scrub_docker_env(os.environ.copy())
NOTIFY_SECRET = 'notify-' + uuid.uuid4().hex
BINARY = ROOT / '.lake/build/bin/checkOutbox'
PARALLEL = ['o-par%d' % i for i in range(12)]
NOTIFY_BODY = {'amount': 1200, 'note': 'first'}
LOOP_SECONDS = 14
BACKOFF_BASE = 1  # seconds; the loop retries after BACKOFF_BASE * 2^attempts
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


def expect(condition, what):
    global checks
    assert condition, what
    checks += 1


def make_handler(record, lock):
    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.1'

        def log_message(self, *args):
            pass

        def authentication(self):
            authorization = self.headers.get('Authorization')
            if authorization is None:
                return 'none'
            return 'bearer' if authorization == 'Bearer ' + NOTIFY_SECRET else 'bearer-mismatch'

        def body(self):
            length = self.headers.get('Content-Length')
            if length is None:
                return None
            raw = self.rfile.read(int(length))
            if self.headers.get('Content-Type') != 'application/json':
                return 'content-type:' + str(self.headers.get('Content-Type'))
            try:
                return json.loads(raw.decode())
            except ValueError:
                return 'unparsable'

        def respond(self, status, body):
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
            with lock:
                record.append((self.command, self.path, self.authentication(), body,
                               self.headers.get('Cookie') is None and '?' not in self.path, time.monotonic()))
                earlier = sum(1 for (_, p, *_) in record if p == self.path)  # including this one
            name = self.path.rsplit('/', 1)[-1]
            if self.command == 'POST' and self.path.startswith('/notify/v1/events/'):
                if name == 'o-retry':
                    return self.respond(500 if earlier <= 2 else 200, b'{"ok":true}')
                if name == 'o-404':
                    return self.respond(404, b'{"error":"unknown event"}')
                if name == 'o-max':
                    return self.respond(503, b'{"error":"down"}')
                if name.startswith('o-par'):
                    time.sleep(0.3)  # let the two loops overlap on the parallel rows
                return self.respond(200, b'{"ok":true}')
            if self.command == 'POST' and self.path == '/hooks/o-hook':
                return self.respond(204, b'')
            return self.respond(404, b'{"error":"unknown"}')

        do_GET = handle_request
        do_POST = handle_request
        do_PUT = handle_request
        do_PATCH = handle_request
        do_DELETE = handle_request

    return Handler


def run_binary(mode, env, timeout):
    result = subprocess.run([str(BINARY), mode], env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=timeout)
    output = result.stdout.decode(errors='replace')
    errors = result.stderr.decode(errors='replace')
    summary = output.strip().splitlines()[-1] if output.strip() else ''
    if result.returncode or not summary.startswith('check-outbox: '):
        tail = errors.strip().splitlines()[-1:] if errors.strip() else []
        raise RuntimeError('checkOutbox %s failed: %s' % (
            mode, tail[0] if tail and tail[0].startswith('check-outbox') else '(diagnostics withheld)'))
    expect(NOTIFY_SECRET not in output and NOTIFY_SECRET not in errors, 'secret in the output of ' + mode)
    return summary


def rows():
    """(id, target, destination, method, url, body, state, attempts, last_status, last_error, sent_at?) per row."""
    text = sql('''SELECT json_agg(json_build_object('id', "_nyxis_id", 'principal', principal, 'action', action,
                    'target', target, 'destination', destination, 'method', method, 'url', url, 'body', body,
                    'state', state, 'attempts', attempts, 'last_status', last_status, 'last_error', last_error,
                    'sent', sent_at IS NOT NULL, 'due', next_at <= now()) ORDER BY "_nyxis_id")
                  FROM public."_nyxis_outbox";''', DATABASE)
    return json.loads(text) if text else []


def by_target(all_rows):
    grouped = {}
    for row in all_rows:
        grouped.setdefault(row['target'], []).append(row)
    return grouped


def main():
    endpoint = urlsplit(os.environ.get('NYXIS_DATABASE_URL', ''))
    assert endpoint.scheme in ('postgres', 'postgresql'), 'local DB URL required'
    assert endpoint.hostname in ('127.0.0.1', 'localhost', '::1'), 'local DB required'
    assert endpoint.port == 55322 and endpoint.path == '/postgres', 'nyxis local DB required'
    assert not endpoint.query and not endpoint.fragment, 'unexpected DB URL options'
    context = subprocess.run(['docker', 'context', 'inspect', 'desktop-linux'], env=ENV,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    assert context.returncode == 0, 'Docker context unavailable'
    assert json.loads(context.stdout)[0]['Endpoints']['docker']['Host'].startswith('unix:///'), 'local Docker required'
    assert BINARY.exists(), 'run lake build first'
    record = []
    lock = threading.Lock()
    with nyxis_local.tls_material('nyxis-outbox-') as (cert, key), \
            nyxis_local.tls_server(make_handler(record, lock), cert, key) as server:
        env = ENV.copy()
        env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + DATABASE))
        env['NYXIS_CHECK_EXTERNAL_PORT'] = str(server.server_port)
        env['NYXIS_EXT_NOTIFY'] = NOTIFY_SECRET
        env['NYXIS_OUTBOX_INTERVAL_SECONDS'] = '1'
        env['NYXIS_OUTBOX_MAX_ATTEMPTS'] = '3'
        env['NYXIS_OUTBOX_BACKOFF_BASE_SECONDS'] = str(BACKOFF_BASE)
        env['NYXIS_CHECK_OUTBOX_SECONDS'] = str(LOOP_SECONDS)
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            env.pop(name, None)
        env['CURL_CA_BUNDLE'] = str(cert)  # test children only; no runtime parameter is introduced
        base = 'https://localhost:%d' % server.server_port
        created = False
        try:
            sql('CREATE DATABASE "' + DATABASE + '";')
            created = True
            # 1. provision: the schema tables and the reserved outbox, then the COMMIT-failure trigger.
            print(run_binary('provision', env, 120))
            tables = sql('''SELECT string_agg(table_name, ',' ORDER BY table_name COLLATE "C")
                            FROM information_schema.tables WHERE table_schema = 'public';''', DATABASE)
            expect(tables == 'Order,User,_nyxis_outbox', 'unexpected tables: ' + tables)
            sql('''CREATE FUNCTION public.nyxis_test_boom() RETURNS trigger LANGUAGE plpgsql AS $$
                   BEGIN
                     IF NEW.status = '["string","boom"]'::jsonb THEN
                       RAISE EXCEPTION 'injected commit failure';
                     END IF;
                     RETURN NULL;
                   END $$;
                   CREATE CONSTRAINT TRIGGER nyxis_test_boom AFTER UPDATE ON public."Order"
                     DEFERRABLE INITIALLY DEFERRED FOR EACH ROW EXECUTE FUNCTION public.nyxis_test_boom();''',
                DATABASE)
            # 2. enqueue: permitted async calls are recorded in the request's transaction and nothing is sent.
            summary = run_binary('enqueue', env, 300)
            print(summary)
            expect(int(summary.split()[1]) >= 40, 'unexpectedly few Lean checks')
            expect(record == [], 'an async call was sent during the request: ' + json.dumps(record))
            pending = rows()
            grouped = by_target(pending)
            expected_targets = {'Order/' + o for o in ['o-ok', 'o-404', 'o-retry', 'o-max', 'o-hook', 'o-dead'] + PARALLEL}
            expect(set(grouped) == expected_targets | {'Order/o-twice'},
                   'unexpected outbox targets: ' + json.dumps(sorted(grouped)))
            expect(all(len(grouped[t]) == 1 for t in expected_targets) and len(grouped['Order/o-twice']) == 2,
                   'unexpected number of rows per target')
            twice = ','.join(r['id'] for r in grouped['Order/o-twice'])
            expect(re.fullmatch(r'(req-\d+)-0,\1-1', twice) is not None, 'two async calls in one request: ' + twice)
            for row in pending:
                expect(row['state'] == 'pending' and row['attempts'] == 0 and row['last_status'] is None
                       and row['last_error'] is None and not row['sent'] and row['due'], 'fresh row: ' + json.dumps(row))
                expect(row['principal'] == 'User::"alice"', 'principal column: ' + row['principal'])
                if row['target'] == 'Order/o-hook':
                    expect(row['action'] == 'pingHook' and row['destination'] == 'Hook' and row['method'] == 'POST'
                           and row['url'] == base + '/hooks/o-hook' and row['body'] == {'note': 'first'},
                           'hook row: ' + json.dumps(row))
                elif row['target'] == 'Order/o-dead':
                    # `url: 列` pointing at a closed port: every attempt is a transport failure.
                    expect(row['action'] == 'pingHook' and row['destination'] == 'Hook' and row['method'] == 'POST'
                           and row['url'] == 'https://localhost:1/dead' and row['body'] == {'note': 'first'},
                           'dead hook row: ' + json.dumps(row))
                else:
                    name = row['target'].split('/')[1]
                    expect(row['action'] == 'notifyOrder' and row['destination'] == 'Notify' and row['method'] == 'POST'
                           and row['url'] == base + '/notify/v1/events/' + name and row['body'] == NOTIFY_BODY,
                           'notify row: ' + json.dumps(row))
            expect(all(r['id'].startswith('req-') and r['id'].endswith(('-0', '-1')) for r in pending),
                   'row ids are <request id>-<stage>')
            statuses = sql('''SELECT string_agg("_nyxis_id" || '=' || (status #>> '{1}'), ',' ORDER BY "_nyxis_id" COLLATE "C")
                              FROM public."Order";''', DATABASE)
            expected_statuses = ','.join(name + '=' + status for name, status in sorted(
                [('o-ok', 'noted'), ('o-twice', 'new'), ('o-boom', 'new'), ('o-404', 'new'), ('o-retry', 'new'),
                 ('o-max', 'new'), ('o-hook', 'new'), ('o-dead', 'new')] + [(o, 'new') for o in PARALLEL]))
            expect(statuses == expected_statuses, 'order statuses: ' + statuses)
            # 3. two internal loops at once against the same database.
            started = time.monotonic()
            loops = [subprocess.Popen([str(BINARY), 'loop'], env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                     for _ in range(2)]
            counts = []
            for proc in loops:
                out, err = proc.communicate(timeout=LOOP_SECONDS + 120)
                out, err = out.decode(errors='replace'), err.decode(errors='replace')
                expect(proc.returncode == 0 and out.strip().startswith('check-outbox: loop processed '),
                       'loop process failed')
                expect(NOTIFY_SECRET not in out and NOTIFY_SECRET not in err, 'secret in the output of loop')
                counts.append(int(out.strip().split()[3]))
            processed = sum(counts)
            elapsed = time.monotonic() - started
            print('check-outbox: two loop processes ran for %.1f s and processed %s rows' % (elapsed, ' + '.join(map(str, counts))))
            # Both instances took part (the parallel rows are delayed so the loops overlap on them).
            expect(all(count >= 1 for count in counts), 'one loop process processed nothing: %s' % counts)
            final = rows()
            grouped = by_target(final)
            expect(len(final) == len(pending) and {r['id'] for r in final} == {r['id'] for r in pending},
                   'the loop must not add or remove rows')
            expect(all(r['state'] != 'pending' for r in final), 'rows still pending: ' + json.dumps(
                [r['id'] for r in final if r['state'] == 'pending']))
            for target, expected in [('Order/o-retry', ('sent', 3, 200, None)), ('Order/o-404', ('failed', 1, 404, 'status')),
                                     ('Order/o-max', ('failed', 3, 503, 'attempts')), ('Order/o-ok', ('sent', 1, 200, None)),
                                     ('Order/o-hook', ('sent', 1, 204, None)), ('Order/o-dead', ('failed', 3, None, 'attempts'))] + \
                    [('Order/' + o, ('sent', 1, 200, None)) for o in PARALLEL]:
                (row,) = grouped[target]
                expect((row['state'], row['attempts'], row['last_status'], row['last_error']) == expected
                       and row['sent'] == (expected[0] == 'sent'), 'final row %s: %s' % (target, json.dumps(row)))
            for row in grouped['Order/o-twice']:
                expect((row['state'], row['attempts'], row['last_status'], row['last_error'], row['sent'])
                       == ('sent', 1, 200, None, True), 'final row o-twice: ' + json.dumps(row))
            # The mock saw every pending row exactly once per attempt: no double delivery across the two processes,
            # the 5xx row three times (two failures, one success), the 4xx row once, the always-5xx row three times.
            seen = {}
            times = {}
            for (method, path, auth, body, clean, at) in record:
                seen[path] = seen.get(path, 0) + 1
                times.setdefault(path, []).append(at)
                expect(method == 'POST' and clean, 'request shape: ' + path)
                if path == '/hooks/o-hook':
                    expect(auth == 'none' and body == {'note': 'first'}, 'hook request: ' + json.dumps(body))
                else:
                    expect(auth == 'bearer' and body == NOTIFY_BODY, 'notify request: %s %s %s' % (path, auth, json.dumps(body)))
            expected_seen = {'/notify/v1/events/' + o: 1 for o in ['o-ok'] + PARALLEL}
            expected_seen.update({'/notify/v1/events/o-twice': 2, '/notify/v1/events/o-retry': 3,
                                  '/notify/v1/events/o-404': 1, '/notify/v1/events/o-max': 3, '/hooks/o-hook': 1})
            expect(seen == expected_seen, 'deliveries per path: ' + json.dumps(seen))
            # Exponential backoff: the retries of the 5xx rows came no sooner than base * 2^1 and base * 2^2 seconds
            # after the previous attempt (the loop's interval only adds to the gap).
            for path in ('/notify/v1/events/o-retry', '/notify/v1/events/o-max'):
                gaps = [b - a for a, b in zip(times[path], times[path][1:])]
                expect(len(gaps) == 2 and gaps[0] >= BACKOFF_BASE * 2 - 0.1 and gaps[1] >= BACKOFF_BASE * 4 - 0.1,
                       'backoff gaps for %s: %s' % (path, ['%.2f' % g for g in gaps]))
            # The dead hook (transport failures) was retried up to the maximum and counted by the loops, not by the mock.
            expect(processed == len(record) + 3, 'the two loops processed %d rows but the mock saw %d requests'
                   % (processed, len(record)))
            dump = sql('SELECT string_agg(to_jsonb(o)::text, \',\') FROM public."_nyxis_outbox" o;', DATABASE)
            expect(NOTIFY_SECRET not in dump, 'secret stored in the outbox')
            print('check-outbox: %d recorded mock requests and %d script checks passed (real local DB; mock HTTPS API; '
                  '2 loop processes)' % (len(record), checks))
        finally:
            if created:
                sql('DROP DATABASE "' + DATABASE + '" WITH (FORCE);')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-outbox interrupted (cleanup attempted)')
    except Exception as error:
        message = str(error) if isinstance(error, (AssertionError, RuntimeError)) else '(diagnostics withheld)'
        raise SystemExit('check-outbox failed: ' + message)
