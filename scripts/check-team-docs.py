#!/usr/bin/env python3
"""team-docs sample -> actual Supabase Auth sessions -> HTTPS JWKS relay -> isolated local DB.

Integration test of the second official sample (examples/team-docs/backend) on the local
Supabase: six Auth-issued sessions (owner / editor / viewer / multi-org member / outsider /
individually shared guest) plus anonymous and forged bearers exercise document listing,
reading, creation, editing, deletion, sharing and membership changes, org membership
represented as membership rows (Membership: user / team / org; the user's entity ancestors are
derived from its membership rows, so `principal in resource.org` and `principal in
resource.org.editors` are judged from rows of another table) and individual sharing,
server-generated keys and timestamps and query-string
listing with JSON responses, list filtering / ordering / paging / counts over permitted
rows only and uniqueness / referential integrity with judged cascades (409 on duplicate
titles and org names, 409 deleting a user who created documents, org deletion cascading to
documents only when every document's deleteDoc is permitted, DB-side UNIQUE / FOREIGN KEY
constraints present as the backstop) and attachments (signed upload / download URLs are
issued only to subjects the policy permits, denied subjects get 403 and no request reaches
Storage, the issued URLs upload to and download from the local Supabase Storage, a signed URL
cannot reach another object, the bucket is private) and notifications (sharing a document
creates a notification row per subscriber and sends mail — a declared external effect judged by the
policy — only to subscribers who can read the document now; denied sends do not happen and leave the
row unsent; the periodic job runs as the service principal (configured, not a JWT) and sends a pending
notification once its recipient can read the document; a JWT whose subject equals the configured
service id is still a User and cannot act as the service) and external API calls (the sample's
Cedar schema declares two `@external` destinations on a local mock HTTPS API — this script starts it on
the fixed port the schema names, with a throwaway certificate trusted only by the sample through
CURL_CA_BUNDLE. `POST /docs/{id}/summary` is a `sync` call: only owners / editors get it, nyxis sends
the declared columns with the configured bearer key, the decoded response is written to the `summary`
column only through a second judged action (`recordSummary`: an empty summary is denied although the
call was sent), a non-2xx answer reaches the handler and is mapped to 424; denied subjects get 403 and
no request reaches the mock. `PATCH /docs/{id}` adds an `async` call: every permitted edit leaves exactly
one `_nyxis_outbox` row written in the request's transaction, nyxis's internal loop delivers it to the
mock after COMMIT, denied edits leave none, and the secrets are stored nowhere). Mail goes through the sample's approved
curl to the local Mailpit SMTP port and is observed through Mailpit's HTTP API. The sample reaches
Storage only through the same HTTPS relay as the JWKS (local Storage speaks plain HTTP); the relay
checks that the sample sends the service_role key and only requests under the test bucket. Only this
run's new DB, Auth users and Storage bucket are created and removed (mail to this run's unique
addresses stays in Mailpit). No real project is contacted. Run after `lake build` in
examples/team-docs/backend via python3 scripts/local-supabase.py --exec python3 <this script>.
"""
from contextlib import ExitStack
import http.client
import http.server
import json
import os
from pathlib import Path
import ssl
import subprocess
import sys
import threading
import time
import tomllib
from urllib.parse import urlsplit, urlunsplit
import uuid

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local

BACKEND = ROOT / 'examples/team-docs/backend'
PORT = int(os.environ.get('NYXIS_TEAM_DOCS_PORT', '18117'))
DATABASE = 'nyxis_team_docs_test_' + uuid.uuid4().hex
BUCKET = 'nyxis-team-docs-' + uuid.uuid4().hex[:12]
RELAY = 'https://localhost:55325'
MAILPIT = 'http://127.0.0.1:55324'
SMTP = 'smtp://127.0.0.1:55326'
MAIL_FROM = 'nyxis-team-docs@example.com'
JOB_INTERVAL = 2
# The mock external API. The schema's `@external` destinations name this fixed port, like the JWKS relay's 55325.
MOCK_PORT = 18118
MOCK = 'https://localhost:%d' % MOCK_PORT
SUMMARIZER_SECRET = 'summarizer-' + uuid.uuid4().hex
AUDIT_SECRET = 'audit-' + uuid.uuid4().hex
OUTBOX_INTERVAL = 1
ENV = nyxis_local.scrub_docker_env(os.environ.copy())
NAMES = ('owner', 'editor', 'viewer', 'multi', 'outsider', 'guest')
checks = 0
row_checks = 0
edits_announced = 0  # permitted document edits (204): each must leave exactly one outbox row for the audit API
storage_trace = []   # (path, authorization is the service key) per signing request the sample sent
mock_record = []     # (method, path, authentication, body, clean) per request the mock external API received
mock_lock = threading.Lock()


def summary_of(title, text):
    """What the mock summarizer answers for a document (the test's own formula)."""
    return '' if not text.strip() else title + ': ' + text[:24]


def make_mock():
    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.1'

        def log_message(self, *args):
            pass

        def authentication(self):
            authorization = self.headers.get('Authorization')
            if authorization is None:
                return 'none'
            if authorization == 'Bearer ' + SUMMARIZER_SECRET:
                return 'summarizer'
            if authorization == 'Bearer ' + AUDIT_SECRET:
                return 'audit'
            return 'mismatch'

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
            with mock_lock:
                mock_record.append((self.command, self.path, self.authentication(), body,
                                    self.headers.get('Cookie') is None and '?' not in self.path))
            if self.command == 'POST' and self.path.startswith('/summarizer/v1/summaries/') and isinstance(body, dict):
                text = body.get('body', '')
                if 'reject' in text:
                    return self.respond(422, b'{"error":"unsupported language"}')
                answer = {'summary': summary_of(body.get('title', ''), text), 'model': 'mock-1'}  # `model` is undeclared: dropped
                return self.respond(200, json.dumps(answer).encode())
            if self.command == 'POST' and self.path.startswith('/audit/v1/docs/') and self.path.endswith('/updated'):
                return self.respond(202, b'{"accepted":true}')
            return self.respond(404, b'{"error":"unknown"}')

        do_GET = handle_request
        do_POST = handle_request
        do_PUT = handle_request
        do_PATCH = handle_request
        do_DELETE = handle_request

    return Handler


def mock_requests(prefix):
    with mock_lock:
        return [r for r in mock_record if r[1].startswith(prefix)]


def outbox_rows():
    """nyxis's reserved outbox, oldest first."""
    text = sql('''SELECT json_agg(json_build_object('id', "_nyxis_id", 'principal', principal, 'action', action, 'target', target,
                    'destination', destination, 'method', method, 'url', url, 'body', body, 'state', state, 'attempts', attempts,
                    'last_status', last_status, 'last_error', last_error, 'sent', sent_at IS NOT NULL)
                    ORDER BY created_at, "_nyxis_id")
                  FROM public."_nyxis_outbox";''', DATABASE)
    return json.loads(text) if text else []


def settled_outbox(expected_rows, seconds=20):
    """Wait until the outbox holds `expected_rows` rows and none is pending (the loop runs every OUTBOX_INTERVAL s)."""
    deadline = time.time() + seconds
    rows = outbox_rows()
    while time.time() < deadline and (len(rows) < expected_rows or any(r['state'] == 'pending' for r in rows)):
        time.sleep(0.5)
        rows = outbox_rows()
    return rows


def raw_storage(method, path_and_query, body=None, headers=None):
    """A request to the local Storage without credentials (what a client does with a signed URL)."""
    conn = http.client.HTTPConnection('127.0.0.1', 55321, timeout=10)
    try:
        conn.request(method, path_and_query, body, headers or {})
        res = conn.getresponse()
        return res.status, res.read()
    finally:
        conn.close()


def mailpit(path):
    """One GET to Mailpit's HTTP API (the mail capture of the local Supabase)."""
    conn = http.client.HTTPConnection('127.0.0.1', 55324, timeout=10)
    try:
        conn.request('GET', path)
        res = conn.getresponse()
        assert res.status == 200, ('Mailpit API', path, res.status)
        return json.loads(res.read())
    finally:
        conn.close()


def mails_to(address):
    """The captured messages addressed to `address` (subject, text, from) in delivery order."""
    found = mailpit('/api/v1/search?query=' + 'to:' + address)
    out = []
    for summary in found['messages']:
        message = mailpit('/api/v1/message/' + summary['ID'])
        assert [t['Address'] for t in message['To']] == [address], message['To']
        out.append((message['Subject'], message['Text'], message['From']['Address']))
    return out[::-1]


def local_url(signed):
    """Rewrite the relay URL nyxis returned into a plain-HTTP local Storage path (the client's side)."""
    assert signed.startswith(RELAY + '/storage/v1/'), signed
    return signed[len(RELAY):]


def sql(statement, database='postgres'):
    result = subprocess.run(
        ['docker', '--context', ENV['DOCKER_CONTEXT'], 'exec', '-i', 'supabase_db_nyxis',
         'psql', '-X', '-U', 'postgres', '-d', database, '-At', '-v', 'ON_ERROR_STOP=1'],
        input=statement.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=ENV, timeout=30)
    if result.returncode:
        raise RuntimeError('local test SQL failed (diagnostics withheld)')
    return result.stdout.decode().strip()


def snapshot():
    return sql('''SELECT jsonb_build_object(
        'users', (SELECT jsonb_agg(to_jsonb(u) ORDER BY "_nyxis_id") FROM public."User" u),
        'orgs', (SELECT jsonb_agg(to_jsonb(o) ORDER BY "_nyxis_id") FROM public."Org" o),
        'teams', (SELECT jsonb_agg(to_jsonb(t) ORDER BY "_nyxis_id") FROM public."Team" t),
        'memberships', (SELECT jsonb_agg(to_jsonb(m) ORDER BY "_nyxis_id") FROM public."Membership" m),
        'docs', (SELECT jsonb_agg(to_jsonb(d) ORDER BY "_nyxis_id") FROM public."Doc" d),
        'subscriptions', (SELECT jsonb_agg(to_jsonb(s) ORDER BY "_nyxis_id") FROM public."Subscription" s),
        'notifications', (SELECT jsonb_agg(to_jsonb(n) ORDER BY "_nyxis_id") FROM public."Notification" n));''', DATABASE)


def count(table, where=''):
    return int(sql('SELECT count(*) FROM public."%s"%s;' % (table, (' WHERE ' + where) if where else ''), DATABASE))


def request(method, path, data=None, headers=None):
    conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
    try:
        conn.request(method, path, None if data is None else json.dumps(data), headers or {})
        res = conn.getresponse()
        return res.status, res.read().decode(), {k.lower(): v for k, v in res.getheaders()}
    finally:
        conn.close()


def now_ms():
    return int(time.time() * 1000)


class Client:
    """Requests as one subject; denied and malformed requests must leave the DB unchanged."""

    def __init__(self, tokens):
        self.tokens = tokens

    def headers(self, subject):
        if subject is None:
            return {}
        if subject == 'forged':
            return {'Authorization': 'Bearer forged.' + 'x' * 40, 'Cookie': 'session=secret'}
        return {'Authorization': 'Bearer ' + self.tokens[subject]}

    def expect(self, subject, method, path, status, data=None, json_body=True):
        global checks, row_checks, edits_announced
        before = None
        if status in (400, 403, 404, 409) and method != 'GET':
            before = snapshot()
        got, body, headers = request(method, path, data, self.headers(subject))
        assert got == status, (subject, method, path, got, status)
        checks += 1
        if method == 'PATCH' and path.startswith('/docs/') and got == 204:
            edits_announced += 1
        if before is not None:
            assert snapshot() == before, (subject, method, path, 'denied request changed rows')
            row_checks += 1
        if status in (200, 201):
            assert headers.get('content-type') == 'application/json', (path, headers.get('content-type'))
            return json.loads(body) if json_body else body
        if status == 204:
            assert body == ''
        return body, headers

    def created(self, subject, path, data, collection):
        got, body, headers = request('POST', path, data, self.headers(subject))
        assert got == 201, (subject, path, got)
        assert headers.get('content-type') == 'application/json'
        key = json.loads(body)['id']
        assert headers.get('location') == collection + '/' + key, headers.get('location')
        global checks
        checks += 1
        return key


def is_uuid4(value):
    try:
        return uuid.UUID(value).version == 4 and str(uuid.UUID(value)) == value
    except ValueError:
        return False


def db_doc(key):
    raw = sql('SELECT to_jsonb(d)::text FROM public."Doc" d WHERE "_nyxis_id" = ' + quote(key) + ';', DATABASE)
    return json.loads(raw) if raw else None


def quote(value):
    return "'" + value.replace("'", "''") + "'"


def verify(c, ids, service_id):
    global checks, row_checks
    anon, forged = None, 'forged'
    subjects = NAMES + (anon, forged)

    # --- registration: each Auth subject creates only its own User row ---
    for name in NAMES:
        assert c.expect(name, 'POST', '/users/' + ids[name], 201, {'name': name.title()}) == {'id': ids[name]}
        assert c.expect(name, 'GET', '/users/' + ids[name], 200) == {'name': name.title()}
        c.expect(name, 'POST', '/users/' + ids[name], 409, {'name': 'again'})
    c.expect('editor', 'POST', '/users/' + ids['owner'], 403, {'name': 'x'})
    c.expect('editor', 'GET', '/users/' + ids['owner'], 403)
    c.expect('owner', 'POST', '/users/' + str(uuid.uuid4()), 403, {'name': 'x'})
    c.expect(anon, 'POST', '/users/' + ids['owner'], 403, {'name': 'x'})
    c.expect(forged, 'GET', '/users/' + ids['owner'], 403)
    c.expect('owner', 'POST', '/users/' + ids['owner'], 400, {'name': 1})
    print('users: registration/self-read/409/403/400 passed', flush=True)

    # --- organisations and membership rows ---
    acme = c.created('owner', '/orgs', {'name': 'Acme', 'owners': [ids['editor']], 'editors': 'x'}, '/orgs')
    assert is_uuid4(acme), 'org key is not a nyxis-generated UUID'
    org_row = c.expect('owner', 'GET', '/orgs/' + acme, 200)
    assert org_row == {'name': 'Acme', 'owners': [ids['owner']], 'editors': acme + '/editors', 'viewers': acme + '/viewers'}, org_row
    zen = c.created('outsider', '/orgs', {'name': 'Zen'}, '/orgs')
    solo = c.created('outsider', '/orgs', {'name': 'Solo'}, '/orgs')
    assert len({acme, zen, solo}) == 3, 'generated keys collide'
    # Creating an org inserts its two role teams in the same request (each judged by createTeam).
    assert count('Team') == 6 and count('Membership') == 0 and count('Org') == 3
    teams = sql("""SELECT string_agg("_nyxis_id" || ':' || ("role"->>1), ',' ORDER BY "_nyxis_id") FROM public."Team";""", DATABASE)
    assert teams == ','.join(sorted(o + '/editors:editor,' + o + '/viewers:viewer' for o in (acme, zen, solo))), teams
    row_checks += 2
    c.expect(anon, 'POST', '/orgs', 403, {'name': 'Anon'})
    c.expect(forged, 'POST', '/orgs', 403, {'name': 'Forged'})
    c.expect('owner', 'POST', '/orgs', 400, {})
    c.expect('editor', 'GET', '/orgs/' + acme, 403)
    c.expect('editor', 'POST', '/orgs/' + acme + '/members', 403, {'user': ids['editor'], 'role': 'editor'})
    mids = {}

    def add_member(subject, org, name, role):
        key = c.created(subject, '/orgs/' + org + '/members', {'user': ids[name], 'role': role}, '/memberships')
        assert is_uuid4(key), 'membership key is not a nyxis-generated UUID'
        mids[(org, name)] = key
        return key

    add_member('owner', acme, 'editor', 'editor')
    add_member('owner', acme, 'multi', 'editor')
    add_member('owner', acme, 'viewer', 'viewer')
    stored = json.loads(sql('SELECT to_jsonb(m)::text FROM public."Membership" m WHERE "_nyxis_id" = ' + quote(mids[(acme, 'viewer')]) + ';', DATABASE))
    assert stored['user'] == ['entity', [], 'User', ids['viewer']] and stored['team'] == ['entity', [], 'Team', acme + '/viewers']
    assert stored['org'] == ['entity', [], 'Org', acme], stored
    row_checks += 1
    c.expect('owner', 'POST', '/orgs/' + acme + '/members', 409, {'user': ids['editor'], 'role': 'editor'})   # unique (user, team)
    c.expect('owner', 'POST', '/orgs/' + acme + '/members', 400, {'user': ids['guest'], 'role': 'boss'})
    c.expect('owner', 'POST', '/orgs/' + acme + '/members', 400, {'user': ids['guest']})
    c.expect('owner', 'POST', '/orgs/' + acme + '/members', 400, {'user': 1, 'role': 'viewer'})
    c.expect('owner', 'PUT', '/orgs/' + acme + '/owners', 403, {'owners': [ids['editor']]})
    c.expect('owner', 'PUT', '/orgs/' + acme + '/owners', 400, {})
    c.expect('owner', 'PUT', '/orgs/' + acme + '/owners', 400, {'owners': 'x'})
    for subject in ('editor', 'viewer', 'multi', 'outsider', 'guest', anon, forged):
        c.expect(subject, 'POST', '/orgs/' + acme + '/members', 403, {'user': ids['guest'], 'role': 'viewer'})
        c.expect(subject, 'PUT', '/orgs/' + acme + '/owners', 403, {'owners': [ids['owner'], ids[subject] if subject in NAMES else ids['guest']]})
        c.expect(subject, 'DELETE', '/memberships/' + mids[(acme, 'viewer' if subject != 'viewer' else 'editor')], 403)   # not one's own row
    c.expect('owner', 'PUT', '/orgs/' + acme + '/owners', 204, {'owners': [ids['editor'], ids['owner']]})
    assert c.expect('owner', 'GET', '/orgs/' + acme, 200)['owners'] == sorted([ids['editor'], ids['owner']])
    # A second owner cannot remove itself either, but can manage memberships; the original owner restores the single owner.
    c.expect('editor', 'PUT', '/orgs/' + acme + '/owners', 403, {'owners': [ids['owner']]})
    temp = add_member('editor', acme, 'guest', 'viewer')
    c.expect('editor', 'DELETE', '/memberships/' + temp, 204)
    del mids[(acme, 'guest')]
    c.expect('owner', 'PUT', '/orgs/' + acme + '/owners', 204, {'owners': [ids['owner']]})
    c.expect('editor', 'POST', '/orgs/' + acme + '/members', 403, {'user': ids['guest'], 'role': 'viewer'})
    c.expect('editor', 'DELETE', '/memberships/' + mids[(acme, 'multi')], 403)
    add_member('outsider', zen, 'multi', 'viewer')
    c.expect('owner', 'POST', '/orgs/' + zen + '/members', 403, {'user': ids['owner'], 'role': 'viewer'})
    c.expect('owner', 'POST', '/orgs/' + str(uuid.uuid4()) + '/members', 403, {'user': ids['owner'], 'role': 'viewer'})
    c.expect('owner', 'DELETE', '/memberships/' + str(uuid.uuid4()), 403)
    assert count('Membership') == 4
    row_checks += 1
    for subject, expected in [('owner', {acme}), ('editor', {acme}), ('viewer', {acme}), ('multi', {acme, zen}),
                              ('outsider', {zen, solo}), ('guest', set()), (anon, set()), (forged, set())]:
        listing = c.expect(subject, 'GET', '/orgs', 200)
        assert {row['id'] for row in listing['rows']} == expected and listing['total'] == len(expected), (subject, listing)
    for subject in ('guest', anon, forged):
        c.expect(subject, 'GET', '/orgs/' + acme, 403)
    # Membership rows of an org are listed (filtered by org) to its owner and members only.
    acme_members = {mids[(acme, name)] for name in ('editor', 'multi', 'viewer')}
    for subject in ('owner', 'editor', 'viewer', 'multi'):
        listing = c.expect(subject, 'GET', '/orgs/' + acme + '/members', 200)
        assert {row['id'] for row in listing['rows']} == acme_members and listing['total'] == 3, (subject, listing)
        assert all(row['org'] == acme and row['team'] in (acme + '/editors', acme + '/viewers') for row in listing['rows'])
    for subject in ('outsider', 'guest', anon, forged):
        assert c.expect(subject, 'GET', '/orgs/' + acme + '/members', 200) == {'rows': [], 'total': 0}
    listing = c.expect('multi', 'GET', '/orgs/' + zen + '/members', 200)
    assert {row['id'] for row in listing['rows']} == {mids[(zen, 'multi')]} and listing['total'] == 1
    print('orgs: creator-only owner with two role teams, owner-only membership rows / owners change, '
          'member-only read/list/members passed', flush=True)

    # --- document creation: server-generated key and timestamps ---
    forged_body = {'org': acme, 'title': 'a1', 'body': 'a1 body', 'id': 'client-chosen',
                   'createdAt': 1, 'updatedAt': 1, 'createdBy': ids['viewer'], 'shared': [ids['guest']],
                   'attachment': 'evil'}
    t0 = now_ms()
    a1 = c.created('editor', '/docs', forged_body, '/docs')
    t1 = now_ms()
    assert is_uuid4(a1) and a1 != 'client-chosen', 'document key is not a nyxis-generated UUID'
    doc = c.expect('editor', 'GET', '/docs/' + a1, 200)
    assert doc['org'] == acme and doc['title'] == 'a1' and doc['body'] == 'a1 body'
    assert doc['createdBy'] == ids['editor'] and doc['shared'] == [] and doc['attachment'] == '', doc
    assert doc['createdAt'] == doc['updatedAt'] and t0 - 1 <= doc['createdAt'] <= t1 + 1, (t0, doc, t1)
    stored = db_doc(a1)
    assert stored['createdAt'] == ['datetime', str(doc['createdAt'])], stored
    assert stored['createdBy'] == ['entity', [], 'User', ids['editor']] and stored['shared'] == ['set', []]
    assert stored['attachment'] == ['string', ''], stored
    assert db_doc('client-chosen') is None, 'client-chosen key was stored'
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '1'
    row_checks += 4
    a2 = c.created('owner', '/docs', {'org': acme, 'title': 'a2', 'body': 'a2 body'}, '/docs')
    m1 = c.created('multi', '/docs', {'org': acme, 'title': 'm1', 'body': 'm1 body'}, '/docs')
    z1 = c.created('outsider', '/docs', {'org': zen, 'title': 'z1', 'body': 'z1 body'}, '/docs')
    s1 = c.created('outsider', '/docs', {'org': solo, 'title': 's1', 'body': 's1 body'}, '/docs')
    assert len({a1, a2, m1, z1, s1}) == 5, 'generated keys collide'
    assert all(is_uuid4(k) for k in (a2, m1, z1, s1))
    c.expect('viewer', 'POST', '/docs', 403, {'org': acme, 'title': 'v', 'body': 'v'})
    c.expect('outsider', 'POST', '/docs', 403, {'org': acme, 'title': 'v', 'body': 'v'})
    c.expect('multi', 'POST', '/docs', 403, {'org': zen, 'title': 'v', 'body': 'v'})
    c.expect('guest', 'POST', '/docs', 403, {'org': acme, 'title': 'v', 'body': 'v'})
    c.expect('editor', 'POST', '/docs', 403, {'org': zen, 'title': 'v', 'body': 'v'})
    c.expect('editor', 'POST', '/docs', 403, {'org': str(uuid.uuid4()), 'title': 'v', 'body': 'v'})
    c.expect(anon, 'POST', '/docs', 403, {'org': acme, 'title': 'v', 'body': 'v'})
    c.expect(forged, 'POST', '/docs', 403, {'org': acme, 'title': 'v', 'body': 'v'})
    c.expect('editor', 'POST', '/docs', 400, {'org': acme, 'title': 'v'})
    c.expect('editor', 'POST', '/docs', 400, {'org': 1, 'title': 'v', 'body': 'v'})
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '5'
    print('docs: generated UUID keys and nyxis timestamps, body-supplied id/time/creator ignored, '
          'editor-only creation passed', flush=True)

    # --- reading: own orgs only, other orgs 403, individually shared readable ---
    docs = {a1: acme, a2: acme, m1: acme, z1: zen, s1: solo}
    members = {acme: {'owner', 'editor', 'viewer', 'multi'}, zen: {'outsider', 'multi'}, solo: {'outsider'}}
    shared = {key: set() for key in docs}

    def readable(subject, key):
        return subject in members[docs[key]] or subject in shared[key]

    def verify_reads_and_lists():
        for subject in subjects:
            expected = {}
            for key in docs:
                if readable(subject, key):
                    expected[key] = dict(c.expect(subject, 'GET', '/docs/' + key, 200), id=key)
                else:
                    c.expect(subject, 'GET', '/docs/' + key, 403)
            listing = c.expect(subject, 'GET', '/docs', 200)
            assert isinstance(listing['rows'], list) and {row['id']: row for row in listing['rows']} == expected, (subject, listing)
            assert listing['total'] == len(expected) and [row['id'] for row in listing['rows']] == sorted(expected)
            for org in (acme, zen, solo):
                listing = c.expect(subject, 'GET', '/docs?org=' + org, 200)
                org_expected = {k: v for k, v in expected.items() if docs[k] == org}
                assert {row['id']: row for row in listing['rows']} == org_expected and listing['total'] == len(org_expected)
            assert c.expect(subject, 'GET', '/docs?org=' + str(uuid.uuid4()), 200) == {'rows': [], 'total': 0}
            # The first `org` wins; unrelated parameters are ignored.
            listing = c.expect(subject, 'GET', '/docs?x=1&org=' + acme + '&org=' + zen, 200)
            assert {row['id'] for row in listing['rows']} == {k for k in expected if docs[k] == acme}, (subject, listing)
        c.expect('multi', 'GET', '/docs/' + str(uuid.uuid4()), 403)
        return

    def verify_paging():
        """List queries: filtering happens before the judgement, sorting/paging/count apply to permitted rows only."""
        for subject in subjects:
            readable_docs = {}
            for key in docs:
                if readable(subject, key):
                    readable_docs[key] = dict(c.expect(subject, 'GET', '/docs/' + key, 200), id=key)
            by_title = sorted(readable_docs.values(), key=lambda d: (d['title'], d['id']))
            by_updated_desc = sorted(readable_docs.values(), key=lambda d: (-d['updatedAt'], d['id']))
            # Pages of 2 over the title order: concatenation is the whole permitted list, every page is full
            # except the last, and total never changes. Denied rows (e.g. s1 between m1 and z1) leave no gap.
            seen = []
            for offset in range(0, len(by_title) + 2, 2):
                listing = c.expect(subject, 'GET', '/docs?sort=title&limit=2&offset=%d' % offset, 200)
                assert listing['total'] == len(readable_docs), (subject, listing)
                assert len(listing['rows']) == max(0, min(2, len(by_title) - offset)), (subject, offset, listing)
                seen += listing['rows']
            assert seen == by_title, (subject, seen, by_title)
            listing = c.expect(subject, 'GET', '/docs?sort=updatedAt&dir=desc&limit=3', 200)
            assert listing['rows'] == by_updated_desc[:3] and listing['total'] == len(readable_docs), (subject, listing)
            listing = c.expect(subject, 'GET', '/docs?sort=title&dir=desc', 200)
            assert listing['rows'] == by_title[::-1], (subject, listing)
            # Filters: exact title, updatedAt range, and org combined with paging.
            for key, doc in readable_docs.items():
                listing = c.expect(subject, 'GET', '/docs?title=' + doc['title'], 200)
                assert listing == {'rows': [doc], 'total': 1}, (subject, listing)
            if readable_docs:
                cut = sorted(d['updatedAt'] for d in readable_docs.values())[len(readable_docs) // 2]
                listing = c.expect(subject, 'GET', '/docs?since=%d&sort=updatedAt' % cut, 200)
                expected = sorted((d for d in readable_docs.values() if d['updatedAt'] >= cut), key=lambda d: (d['updatedAt'], d['id']))
                assert listing == {'rows': expected, 'total': len(expected)}, (subject, listing)
                listing = c.expect(subject, 'GET', '/docs?before=%d' % cut, 200)
                expected = sorted((d for d in readable_docs.values() if d['updatedAt'] < cut), key=lambda d: d['id'])
                assert listing == {'rows': expected, 'total': len(expected)}, (subject, listing)
            # String ranges use the code-point order (COLLATE "C" in the DB): titles from 'm' up to (not including) 'z'.
            listing = c.expect(subject, 'GET', '/docs?titleFrom=m&titleTo=z&sort=title', 200)
            expected = [d for d in by_title if 'm' <= d['title'] < 'z']
            assert listing == {'rows': expected, 'total': len(expected)}, (subject, listing)
            listing = c.expect(subject, 'GET', '/docs?titleTo=m', 200)
            expected = sorted((d for d in readable_docs.values() if d['title'] < 'm'), key=lambda d: d['id'])
            assert listing == {'rows': expected, 'total': len(expected)}, (subject, listing)
            acme_docs = sorted((d for d in readable_docs.values() if d['org'] == acme), key=lambda d: (d['title'], d['id']))
            listing = c.expect(subject, 'GET', '/docs?org=' + acme + '&sort=title&limit=1&offset=1', 200)
            assert listing == {'rows': acme_docs[1:2], 'total': len(acme_docs)}, (subject, listing)
            # A denied document is not found by its title either: filtering never widens the permitted set.
            for key in docs:
                if not readable(subject, key):
                    listing = c.expect(subject, 'GET', '/docs?title=' + titles[key], 200)
                    assert listing == {'rows': [], 'total': 0}, (subject, key, listing)
        for query in ('limit=x', 'offset=-1', 'since=soon', 'sort=body', 'dir=up', 'title=a%00b', 'org=%00'):
            c.expect('multi', 'GET', '/docs?' + query, 400)

    verify_reads_and_lists()
    print('reads/lists: multi-org member reads only own orgs, other orgs 403, exact list/readDoc '
          'agreement, query-string org filter with application/json passed', flush=True)
    titles = {a1: 'a1', a2: 'a2', m1: 'm1', z1: 'z1', s1: 's1'}
    verify_paging()
    print('paging: DB-side filters, title/updatedAt ordering, limit/offset over permitted rows only, '
          'total counts permitted rows, denied rows leave no gaps, invalid queries 400 passed', flush=True)

    # --- sharing: individually shared docs become readable, not writable ---
    c.expect('outsider', 'PUT', '/docs/' + s1 + '/shared', 204, {'shared': [ids['guest'], ids['multi']]})
    shared[s1] = {'guest', 'multi'}
    assert db_doc(s1)['shared'] == ['set', sorted([['entity', [], 'User', ids['guest']],
                                                   ['entity', [], 'User', ids['multi']]])]
    row_checks += 1
    assert c.expect('guest', 'GET', '/docs/' + s1, 200)['shared'] == sorted([ids['guest'], ids['multi']])
    c.expect('guest', 'PATCH', '/docs/' + s1, 403, {'title': 'x'})
    c.expect('guest', 'DELETE', '/docs/' + s1, 403)
    c.expect('guest', 'PUT', '/docs/' + s1 + '/shared', 403, {'shared': [ids['guest']]})
    c.expect('multi', 'PUT', '/docs/' + s1 + '/shared', 403, {'shared': []})
    for subject in ('viewer', 'outsider', anon, forged):
        c.expect(subject, 'PUT', '/docs/' + a1 + '/shared', 403, {'shared': [ids['guest']]})
    c.expect('multi', 'PUT', '/docs/' + z1 + '/shared', 403, {'shared': [ids['guest']]})
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': [ids['guest']]})
    shared[a1] = {'guest'}
    c.expect('owner', 'PUT', '/docs/' + a1 + '/shared', 400, {})
    c.expect('owner', 'PUT', '/docs/' + a1 + '/shared', 400, {'shared': [1]})
    verify_reads_and_lists()
    verify_paging()  # with individually shared documents in the permitted sets (guest: s1 and a1)
    c.expect('multi', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': []})
    shared[a1] = set()
    c.expect('guest', 'GET', '/docs/' + a1, 403)
    print('sharing: editor/owner-only sharing, shared guest reads but cannot write, unshare passed', flush=True)

    # --- notifications: mail is a declared external effect judged per subscriber; the job runs as the service ---
    tag = uuid.uuid4().hex[:12]
    address = {name: f'nyxis-{tag}-{name}@example.com' for name in NAMES}
    for name in NAMES:
        assert mails_to(address[name]) == [], 'stale mail for a fresh address'
    checks += 1
    mail_body = 'a1 body\r\n'

    def notifications(key, subject='editor'):
        rows = c.expect(subject, 'GET', '/docs/' + key + '/notifications', 200)['rows']
        return {row['id']: row for row in rows}

    def unsent(key):
        return {nid for nid, row in notifications(key).items() if not row['sent']}

    # Subscribing is self-only and needs a readable document; the address is given by the subscriber, not read from Auth.
    sub_viewer = c.created('viewer', '/docs/' + a1 + '/subscriptions', {'email': address['viewer']}, '/subscriptions')
    assert is_uuid4(sub_viewer)
    c.expect('guest', 'POST', '/docs/' + a1 + '/subscriptions', 403, {'email': address['guest']})     # not shared yet
    c.expect('outsider', 'POST', '/docs/' + a1 + '/subscriptions', 403, {'email': address['outsider']})
    c.expect(anon, 'POST', '/docs/' + a1 + '/subscriptions', 403, {'email': 'anon@example.com'})
    c.expect(forged, 'POST', '/docs/' + a1 + '/subscriptions', 403, {'email': 'forged@example.com'})
    c.expect('viewer', 'POST', '/docs/' + a1 + '/subscriptions', 409, {'email': address['viewer']})   # unique (doc, user)
    c.expect('viewer', 'POST', '/docs/' + a1 + '/subscriptions', 400, {})
    c.expect('viewer', 'POST', '/docs/' + a1 + '/subscriptions', 400, {'email': 1})
    c.expect('editor', 'POST', '/docs/' + str(uuid.uuid4()) + '/subscriptions', 403, {'email': address['editor']})
    # Share #1 (with the guest): the only subscriber (viewer) can read a1, so exactly one mail is sent synchronously.
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': [ids['guest']]})
    shared[a1] = {'guest'}
    sent = mails_to(address['viewer'])
    assert sent == [('a1', mail_body, MAIL_FROM)], sent
    assert all(mails_to(address[name]) == [] for name in NAMES if name != 'viewer')
    checks += 2
    first = notifications(a1)
    assert len(first) == 1 and all(row['sent'] and row['recipient'] == ids['viewer'] and row['email'] == address['viewer']
                                  and row['subject'] == 'a1' and row['body'] == 'a1 body' for row in first.values()), first
    stored = json.loads(sql('SELECT to_jsonb(n)::text FROM public."Notification" n;', DATABASE))
    assert stored['sent'] == ['bool', True] and stored['email'] == ['string', address['viewer']], stored
    row_checks += 1
    # Now the guest (shared) and multi (editor team) subscribe too.
    sub_guest = c.created('guest', '/docs/' + a1 + '/subscriptions', {'email': address['guest']}, '/subscriptions')
    sub_multi = c.created('multi', '/docs/' + a1 + '/subscriptions', {'email': address['multi']}, '/subscriptions')
    listing = c.expect('editor', 'GET', '/docs/' + a1 + '/subscriptions', 200)
    assert {row['id'] for row in listing['rows']} == {sub_viewer, sub_guest, sub_multi} and listing['total'] == 3, listing
    assert all(row['doc'] == a1 for row in listing['rows'])
    listing = c.expect('viewer', 'GET', '/docs/' + a1 + '/subscriptions', 200)
    assert listing == {'rows': [{'id': sub_viewer, 'doc': a1, 'user': ids['viewer'], 'email': address['viewer']}], 'total': 1}, listing
    for subject in ('outsider', anon, forged):
        assert c.expect(subject, 'GET', '/docs/' + a1 + '/subscriptions', 200) == {'rows': [], 'total': 0}
    # Share #2 (unshare the guest): viewer and multi can read a1 and get mail; the guest cannot, so the policy denies that
    # send — no mail, and the notification row stays unsent.
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': []})
    shared[a1] = set()
    assert len(mails_to(address['viewer'])) == 2 and len(mails_to(address['multi'])) == 1, 'sharing did not mail readers'
    assert mails_to(address['guest']) == [], 'a subscriber who cannot read the document was mailed'
    checks += 3
    second = notifications(a1)
    assert len(second) == 4
    pending = unsent(a1)
    assert len(pending) == 1 and second[next(iter(pending))]['recipient'] == ids['guest'], second
    pending_id = next(iter(pending))
    # Only owners/editors (and the service) see notifications; a manual resend by others is denied; a sent one cannot be resent.
    for subject in ('viewer', 'guest', 'outsider', anon, forged):
        assert c.expect(subject, 'GET', '/docs/' + a1 + '/notifications', 200) == {'rows': [], 'total': 0}
        c.expect(subject, 'POST', '/notifications/' + pending_id + '/send', 403)
    for nid, row in second.items():
        if row['sent']:
            c.expect('editor', 'POST', '/notifications/' + nid + '/send', 403)
    c.expect('editor', 'POST', '/notifications/' + pending_id + '/send', 403)   # the guest still cannot read: denied
    assert mails_to(address['guest']) == []
    # The configured service principal id equals the outsider's Auth id: over HTTP the outsider is still User::"...",
    # never Service::"...", so the service-only permissions do not apply to its JWT.
    assert service_id == ids['outsider']
    c.expect('outsider', 'POST', '/notifications/' + pending_id + '/send', 403)
    assert c.expect('outsider', 'GET', '/docs/' + a1 + '/notifications', 200) == {'rows': [], 'total': 0}
    # The periodic job (service principal) runs every JOB_INTERVAL seconds, but the pending send stays denied while the
    # guest cannot read a1: no mail, row still unsent.
    time.sleep(JOB_INTERVAL * 2 + 1)
    assert mails_to(address['guest']) == [] and unsent(a1) == {pending_id}, 'the job sent a denied notification'
    checks += 1
    # Share #3 (with the guest again): three new notifications are sent synchronously (viewer, multi, guest), and the
    # job sends the old pending one as the service principal within its interval.
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': [ids['guest']]})
    shared[a1] = {'guest'}
    assert len(mails_to(address['viewer'])) == 3 and len(mails_to(address['multi'])) == 2
    assert len(mails_to(address['guest'])) == 1
    deadline = time.time() + JOB_INTERVAL * 5 + 5
    while time.time() < deadline and unsent(a1):
        time.sleep(0.5)
    assert unsent(a1) == set(), 'the job did not send the pending notification once the guest could read'
    guest_mail = mails_to(address['guest'])
    assert len(guest_mail) == 2 and all(m == ('a1', mail_body, MAIL_FROM) for m in guest_mail), guest_mail
    assert len(notifications(a1)) == 7 and all(row['sent'] for row in notifications(a1).values())
    assert all(mails_to(address[name]) == [] for name in ('owner', 'editor', 'outsider'))
    checks += 4
    row_checks += 1
    # Unsubscribing is self-only (or creator/owner); the subscriber's notifications cascade with the subscription
    # (each judged by deleteNotification), and the editor's listing shrinks.
    c.expect('viewer', 'DELETE', '/subscriptions/' + sub_guest, 403)
    c.expect('outsider', 'DELETE', '/subscriptions/' + sub_guest, 403)
    c.expect('guest', 'DELETE', '/subscriptions/' + sub_guest, 204)
    assert len(notifications(a1)) == 5 and count('Notification', '"_nyxis_ref_subscription" = ' + quote(sub_guest)) == 0
    c.expect('editor', 'DELETE', '/subscriptions/' + sub_multi, 204)        # a1's creator
    assert c.expect('editor', 'GET', '/docs/' + a1 + '/subscriptions', 200)['total'] == 1
    c.expect('multi', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': []})
    shared[a1] = set()
    assert len(mails_to(address['viewer'])) == 4 and len(mails_to(address['guest'])) == 2 and len(mails_to(address['multi'])) == 2
    assert count('Subscription') == 1 and count('Notification') == 4
    assert all(row['subscription'] == sub_viewer for row in notifications(a1).values())
    row_checks += 1
    checks += 1
    print('notifications: subscriber-supplied addresses, mail only to subscribers who can read the document (viewer/'
          'multi yes, unshared guest no — row left unsent), denied manual resends, service-id JWT is still a User (403), '
          'periodic job as the service principal sends the pending notification once the guest is shared, Mailpit-captured '
          'subject/body/from passed', flush=True)

    # --- attachments: signed URLs are a declared external effect judged by the policy ---
    def storage_requests():
        return len(storage_trace)

    before_storage = storage_requests()
    # Denied subjects: 403, the attachment column stays empty and nothing reaches Storage.
    for subject in ('viewer', 'outsider', 'guest', anon, forged):
        c.expect(subject, 'POST', '/docs/' + a1 + '/attachment', 403)
        c.expect(subject, 'GET', '/docs/' + a1 + '/attachment', 403 if subject in ('outsider', 'guest', anon, forged) else 404)
    c.expect('multi', 'POST', '/docs/' + z1 + '/attachment', 403)            # viewer team of zen
    c.expect('editor', 'POST', '/docs/' + str(uuid.uuid4()) + '/attachment', 403)
    assert db_doc(a1)['attachment'] == ['string', ''] and storage_requests() == before_storage, 'denied attach reached Storage'
    row_checks += 1
    # No attachment yet: readers get 404 without any Storage request.
    for subject in ('owner', 'editor', 'viewer', 'multi'):
        c.expect(subject, 'GET', '/docs/' + a1 + '/attachment', 404)
    assert storage_requests() == before_storage, 'download of a missing attachment reached Storage'
    # The editor attaches: the column records nyxis's generated object name and a signed upload URL is issued.
    issued = c.expect('editor', 'POST', '/docs/' + a1 + '/attachment', 200)
    assert set(issued) == {'url', 'object'} and is_uuid4(issued['object']), issued
    assert db_doc(a1)['attachment'] == ['string', issued['object']], db_doc(a1)
    row_checks += 1
    object_path = f'{BUCKET}/Doc/{a1}/{issued["object"]}'
    assert issued['url'].startswith(RELAY + '/storage/v1/object/upload/sign/' + object_path + '?token='), issued['url']
    assert storage_requests() == before_storage + 1
    assert storage_trace[-1] == ('/storage/v1/object/upload/sign/' + object_path, True), storage_trace[-1]
    content = ('attachment of ' + a1 + ' ' + uuid.uuid4().hex).encode()
    status, raw = raw_storage('PUT', local_url(issued['url']), content, {'Content-Type': 'text/plain'})
    assert status == 200, ('upload with the signed URL failed', status)
    checks += 1
    # Readers (owner, editor team, viewer team, multi-org member) get a signed download URL that returns the bytes.
    for subject in ('owner', 'editor', 'viewer', 'multi'):
        link = c.expect(subject, 'GET', '/docs/' + a1 + '/attachment', 200)
        assert set(link) == {'url'} and link['url'].startswith(RELAY + '/storage/v1/object/sign/' + object_path + '?token='), link
        status, raw = raw_storage('GET', local_url(link['url']))
        assert status == 200 and raw == content, ('download with the signed URL failed', status)
        checks += 1
        assert storage_trace[-1] == ('/storage/v1/object/sign/' + object_path, True)
    download_url = local_url(c.expect('viewer', 'GET', '/docs/' + a1 + '/attachment', 200)['url'])
    for subject in ('outsider', 'guest', anon, forged):
        c.expect(subject, 'GET', '/docs/' + a1 + '/attachment', 403)
    denied_storage = storage_requests()
    # A signed URL is bound to its object: the same token does not read another path, and the bucket is private.
    other = download_url.replace(issued['object'], 'other-object')
    status, _ = raw_storage('GET', other)
    assert status in (400, 401, 403, 404), ('signed URL reached another object', status)
    status, _ = raw_storage('GET', f'/storage/v1/object/{object_path}')
    assert status in (400, 401, 403, 404), ('object readable without a signed URL', status)
    status, _ = raw_storage('GET', f'/storage/v1/object/public/{object_path}')
    assert status in (400, 401, 403, 404), ('object readable as public', status)
    checks += 3
    assert storage_requests() == denied_storage, 'client-side Storage checks were routed through the sample'
    # Sharing grants download to the guest; unsharing takes it away again.
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': [ids['guest']]})
    link = c.expect('guest', 'GET', '/docs/' + a1 + '/attachment', 200)
    assert raw_storage('GET', local_url(link['url']))[0] == 200
    checks += 1
    c.expect('guest', 'POST', '/docs/' + a1 + '/attachment', 403)        # shared: read only
    c.expect('editor', 'PUT', '/docs/' + a1 + '/shared', 204, {'shared': []})
    c.expect('guest', 'GET', '/docs/' + a1 + '/attachment', 403)
    # Re-attaching issues a new object name; until it is uploaded, Storage knows no such object (404 from the sample).
    again = c.expect('owner', 'POST', '/docs/' + a1 + '/attachment', 200)
    assert again['object'] != issued['object'] and is_uuid4(again['object'])
    assert db_doc(a1)['attachment'] == ['string', again['object']]
    row_checks += 1
    missing = c.expect('viewer', 'GET', '/docs/' + a1 + '/attachment', 404)
    assert storage_trace[-1] == (f'/storage/v1/object/sign/{BUCKET}/Doc/{a1}/{again["object"]}', True)
    status, _ = raw_storage('PUT', local_url(again['url']), b'second version', {'Content-Type': 'text/plain'})
    assert status == 200
    checks += 1
    link = c.expect('viewer', 'GET', '/docs/' + a1 + '/attachment', 200)
    assert raw_storage('GET', local_url(link['url'])) == (200, b'second version')
    checks += 1
    # Other documents: the owner attaches to a2, the multi-org editor to m1; z1 (zen) stays out of reach for acme's editor.
    for subject, key in (('owner', a2), ('multi', m1)):
        issued_other = c.expect(subject, 'POST', '/docs/' + key + '/attachment', 200)
        assert issued_other['url'].startswith(f'{RELAY}/storage/v1/object/upload/sign/{BUCKET}/Doc/{key}/{issued_other["object"]}?token=')
    c.expect('editor', 'POST', '/docs/' + z1 + '/attachment', 403)
    c.expect('editor', 'GET', '/docs/' + z1 + '/attachment', 403)
    assert all(path.startswith(f'/storage/v1/object/upload/sign/{BUCKET}/Doc/') or
               path.startswith(f'/storage/v1/object/sign/{BUCKET}/Doc/') for path, _ in storage_trace), storage_trace
    assert all(service for _, service in storage_trace), 'the sample signed without the service_role key'
    print('attachments: editor/owner-only signed upload URLs recording nyxis\'s object name, reader-only signed '
          'download URLs, 403 without any Storage request, upload/download through the issued URLs, token bound to its '
          'object, private bucket, sharing grants/revokes download passed', flush=True)

    # --- editing: updatedAt is nyxis's clock, createdAt unchanged ---
    before = c.expect('editor', 'GET', '/docs/' + a1, 200)
    time.sleep(0.002)
    t0 = now_ms()
    c.expect('editor', 'PATCH', '/docs/' + a1, 204, {'title': 'edited', 'updatedAt': 1, 'createdAt': 1, 'org': zen})
    t1 = now_ms()
    after = c.expect('viewer', 'GET', '/docs/' + a1, 200)
    assert after['title'] == 'edited' and after['body'] == before['body'] and after['org'] == acme
    assert after['createdAt'] == before['createdAt'] and after['updatedAt'] > before['updatedAt']
    assert t0 - 1 <= after['updatedAt'] <= t1 + 1, (t0, after, t1)
    assert db_doc(a1)['updatedAt'] == ['datetime', str(after['updatedAt'])]
    row_checks += 1
    c.expect('owner', 'PATCH', '/docs/' + a2, 204, {'body': 'owner edited'})
    c.expect('multi', 'PATCH', '/docs/' + a1, 204, {'body': 'multi edited'})
    c.expect('viewer', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    c.expect('outsider', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    c.expect('multi', 'PATCH', '/docs/' + z1, 403, {'title': 'x'})
    c.expect(anon, 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    c.expect(forged, 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    c.expect('editor', 'PATCH', '/docs/' + a1, 400, {})
    c.expect('editor', 'PATCH', '/docs/' + a1, 400, {'updatedAt': 1})
    c.expect('editor', 'PATCH', '/docs/' + str(uuid.uuid4()), 403, {'title': 'x'})
    print('edits: nyxis updatedAt, body-supplied timestamps ignored, editor/owner-only passed', flush=True)

    # --- external API calls: a sync response written through a second judged action; async via the outbox ---
    before_sync = len(mock_requests('/summarizer/'))
    # Denied subjects: 403, no request reaches the summarizer, the summary column stays empty.
    for subject in ('viewer', 'outsider', 'guest', anon, forged):
        c.expect(subject, 'POST', '/docs/' + a1 + '/summary', 403)
    c.expect('multi', 'POST', '/docs/' + z1 + '/summary', 403)        # viewer team of zen
    c.expect('editor', 'POST', '/docs/' + z1 + '/summary', 403)       # other org
    c.expect('editor', 'POST', '/docs/' + str(uuid.uuid4()) + '/summary', 403)
    assert shared[s1] == {'guest', 'multi'} and c.expect('guest', 'GET', '/docs/' + s1, 200)['summary'] == ''
    c.expect('guest', 'POST', '/docs/' + s1 + '/summary', 403)        # individually shared: reads, but no call
    c.expect('multi', 'POST', '/docs/' + s1 + '/summary', 403)        # shared on s1, not a member of solo
    c.expect('guest', 'PATCH', '/docs/' + s1, 403, {'title': 'x'})    # shared: no edit, hence no announcement
    assert db_doc(s1)['summary'] == ['string', ''], db_doc(s1)
    assert len(mock_requests('/summarizer/')) == before_sync, 'a denied summarizeDoc reached the summarizer'
    assert db_doc(a1)['summary'] == ['string', ''], db_doc(a1)
    checks += 1
    row_checks += 1
    # The editor: nyxis sends the declared columns (title, body) with the configured bearer key to the declared URL,
    # decodes the 2xx answer to the declared type (the undeclared `model` key is dropped) and the handler records the
    # value through recordSummary; readers see it.
    current = c.expect('editor', 'GET', '/docs/' + a1, 200)
    expected_summary = summary_of(current['title'], current['body'])
    assert c.expect('editor', 'POST', '/docs/' + a1 + '/summary', 200) == {'summary': expected_summary}
    assert db_doc(a1)['summary'] == ['string', expected_summary], db_doc(a1)
    assert c.expect('viewer', 'GET', '/docs/' + a1, 200)['summary'] == expected_summary
    row_checks += 1
    sent = mock_requests('/summarizer/')
    assert len(sent) == before_sync + 1, sent
    assert sent[-1] == ('POST', '/summarizer/v1/summaries/' + a1, 'summarizer', {'title': current['title'], 'body': current['body']}, True), sent[-1]
    checks += 1
    for subject, key in (('owner', a2), ('multi', m1)):           # the owner branch of the policy; the multi-org editor
        doc = c.expect(subject, 'GET', '/docs/' + key, 200)
        assert c.expect(subject, 'POST', '/docs/' + key + '/summary', 200) == {'summary': summary_of(doc['title'], doc['body'])}
        assert mock_requests('/summarizer/')[-1][1:3] == ('/summarizer/v1/summaries/' + key, 'summarizer')
    checks += 2
    # A non-2xx answer reaches the handler as status + body (the transaction continues) and is mapped to 424 with the
    # upstream status; nothing is recorded.
    r1 = c.created('editor', '/docs', {'org': acme, 'title': 'r1', 'body': 'reject this text'}, '/docs')
    got, raw, headers = request('POST', '/docs/' + r1 + '/summary', None, c.headers('editor'))
    assert got == 424 and json.loads(raw) == {'error': 'summarizer', 'status': 422}, (got, raw)
    assert headers.get('content-type') == 'application/json'
    assert mock_requests('/summarizer/')[-1][1] == '/summarizer/v1/summaries/' + r1
    assert db_doc(r1)['summary'] == ['string', ''], db_doc(r1)
    checks += 1
    row_checks += 1
    # The response value enters the DB only through recordSummary's own judgement: the mock answers an empty summary for a
    # blank document, the policy denies recording it (403) although the call itself was permitted and sent.
    e1 = c.created('editor', '/docs', {'org': acme, 'title': 'e1', 'body': '   '}, '/docs')
    c.expect('editor', 'POST', '/docs/' + e1 + '/summary', 403)
    assert mock_requests('/summarizer/')[-1] == ('POST', '/summarizer/v1/summaries/' + e1, 'summarizer', {'title': 'e1', 'body': '   '}, True)
    assert db_doc(e1)['summary'] == ['string', ''], db_doc(e1)
    checks += 1
    row_checks += 1
    c.expect('editor', 'DELETE', '/docs/' + r1, 204)
    c.expect('editor', 'DELETE', '/docs/' + e1, 204)
    # async: every permitted edit so far left exactly one outbox row for the audit API, written in the request's
    # transaction and delivered by nyxis's internal loop after COMMIT; a denied edit leaves none.
    c.expect('viewer', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    assert len(outbox_rows()) == edits_announced, 'a denied edit left an outbox row'
    c.expect('editor', 'PATCH', '/docs/' + a1, 204, {'body': 'announced'})
    announced = c.expect('editor', 'GET', '/docs/' + a1, 200)
    rows = settled_outbox(edits_announced)
    assert len(rows) == edits_announced, (len(rows), edits_announced)
    for row in rows:
        assert (row['state'], row['attempts'], row['last_status'], row['last_error'], row['sent']) == ('sent', 1, 202, None, True), row
        assert (row['destination'], row['method'], row['action']) == ('Audit', 'POST', 'announceDocUpdate'), row
        table, key = row['target'].split('/', 1)
        assert table == 'Doc' and row['url'] == MOCK + '/audit/v1/docs/' + key + '/updated', row
        assert set(row['body']) == {'title', 'updatedAt'} and row['id'].endswith('-0'), row
        assert row['principal'].startswith('User::"') and row['principal'][7:-1] in ids.values(), row['principal']
    last = rows[-1]
    assert last['target'] == 'Doc/' + a1 and last['principal'] == 'User::"' + ids['editor'] + '"', last
    assert last['body'] == {'title': announced['title'], 'updatedAt': announced['updatedAt']}, (last, announced)
    row_checks += 2
    delivered = mock_requests('/audit/')
    assert len(delivered) == len(rows), (len(delivered), len(rows))
    assert all(method == 'POST' and auth == 'audit' and clean for (method, _, auth, _, clean) in delivered), delivered
    assert sorted((path, json.dumps(body, sort_keys=True)) for (_, path, _, body, _) in delivered) == \
        sorted((row['url'][len(MOCK):], json.dumps(row['body'], sort_keys=True)) for row in rows), \
        'the requests the audit API received differ from the outbox rows'
    checks += 2
    dump = sql('SELECT string_agg(to_jsonb(o)::text, \',\') FROM public."_nyxis_outbox" o;', DATABASE)
    assert SUMMARIZER_SECRET not in dump and AUDIT_SECRET not in dump, 'a destination secret is stored in the outbox'
    row_checks += 1
    print('external API calls: owner/editor-only sync summaries sent with the configured key and declared columns, '
          'decoded answer recorded only through recordSummary (empty summary denied, 422 mapped to 424), 403 without any '
          'request for denied subjects, each permitted edit announced once through the outbox and delivered to the audit API '
          'after COMMIT, denied edits leave no row passed', flush=True)

    # --- membership row changes take effect on the next request ---
    c.expect('owner', 'DELETE', '/memberships/' + mids.pop((acme, 'viewer')), 204)
    members[acme].discard('viewer')
    c.expect('viewer', 'GET', '/docs/' + a1, 403)
    c.expect('viewer', 'GET', '/orgs/' + acme, 403)
    assert c.expect('viewer', 'GET', '/docs', 200) == {'rows': [], 'total': 0}
    add_member('owner', acme, 'viewer', 'viewer')
    add_member('owner', acme, 'guest', 'viewer')
    members[acme] |= {'viewer', 'guest'}
    verify_reads_and_lists()
    c.expect('viewer', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})      # viewer team: read only
    c.expect('guest', 'POST', '/docs', 403, {'org': acme, 'title': 'x', 'body': 'x'})
    # Leaving an org (deleting one's own membership row) is allowed; removing someone else's is owner-only.
    c.expect('guest', 'DELETE', '/memberships/' + mids[(acme, 'editor')], 403)
    c.expect('guest', 'DELETE', '/memberships/' + mids.pop((acme, 'guest')), 204)
    members[acme].discard('guest')
    c.expect('guest', 'GET', '/docs/' + a1, 403)
    c.expect('owner', 'DELETE', '/memberships/' + mids.pop((acme, 'editor')), 204)
    members[acme].discard('editor')
    c.expect('editor', 'POST', '/docs', 403, {'org': acme, 'title': 'x', 'body': 'x'})
    c.expect('editor', 'GET', '/docs/' + a1, 403)
    c.expect('editor', 'DELETE', '/docs/' + a1, 403)
    c.expect('editor', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    add_member('owner', acme, 'editor', 'viewer')          # back as a viewer: reads, but cannot write or delete
    members[acme].add('editor')
    c.expect('editor', 'GET', '/docs/' + a1, 200)
    c.expect('editor', 'PATCH', '/docs/' + a1, 403, {'title': 'x'})
    c.expect('editor', 'DELETE', '/docs/' + a1, 403)
    c.expect('owner', 'DELETE', '/memberships/' + mids.pop((acme, 'editor')), 204)
    add_member('owner', acme, 'editor', 'editor')
    c.expect('editor', 'PATCH', '/docs/' + a1, 204, {'body': 'editor again'})
    assert count('Membership') == 4
    row_checks += 1
    print('membership rows: removal / re-addition / self-removal take effect on the next request, '
          'viewer team reads only, editor team writes passed', flush=True)

    # --- deletion: org owner and the creator while still an editor ---
    c.expect('viewer', 'DELETE', '/docs/' + a1, 403)
    c.expect('guest', 'DELETE', '/docs/' + a1, 403)
    c.expect('outsider', 'DELETE', '/docs/' + a1, 403)
    c.expect('editor', 'DELETE', '/docs/' + a2, 403)
    c.expect('multi', 'DELETE', '/docs/' + z1, 403)
    c.expect(anon, 'DELETE', '/docs/' + a1, 403)
    c.expect(forged, 'DELETE', '/docs/' + a1, 403)
    c.expect('owner', 'DELETE', '/docs/' + str(uuid.uuid4()), 403)
    c.expect('owner', 'DELETE', '/docs/' + a2, 204)
    del docs[a2]
    c.expect('owner', 'GET', '/docs/' + a2, 403)
    c.expect('editor', 'DELETE', '/docs/' + a1, 204)
    del docs[a1]
    c.expect('multi', 'DELETE', '/docs/' + m1, 204)
    del docs[m1]
    c.expect('outsider', 'DELETE', '/docs/' + z1, 204)
    del docs[z1]
    verify_reads_and_lists()
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '1'
    assert sql('SELECT count(*) FROM public."Org";', DATABASE) == '3'
    assert sql('SELECT count(*) FROM public."User";', DATABASE) == '6'
    assert count('Team') == 6 and count('Membership') == 4
    # a1's subscription and notifications were cascaded with it (each judged by deleteSubscription / deleteNotification).
    assert count('Subscription') == 0 and count('Notification') == 0
    row_checks += 5
    print('deletes: creator only (owners cannot delete other creators\' documents), denied deletes leave rows, '
          'subscriptions/notifications cascade with the document passed', flush=True)

    # --- uniqueness and referential integrity ---
    u1 = c.created('editor', '/docs', {'org': acme, 'title': 'u1', 'body': 'u1'}, '/docs')
    c.expect('editor', 'POST', '/docs', 409, {'org': acme, 'title': 'u1', 'body': 'again'})
    c.expect('owner', 'POST', '/docs', 409, {'org': acme, 'title': 'u1', 'body': 'again'})
    c.expect('viewer', 'POST', '/docs', 403, {'org': acme, 'title': 'u1', 'body': 'again'})   # not permitted: 403, not 409
    c.expect('outsider', 'POST', '/docs', 403, {'org': acme, 'title': 'u1', 'body': 'again'})
    u1z = c.created('outsider', '/docs', {'org': zen, 'title': 'u1', 'body': 'same title, other org'}, '/docs')
    u2 = c.created('owner', '/docs', {'org': acme, 'title': 'u2', 'body': 'u2'}, '/docs')
    c.expect('editor', 'PATCH', '/docs/' + u1, 409, {'title': 'u2'})
    c.expect('editor', 'PATCH', '/docs/' + u1, 204, {'title': 'u1'})          # own title is not a conflict
    c.expect('editor', 'PATCH', '/docs/' + u1, 204, {'title': 'u1 renamed'})
    c.expect('editor', 'PATCH', '/docs/' + u1, 204, {'title': 'u1'})
    c.expect('guest', 'POST', '/orgs', 409, {'name': 'Acme'})
    extra = c.created('guest', '/orgs', {'name': 'Acme '}, '/orgs')
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '4' and sql('SELECT count(*) FROM public."Org";', DATABASE) == '4'
    row_checks += 2
    # The same constraints exist in the DB (backstop): direct duplicate / dangling inserts and a referenced delete are rejected.
    for statement in (
            'INSERT INTO public."Doc" ("_nyxis_id", "org", "title") VALUES (\'direct-dup\', \'["entity",[],"Org","%s"]\', \'["string","u1"]\');' % acme,
            'INSERT INTO public."Doc" ("_nyxis_id", "org", "title") VALUES (\'direct-dangling\', \'["entity",[],"Org","%s"]\', \'["string","x"]\');' % str(uuid.uuid4()),
            'INSERT INTO public."Org" ("_nyxis_id", "name") VALUES (\'direct-dup-org\', \'["string","Acme"]\');',
            'INSERT INTO public."Membership" ("_nyxis_id", "user", "team", "org") VALUES (\'direct-dup-member\', \'["entity",[],"User","%s"]\', \'["entity",[],"Team","%s/editors"]\', \'["entity",[],"Org","%s"]\');' % (ids['editor'], acme, acme),
            'INSERT INTO public."Membership" ("_nyxis_id", "user", "team", "org") VALUES (\'direct-dangling-member\', \'["entity",[],"User","%s"]\', \'["entity",[],"Team","nope"]\', \'["entity",[],"Org","%s"]\');' % (ids['guest'], acme),
            'DELETE FROM public."Team" WHERE "_nyxis_id" = \'%s/editors\';' % acme,
            'DELETE FROM public."Org" WHERE "_nyxis_id" = \'%s\';' % acme):
        try:
            sql(statement, DATABASE)
        except RuntimeError:
            row_checks += 1
        else:
            raise AssertionError('DB-side constraint did not reject: ' + statement[:40])
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '4' and sql('SELECT count(*) FROM public."Org";', DATABASE) == '4'
    assert count('Team') == 8 and count('Membership') == 4
    row_checks += 1
    print('uniqueness: duplicate titles within an org and duplicate org names are 409, other orgs / own title OK, '
          'denied subjects get 403, DB UNIQUE / FOREIGN KEY backstop (documents, orgs, membership rows, teams) passed', flush=True)
    # restrict: a user who created documents cannot be deleted; a user without documents can delete only itself,
    # and its membership rows cascade (each judged by removeMember: the user itself is permitted).
    c.expect('editor', 'DELETE', '/users/' + ids['editor'], 409)
    c.expect('owner', 'DELETE', '/users/' + ids['owner'], 409)
    c.expect('viewer', 'DELETE', '/users/' + ids['editor'], 403)
    c.expect(anon, 'DELETE', '/users/' + ids['viewer'], 403)
    c.expect(forged, 'DELETE', '/users/' + ids['viewer'], 403)
    c.expect('viewer', 'DELETE', '/users/' + ids['viewer'], 204)
    c.expect('viewer', 'GET', '/users/' + ids['viewer'], 404)
    assert count('Membership') == 3 and count('Membership', '"_nyxis_id" = ' + quote(mids.pop((acme, 'viewer')))) == 0
    row_checks += 1
    assert c.expect('viewer', 'POST', '/users/' + ids['viewer'], 201, {'name': 'Viewer'}) == {'id': ids['viewer']}
    c.expect('viewer', 'GET', '/orgs/' + acme, 403)         # the membership row is gone: no longer a member
    assert c.expect('viewer', 'GET', '/orgs', 200) == {'rows': [], 'total': 0}
    add_member('owner', acme, 'viewer', 'viewer')
    c.expect('viewer', 'GET', '/orgs/' + acme, 200)
    print('referential integrity: deleting a document creator is 409 (restrict), self-deletion without documents 204 '
          'with its membership rows cascaded passed', flush=True)
    # cascade: deleting an org deletes its documents only if every document's deleteDoc is permitted for the caller.
    c.expect('owner', 'DELETE', '/orgs/' + acme, 403)      # u1 belongs to editor: the owner may not delete it
    c.expect('editor', 'DELETE', '/orgs/' + acme, 403)     # not an owner
    c.expect('multi', 'DELETE', '/orgs/' + acme, 403)
    c.expect(anon, 'DELETE', '/orgs/' + acme, 403)
    c.expect(forged, 'DELETE', '/orgs/' + acme, 403)
    c.expect('owner', 'GET', '/docs/' + u1, 200)
    c.expect('owner', 'GET', '/docs/' + u2, 200)
    c.expect('editor', 'DELETE', '/docs/' + u1, 204)
    assert count('Team', '"_nyxis_ref_org" = ' + quote(acme)) == 2 and count('Membership', '"_nyxis_ref_org" = ' + quote(acme)) == 3
    c.expect('owner', 'DELETE', '/orgs/' + acme, 204)      # only the owner's own u2 remains: cascade permitted (teams, 3 membership rows, u2)
    c.expect('owner', 'GET', '/docs/' + u2, 403)
    c.expect('owner', 'GET', '/orgs/' + acme, 403)
    c.expect('owner', 'DELETE', '/orgs/' + acme, 403)
    c.expect('editor', 'GET', '/orgs/' + acme, 403)
    assert c.expect('editor', 'GET', '/orgs', 200) == {'rows': [], 'total': 0}
    assert sql('SELECT count(*) FROM public."Doc" WHERE "org" = \'["entity",[],"Org","%s"]\';' % acme, DATABASE) == '0'
    assert sql('SELECT count(*) FROM public."Org" WHERE "_nyxis_id" = \'%s\';' % acme, DATABASE) == '0'
    assert count('Team', '"_nyxis_ref_org" = ' + quote(acme)) == 0 and count('Membership', '"_nyxis_ref_org" = ' + quote(acme)) == 0
    assert count('Team') == 6 and count('Membership') == 1
    row_checks += 5
    z2 = c.created('outsider', '/docs', {'org': zen, 'title': 'z2', 'body': 'z2'}, '/docs')
    z3 = c.created('outsider', '/docs', {'org': zen, 'title': 'z3', 'body': 'z3'}, '/docs')
    c.expect('outsider', 'PUT', '/docs/' + z2 + '/shared', 204, {'shared': [ids['guest']]})
    c.expect('guest', 'DELETE', '/orgs/' + zen, 403)
    c.expect('multi', 'DELETE', '/orgs/' + zen, 403)       # viewer of zen, not an owner
    c.expect('outsider', 'DELETE', '/orgs/' + zen, 204)    # u1z, z2, z3 are all the outsider's: three cascaded deletes
    for key in (u1z, z2, z3):
        c.expect('outsider', 'GET', '/docs/' + key, 403)
        c.expect('guest', 'GET', '/docs/' + key, 403)
    assert c.expect('multi', 'GET', '/orgs', 200) == {'rows': [], 'total': 0}
    c.expect('guest', 'DELETE', '/orgs/' + extra, 204)
    c.expect('outsider', 'DELETE', '/orgs/' + solo, 204)   # s1 is the outsider's
    assert sql('SELECT count(*) FROM public."Doc";', DATABASE) == '0'
    assert sql('SELECT count(*) FROM public."Org";', DATABASE) == '0'
    assert sql('SELECT count(*) FROM public."User";', DATABASE) == '6'
    assert count('Team') == 0 and count('Membership') == 0
    row_checks += 4
    for name in ('owner', 'editor', 'viewer'):
        c.expect(name, 'DELETE', '/users/' + ids[name], 204)   # no documents reference them any more
    assert sql('SELECT count(*) FROM public."User";', DATABASE) == '3'
    row_checks += 1
    print('cascade: org deletion is 403 and leaves every row while a non-creator document remains, '
          'cascades (teams, membership rows, three documents) once every deleteDoc is permitted, restrict lifted after cascade passed', flush=True)
    # Every permitted edit of the whole run (including the later renames) was announced through the outbox exactly once
    # and delivered; the rows outlive the deleted documents (the outbox is nyxis's own record, not a declared table).
    rows = settled_outbox(edits_announced)
    assert len(rows) == edits_announced and all(r['state'] == 'sent' for r in rows), [(r['target'], r['state']) for r in rows]
    assert len(mock_requests('/audit/')) == len(rows)
    row_checks += 1


def main():
    global checks
    endpoint = urlsplit(os.environ.get('NYXIS_DATABASE_URL', ''))
    assert endpoint.scheme in ('postgres', 'postgresql'), 'local DB URL required'
    assert endpoint.hostname in ('127.0.0.1', 'localhost', '::1'), 'local DB required'
    assert endpoint.port == 55322 and endpoint.path == '/postgres', 'nyxis local DB required'
    assert not endpoint.query and not endpoint.fragment, 'unexpected DB URL options'
    nyxis_local.require_local_docker(ENV)
    nyxis_local.require_free_port(PORT)
    nyxis_local.require_free_port(MOCK_PORT)
    service_key = os.environ.get('NYXIS_SUPABASE_SERVICE_ROLE_KEY')
    assert service_key, 'local service_role key required (before-cycle --exec)'
    with ExitStack() as resources:
        cert, key = resources.enter_context(nyxis_local.tls_material('nyxis-team-docs-'))
        trace = []
        upstream = [0]

        def document():
            upstream[0] += 1
            return nyxis_local.local_jwks()

        def storage(path, authorization, body):
            # The sample must sign with the service_role key and only under the test bucket (Assumption 2).
            storage_trace.append((path, authorization == 'Bearer ' + service_key))
            assert path.startswith(('/storage/v1/object/upload/sign/' + BUCKET + '/',
                                    '/storage/v1/object/sign/' + BUCKET + '/')), 'signing outside the test bucket'
            return nyxis_local.storage_request('POST', path, body, key=service_key,
                                                headers={'Content-Type': 'application/json'})

        server = resources.enter_context(nyxis_local.tls_server(
            nyxis_local.relay_handler(document, trace=trace.append, storage=storage), cert, key, port=55325))
        issuer = f'https://localhost:{server.server_port}/auth/v1'
        assert RELAY == f'https://localhost:{server.server_port}'
        # The mock external API on the fixed port the schema's `@external` destinations name, with the same
        # throwaway certificate (CN localhost) the sample trusts for the relay.
        mock = resources.enter_context(nyxis_local.tls_server(make_mock(), cert, key, port=MOCK_PORT))
        assert MOCK == f'https://localhost:{mock.server_port}'
        schema_text = (BACKEND / 'schema.cedarschema').read_text()
        assert f'base: {MOCK}/summarizer; auth: bearer NYXIS_EXT_SUMMARIZER' in schema_text, 'schema destination differs'
        assert f'base: {MOCK}/audit; auth: bearer NYXIS_EXT_AUDIT' in schema_text, 'schema destination differs'
        config = tomllib.loads((ROOT / 'supabase/config.toml').read_text())
        assert config['auth']['jwt_issuer'] == issuer, 'local Auth issuer differs'
        assert config['storage']['enabled'] is True, 'local Storage must be enabled for attachments'
        sessions = resources.enter_context(nyxis_local.auth_sessions(NAMES, prefix='nyxis-team-docs-'))
        tokens = {name: info['access_token'] for name, info in sessions.items()}
        ids = {name: info['id'] for name, info in sessions.items()}

        env = ENV.copy()
        env['NYXIS_DATABASE_URL'] = urlunsplit(endpoint._replace(path='/' + DATABASE))
        env['NYXIS_SUPABASE_ISSUER'] = issuer
        env['NYXIS_STORAGE_URL'] = RELAY
        env['NYXIS_STORAGE_BUCKET'] = BUCKET
        env['NYXIS_STORAGE_SERVICE_KEY'] = service_key
        env['NYXIS_SMTP_URL'] = SMTP
        env['NYXIS_MAIL_FROM'] = MAIL_FROM
        env['NYXIS_SERVICE_PRINCIPAL'] = 'Service::"' + ids['outsider'] + '"'
        env['NYXIS_JOB_INTERVAL_SECONDS'] = str(JOB_INTERVAL)
        env['NYXIS_EXT_SUMMARIZER'] = SUMMARIZER_SECRET   # the keys of the schema's two destinations (required at startup)
        env['NYXIS_EXT_AUDIT'] = AUDIT_SECRET
        env['NYXIS_OUTBOX_INTERVAL_SECONDS'] = str(OUTBOX_INTERVAL)
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            env.pop(name, None)
        env['CURL_CA_BUNDLE'] = str(cert)  # test child only; no runtime parameter is introduced
        created = False
        bucket_created = False
        proc = None
        try:
            status, raw = nyxis_local.storage_request(
                'POST', '/storage/v1/bucket', json.dumps({'id': BUCKET, 'name': BUCKET, 'public': False}).encode(),
                key=service_key, headers={'Content-Type': 'application/json'})
            assert status == 200, 'local Storage bucket creation failed (diagnostics withheld)'
            bucket_created = True
            sql('CREATE DATABASE "' + DATABASE + '";')
            created = True
            init = subprocess.run([str(BACKEND / '.lake/build/bin/initTeamDocsDatabase')], env=env,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
            assert init.returncode == 0, 'team-docs provisioning failed (diagnostics withheld)'
            # The declared tables; nyxis's reserved outbox is checked separately below.
            columns = sql('''SELECT string_agg(table_name || '.' || column_name || ':' || data_type, ',' ORDER BY table_name, ordinal_position)
                FROM information_schema.columns WHERE table_schema = 'public' AND table_name <> '_nyxis_outbox';''', DATABASE)
            assert columns == ('Doc._nyxis_id:text,Doc.org:jsonb,Doc.title:jsonb,Doc.body:jsonb,Doc.shared:jsonb,'
                               'Doc.createdBy:jsonb,Doc.createdAt:jsonb,Doc.updatedAt:jsonb,Doc.attachment:jsonb,Doc.summary:jsonb,'
                               'Doc._nyxis_ref_org:text,Doc._nyxis_ref_createdBy:text,'
                               'Membership._nyxis_id:text,Membership.user:jsonb,Membership.team:jsonb,Membership.org:jsonb,'
                               'Membership._nyxis_ref_user:text,Membership._nyxis_ref_team:text,Membership._nyxis_ref_org:text,'
                               'Notification._nyxis_id:text,Notification.doc:jsonb,Notification.recipient:jsonb,Notification.subscription:jsonb,'
                               'Notification.email:jsonb,Notification.subject:jsonb,Notification.body:jsonb,Notification.sent:jsonb,'
                               'Notification._nyxis_ref_doc:text,Notification._nyxis_ref_recipient:text,Notification._nyxis_ref_subscription:text,'
                               'Org._nyxis_id:text,Org.name:jsonb,Org.owners:jsonb,Org.editors:jsonb,Org.viewers:jsonb,'
                               'Subscription._nyxis_id:text,Subscription.doc:jsonb,Subscription.user:jsonb,Subscription.email:jsonb,'
                               'Subscription._nyxis_ref_doc:text,Subscription._nyxis_ref_user:text,'
                               'Team._nyxis_id:text,Team.org:jsonb,Team.role:jsonb,Team._nyxis_ref_org:text,'
                               'User._nyxis_id:text,User.name:jsonb'), columns
            # nyxis's reserved outbox exists with its fixed shape (docs/external-calls.md §4.3) in every provisioned
            # database; team-docs' `async` call (announceDocUpdate) writes to it — checked in verify().
            outbox = sql('''SELECT string_agg(column_name || ':' || data_type, ',' ORDER BY ordinal_position)
                FROM information_schema.columns WHERE table_schema = 'public' AND table_name = '_nyxis_outbox';''', DATABASE)
            assert outbox == ('_nyxis_id:text,principal:text,action:text,target:text,destination:text,method:text,url:text,'
                              'body:jsonb,state:text,attempts:integer,next_at:timestamp with time zone,last_status:integer,'
                              'last_error:text,created_at:timestamp with time zone,sent_at:timestamp with time zone'), outbox
            constraints = sql('''SELECT string_agg(constraint_name || ':' || constraint_type, ',' ORDER BY constraint_name)
                FROM information_schema.table_constraints
                WHERE table_schema = 'public' AND constraint_type IN ('UNIQUE', 'FOREIGN KEY');''', DATABASE)
            assert constraints == ('Doc_createdBy_fkey:FOREIGN KEY,Doc_org_fkey:FOREIGN KEY,Doc_org_title_key:UNIQUE,'
                                   'Membership_org_fkey:FOREIGN KEY,Membership_team_fkey:FOREIGN KEY,Membership_user_fkey:FOREIGN KEY,'
                                   'Membership_user_team_key:UNIQUE,Notification_doc_fkey:FOREIGN KEY,Notification_recipient_fkey:FOREIGN KEY,'
                                   'Notification_subscription_fkey:FOREIGN KEY,'
                                   'Org_name_key:UNIQUE,Subscription_doc_fkey:FOREIGN KEY,Subscription_doc_user_key:UNIQUE,'
                                   'Subscription_user_fkey:FOREIGN KEY,Team_org_fkey:FOREIGN KEY,Team_org_role_key:UNIQUE'), constraints
            fk_rules = sql('''SELECT string_agg(constraint_name || ':' || delete_rule, ',' ORDER BY constraint_name)
                FROM information_schema.referential_constraints WHERE constraint_schema = 'public';''', DATABASE)
            assert fk_rules == ('Doc_createdBy_fkey:RESTRICT,Doc_org_fkey:RESTRICT,Membership_org_fkey:RESTRICT,'
                                'Membership_team_fkey:RESTRICT,Membership_user_fkey:RESTRICT,Notification_doc_fkey:RESTRICT,'
                                'Notification_recipient_fkey:RESTRICT,Notification_subscription_fkey:RESTRICT,'
                                'Subscription_doc_fkey:RESTRICT,Subscription_user_fkey:RESTRICT,'
                                'Team_org_fkey:RESTRICT'), fk_rules
            proc = subprocess.Popen([str(BACKEND / '.lake/build/bin/teamDocs'), str(PORT)], env=env,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            nyxis_local.wait_ready(proc, lambda: request('GET', '/health')[0] == 200, 'teamDocs')
            status, body, headers = request('GET', '/health')
            assert status == 200 and body == 'ok'
            checks += 1
            verify(Client(tokens), ids, ids['outsider'])
        finally:
            if proc is not None:
                nyxis_local.stop(proc)
            if created:
                sql('DROP DATABASE "' + DATABASE + '";')
            if bucket_created:
                nyxis_local.storage_request('POST', '/storage/v1/bucket/' + BUCKET + '/empty', b'', key=service_key)
                status, _ = nyxis_local.storage_request('DELETE', '/storage/v1/bucket/' + BUCKET, key=service_key)
                assert status == 200, 'local Storage bucket cleanup failed (diagnostics withheld)'
        assert upstream[0] > 50, 'live Auth JWKS relay was skipped'
        assert all(req == ('/auth/v1/.well-known/jwks.json', None, None) for req in trace), \
            'JWKS path/header boundary failed'
        assert len(storage_trace) >= 12 and all(service for _, service in storage_trace), 'Storage signing boundary failed'
        assert all(clean and auth in ('summarizer', 'audit') for (_, _, auth, _, clean) in mock_record), \
            'external API boundary failed (authentication header, Cookie or query string)'
        assert mock_record and edits_announced >= 4, 'external API calls were skipped'
    print(f'check-team-docs: {checks} HTTP + {row_checks} persistent-row/DB-constraint checks; {upstream[0]} HTTPS JWKS requests; '
          f'{len(storage_trace)} signed-URL requests to local Storage; notification mail captured by Mailpit over SMTP; '
          f'{len(mock_record)} requests to the mock external API ({len(mock_requests("/summarizer/"))} sync summaries, '
          f'{len(mock_requests("/audit/"))} audit events delivered from the outbox for {edits_announced} permitted edits); '
          '6 Auth sessions/users, the test DB and the test bucket removed (actual team-docs sample, real Auth JWTs/clock/DB/Storage/SMTP)')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit('check-team-docs interrupted (cleanup attempted)')
    except Exception:
        # Exceptions from URL/SQL/process code can carry credentials; do not print them.
        import traceback
        if os.environ.get('NYXIS_TEAM_DOCS_DEBUG'):
            traceback.print_exc()
        raise SystemExit('check-team-docs failed (diagnostics withheld)')
