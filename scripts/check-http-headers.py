#!/usr/bin/env python3
"""Request summary over real HTTP: the query string and the selected request headers reach the handler,
Authorization and Cookie never do (Authorization only becomes the principal), and responses carry
Content-Type plus the few allowed headers only (invalid values and Set-Cookie are dropped).
Uses the core test server `serveHttpHeaders` (opaque test credentials, no JWT, no database)."""
import http.client
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local  # noqa: E402
PORT = int(os.environ.get('NYXIS_HTTP_HEADERS_PORT', '18114'))
checks = 0


def request(method, path, body=b'', headers=()):
    conn = http.client.HTTPConnection('127.0.0.1', PORT, timeout=10)
    try:
        conn.putrequest(method, path, skip_accept_encoding=True)
        conn.putheader('Content-Length', str(len(body)))
        for key, value in headers:
            conn.putheader(key, value)
        conn.endheaders(body)
        res = conn.getresponse()
        return res.status, res.read().decode('utf-8'), [(k.lower(), v) for k, v in res.getheaders()]
    finally:
        conn.close()


def values(headers, name):
    return [v for k, v in headers if k == name]


def expect(method, path, status, body=b'', headers=(), content_type='text/plain; charset=utf-8'):
    global checks
    got, text, response_headers = request(method, path, body, headers)
    assert got == status, (method, path, got, status, text)
    assert values(response_headers, 'content-type') == [content_type], (path, response_headers)
    for forbidden in ('set-cookie', 'authorization', 'cookie', 'x-principal'):
        assert values(response_headers, forbidden) == [], (path, forbidden, response_headers)
    checks += 1
    return text, response_headers


def lines(text):
    out = {}
    for line in text.split('\n'):
        key, _, value = line.partition('=')
        out[key] = value
    return out


nyxis_local.require_free_port(PORT)
proc = subprocess.Popen([str(ROOT / '.lake/build/bin/serveHttpHeaders'), str(PORT)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
try:
    nyxis_local.wait_ready(proc, lambda: request('GET', '/health')[0] == 200)
    expect('GET', '/health?x=1', 200)

    sent = [('Authorization', 'Bearer test-alice'), ('Cookie', 'session=secret-cookie'),
            ('Accept', 'application/json'), ('ACCEPT', 'text/html'), ('Content-Type', 'text/plain'),
            ('If-None-Match', '"v1"'), ('If-Match', '"v2"'), ('Accept-Language', 'ja'),
            ('X-Principal', 'root'), ('Proxy-Authorization', 'Basic c2VjcmV0'), ('Set-Cookie', 'a=b')]
    text, response_headers = expect('GET', '/echo?x=1&name=a%20b+c&flag', 200, headers=sent,
                                    content_type='application/json')
    got = lines(text)
    assert got['principal'] == 'User::alice', got
    assert got['query'] == 'x=1&name=a%20b+c&flag', got
    assert got['params'] == 'x=1;name=a b c;flag=', got
    assert got['headers'] == ('accept=application/json;accept=text/html;content-type=text/plain;'
                              'if-none-match="v1";if-match="v2";accept-language=ja'), got
    assert got['body'] == '', got
    lowered = text.lower()
    for leaked in ('test-alice', 'secret', 'cookie', 'authorization', 'x-principal', 'root', 'bearer', 'host'):
        assert leaked not in lowered, (leaked, text)
    assert values(response_headers, 'etag') == ['"v1"'], response_headers
    assert values(response_headers, 'cache-control') == ['no-store'], response_headers
    checks += 1

    # Cookie alone never becomes a principal and never reaches the handler.
    text, _ = expect('GET', '/echo', 200, headers=[('Cookie', 'auth=test-alice'), ('Accept', '*/*')],
                     content_type='application/json')
    got = lines(text)
    assert got['principal'] == 'anonymous' and got['headers'] == 'accept=*/*' and got['query'] == '', got
    assert 'test-alice' not in text, text
    checks += 1

    # Body and Content-Type of a POST reach the handler; the authenticated principal is the test root.
    text, _ = expect('POST', '/echo?limit=10', 200, body=b'{"a":1}',
                     headers=[('Content-Type', 'application/json'), ('Authorization', 'Bearer test-root')],
                     content_type='application/json')
    got = lines(text)
    assert got['principal'] == 'User::root' and got['body'] == '{"a":1}', got
    assert got['headers'] == 'content-type=application/json' and got['params'] == 'limit=10', got
    checks += 1

    # Injection attempts: invalid Content-Type/ETag are dropped (default Content-Type returns),
    # Set-Cookie never appears, only the valid Location remains.
    _, response_headers = expect('GET', '/inject', 201)
    assert values(response_headers, 'location') == ['/echo'], response_headers
    assert values(response_headers, 'etag') == [], response_headers
    assert values(response_headers, 'cache-control') == [], response_headers
    assert not any(k == 'set-cookie' or 'set-cookie' in v.lower() for k, v in response_headers), response_headers
    checks += 1

    _, response_headers = expect('GET', '/plain', 200)
    for name in ('etag', 'cache-control', 'location'):
        assert values(response_headers, name) == [], response_headers
    checks += 1

    # The principal comes from Authorization alone: the authorization layer sees alice, the handler does not.
    expect('GET', '/posts/draft1', 200, headers=[('Authorization', 'Bearer test-alice')])
    expect('GET', '/posts/draft1', 403)
    expect('GET', '/posts/draft1', 403, headers=[('Cookie', 'auth=test-alice'), ('X-Principal', 'alice')])
    expect('GET', '/posts/draft1', 403, headers=[('Authorization', 'Bearer unknown')])
    expect('GET', '/nope?x=1', 404)
    # Std.Http itself rejects malformed percent-encoding in the request line before nyxis runs.
    status, _, _ = request('GET', '/echo?bad=%zz')
    assert status == 400, status
    checks += 1
finally:
    nyxis_local.stop(proc)
print(f'check-http-headers: {checks} HTTP checks passed (query string, selected request headers, allowed response headers; opaque credentials, no JWT/Supabase)')
