import http.server
import os
from pathlib import Path
import ssl
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import nyxis_local
binary = ROOT / '.lake/build/bin/checkJwksFetch'

with tempfile.TemporaryDirectory(prefix='nyxis-jwks-probe-') as tmp, \
        nyxis_local.tls_material('nyxis-jwks-probe-') as (cert, key):
    root = Path(tmp)
    state = {'mode': 'ok', 'requests': 0}
    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.1'
        def log_message(self, *args):
            pass
        def do_GET(self):
            state['requests'] += 1
            assert self.path == '/auth/v1/.well-known/jwks.json'
            assert self.headers.get('Authorization') is None
            assert self.headers.get('Cookie') is None
            mode = state['mode']
            try:
                if mode == 'slow':
                    # Far beyond curl's 5-second --max-time: an honoured deadline (about 5 s) stays
                    # distinguishable from a served response even on slow or emulated hosts.
                    time.sleep(20)
                if mode == 'redirect':
                    self.send_response(302)
                    self.send_header('Location', '/redirect-target')
                    self.send_header('Content-Length', '0')
                    self.end_headers()
                    return
                status = 503 if mode == 'error' else 200
                body = b'x' * 65537 if mode in ('large', 'chunked') else b'{"keys":[]}'
                if mode == 'empty': body = b''
                if mode == 'utf8': body = b'\xff'
                if mode == 'boundary': body = b'x' * 65536
                if mode == 'created': status = 201
                self.send_response(status)
                if mode == 'chunked':
                    self.send_header('Transfer-Encoding', 'chunked')
                    self.end_headers()
                    for start in range(0, len(body), 1024):
                        chunk = body[start:start + 1024]
                        self.wfile.write(f'{len(chunk):x}\r\n'.encode() + chunk + b'\r\n')
                    self.wfile.write(b'0\r\n\r\n')
                else:
                    self.send_header('Content-Length', str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError, ssl.SSLError):
                pass
    with nyxis_local.tls_server(Handler, cert, key) as server:
        port = server.server_port
        # Poison a task-specific curl config; --disable must suppress it.
        (root / '.curlrc').write_text('insecure\nlocation\n')
        env = os.environ.copy()
        env['CURL_HOME'] = str(root)
        for name in ('CURL_CA_BUNDLE', 'SSL_CERT_FILE', 'SSL_CERT_DIR'):
            env.pop(name, None)
        def probe(name, mode, expected, *, trusted=True, host='localhost', scheme='https'):
            state['mode'] = mode
            before = state['requests']
            started = time.monotonic()
            child_env = env.copy()
            if trusted:
                child_env['CURL_CA_BUNDLE'] = str(cert)
            result = subprocess.run([str(binary), f'{scheme}://{host}:{port}/auth/v1'],
                                    capture_output=True, env=child_env, timeout=15)
            elapsed = time.monotonic() - started
            assert result.returncode == 0 and result.stderr == b'', (name, result.returncode)
            assert result.stdout in (b'accepted\n', b'rejected\n'), name
            accepted = result.stdout == b'accepted\n'
            assert accepted == expected, name
            if mode == 'redirect':
                assert state['requests'] - before == 1
            if mode == 'slow':
                assert 4.5 < elapsed < 15, elapsed
            print(f'{name}: accepted={accepted}')
        probe('valid TLS + 200', 'ok', True)
        probe('untrusted certificate (poisoned curlrc ignored)', 'ok', False, trusted=False)
        probe('hostname mismatch', 'ok', False, host='127.0.0.1')
        probe('redirect refused, only one request', 'redirect', False)
        probe('503 refused', 'error', False)
        probe('Content-Length size bound', 'large', False)
        probe('chunked size bound', 'chunked', False)
        probe('deadline', 'slow', False)
        probe('HTTP protocol refused', 'ok', False, scheme='http')
        probe('empty body', 'empty', False)
        probe('invalid UTF-8', 'utf8', False)
        probe('201 refused', 'created', False)
        probe('65536 byte body accepted', 'boundary', True)
        missing_env = env.copy()
        missing_env['PATH'] = str(root / 'absent')
        result = subprocess.run([str(binary), f'https://localhost:{port}/auth/v1'],
                                capture_output=True, env=missing_env, timeout=3)
        assert result.returncode == 0 and result.stdout == b'rejected\n' and result.stderr == b''
        print('14 Lean/curl transport cases passed')
