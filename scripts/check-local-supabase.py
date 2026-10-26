#!/usr/bin/env python3
"""Credential/endpoint regression checks; no Docker or database mutations."""
import contextlib
import io
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

if not __debug__:
    raise SystemExit('assertions disabled')
HOOK = Path(__file__).resolve().parent / "local-supabase.py"
namespace = runpy.run_path(str(HOOK))
scope = namespace["status"].__globals__
SECRET = "not-for-logs"


class HookChecks(unittest.TestCase):
    def test_cloud_dotenv_refresh_and_exec_without_docker(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / '.env'
            for key in ('first-key', 'second-key'):
                path.write_text('export NYXIS_SUPABASE_URL="https://example.supabase.co"\n'
                                f"NYXIS_SUPABASE_ANON_KEY='{key}' # comment\n"
                                'UNRELATED=$(do-not-execute)\n')
                with patch.dict(scope, ROOT=root), \
                     patch.object(sys, 'argv', [str(HOOK), '--exec-cloud', 'sample']), \
                     patch('os.chdir'), \
                     patch('os.execvpe', side_effect=SystemExit(0)) as execute, \
                     patch('shutil.which', side_effect=AssertionError('Docker not needed')):
                    with self.assertRaises(SystemExit):
                        namespace['main']()
                env = execute.call_args.args[2]
                self.assertEqual(env['NYXIS_SUPABASE_ANON_KEY'], key)
                self.assertEqual(env['NYXIS_SUPABASE_URL'], 'https://example.supabase.co')
                self.assertNotIn('UNRELATED', env)

    def test_bad_cloud_settings_do_not_leak(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for content in (f'NYXIS_SUPABASE_ANON_KEY="{SECRET}\n',
                            f'NYXIS_SUPABASE_URL=http://localhost/{SECRET}\n'):
                (root / '.env').write_text(content)
                with patch.dict(scope, ROOT=root), \
                     patch.dict('os.environ', {}, clear=True), \
                     contextlib.redirect_stderr(io.StringIO()) as err:
                    with self.assertRaises(SystemExit):
                        namespace['cloud_environment']()
                self.assertNotIn(SECRET, err.getvalue())

    def data(self, db="postgresql://postgres:password@127.0.0.1:55322/postgres"):
        return {"DB_URL": db, "API_URL": "http://127.0.0.1:55321",
                "SERVICE_ROLE_KEY": SECRET}

    def status(self, data):
        with patch.dict(scope, run=lambda *a, **k: (0, json.dumps(data).encode())):
            return namespace["status"]()

    def test_local_status(self):
        self.assertEqual(self.status(self.data()), self.data())

    def test_reject_remote_wrong_port_and_database(self):
        for url in ("postgresql://u:secret@remote.test:55322/postgres",
                    "postgresql://u:secret@127.0.0.1:54322/postgres",
                    "postgresql://u:secret@127.0.0.1:55322/production",
                    "https://127.0.0.1:55322/postgres"):
            with self.subTest(url=url), contextlib.redirect_stderr(io.StringIO()) as err:
                with self.assertRaises(SystemExit) as result:
                    self.status(self.data(url))
                self.assertEqual(result.exception.code, 75)
                self.assertNotIn("secret", err.getvalue())

    def test_invalid_status_is_private(self):
        with patch.dict(scope, run=lambda *a, **k: (0, SECRET.encode())):
            with contextlib.redirect_stderr(io.StringIO()) as err:
                with self.assertRaises(SystemExit):
                    namespace["status"]()
            self.assertNotIn(SECRET, err.getvalue())

    def test_failed_command_hides_both_streams(self):
        with contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as result:
                namespace["run"]([sys.executable, "-c",
                    "import sys; print('not-for-logs'); print('not-for-logs', file=sys.stderr); sys.exit(9)"])
        self.assertEqual(result.exception.code, 75)
        self.assertNotIn(SECRET, err.getvalue())
        self.assertIn("exit 9", err.getvalue())

    def test_timeout_is_bounded(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as result:
                namespace["run"]([sys.executable, "-c", "import time; time.sleep(30)"], timeout=0.05)
        self.assertEqual(result.exception.code, 75)

    def test_exec_passes_credentials_only_in_environment(self):
        calls = []
        def fake_run(argv, **kwargs):
            calls.append(argv)
            return 0, b'[{"Endpoints":{"docker":{"Host":"unix:///tmp/docker.sock"}}}]'
        with patch.dict(scope, run=fake_run, status=lambda: self.data()), \
             patch.object(sys, "argv", [str(HOOK), "--exec", "sample", "8080"]), \
             patch("shutil.which", return_value="/bin/tool"), \
             patch("os.chdir"), patch("os.execvpe", side_effect=SystemExit(0)) as execute:
            with self.assertRaises(SystemExit):
                namespace["main"]()
        command, argv, env = execute.call_args.args
        self.assertEqual((command, argv), ("sample", ["sample", "8080"]))
        self.assertEqual(env["NYXIS_DATABASE_URL"], self.data()["DB_URL"])
        self.assertEqual(env["NYXIS_SUPABASE_SERVICE_ROLE_KEY"], SECRET)
        self.assertFalse(any("start" in command for command in calls))

    def test_remote_docker_context_rejected(self):
        with patch.dict(scope, run=lambda *a, **k: (0, b'[{"Endpoints":{"docker":{"Host":"tcp://remote:2375"}}}]')), \
             patch.object(sys, "argv", [str(HOOK)]), \
             patch("shutil.which", return_value="/bin/tool"), \
             contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as result:
                namespace["main"]()
        self.assertEqual(result.exception.code, 75)


if __name__ == "__main__":
    unittest.main()
