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
import types
import unittest
from unittest.mock import patch

if not __debug__:
    raise SystemExit('assertions disabled')
HOOK = Path(__file__).resolve().parent / "local-supabase.py"
namespace = runpy.run_path(str(HOOK))
scope = namespace["status"].__globals__
SECRET = "not-for-logs"
sys.path.insert(0, str(HOOK.parent))
import nyxis_docker
import nyxis_local

DAEMON = ("DOCKER_HOST", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH")
# A caller whose shell targets a remote daemon; none of it may reach a Docker command.
CALLER = {"DOCKER_HOST": "tcp://203.0.113.1:2375", "DOCKER_TLS": "1", "DOCKER_TLS_VERIFY": "1",
          "DOCKER_CERT_PATH": "/caller/certs", "DOCKER_CONTEXT": "caller-remote"}
NOT_UNIX = ("tcp://203.0.113.1:2375", "ssh://user@203.0.113.1", "npipe:////./pipe/docker_engine",
            "unix://relative.sock", "http://127.0.0.1:2375", "", "tcp://" + SECRET + ":2375")


def inspect(name, host):
    """`docker context inspect NAME` output, in the shape the Docker CLI prints."""
    return json.dumps([{"Name": name, "Metadata": {},
                        "Endpoints": {"docker": {"Host": host, "SkipTLSVerify": False}}}]).encode()


def load(environ):
    """The globals of a fresh copy of the hook, imported as if called from a shell with exactly `environ`."""
    with patch.dict("os.environ", environ, clear=True):
        return runpy.run_path(str(HOOK))["main"].__globals__


class FakeDocker:
    """Answers the hook's commands without Docker; records each one with the ENV it ran under."""

    def __init__(self, hook, hosts=None, info=(0,)):
        self.hook, self.calls, self.info = hook, [], list(info)
        self.hosts = {"default": "unix:///var/run/docker.sock",
                      "desktop-linux": "unix:///Users/u/.docker/run/docker.sock"} if hosts is None else hosts

    def __call__(self, argv, timeout=30, check=True):
        self.calls.append((list(argv), dict(self.hook["ENV"])))
        if argv[:3] == ["docker", "context", "inspect"]:
            host = self.hosts.get(argv[3])
            if host is None:
                return 1, b""
            return 0, host if isinstance(host, bytes) else inspect(argv[3], host)
        if argv[0] == "docker" and argv[3] == "info":
            return (self.info.pop(0) if len(self.info) > 1 else self.info[0]), b""
        if argv[0] == "docker" and argv[3] == "exec":
            return 0, b"1\n"
        if argv[:2] == ["supabase", "status"]:
            return 0, json.dumps({"DB_URL": "postgresql://postgres:postgres@127.0.0.1:55322/postgres",
                                  "API_URL": "http://127.0.0.1:55321", "SERVICE_ROLE_KEY": SECRET}).encode()
        return 0, b""


class Healthy:
    status = 200

    def __enter__(self):
        return self

    def __exit__(self, *_):
        return False


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
            return 0, inspect(argv[-1], "unix:///tmp/docker.sock")
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
        calls = []
        def fake_run(argv, **kwargs):
            calls.append(argv)
            return 0, inspect(argv[-1], "tcp://remote:2375")
        with patch.dict(scope, run=fake_run), \
             patch.object(sys, "argv", [str(HOOK)]), \
             patch("shutil.which", return_value="/bin/tool"), \
             contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as result:
                namespace["main"]()
        self.assertEqual(result.exception.code, 75)
        self.assertIn("must use a local Unix socket", err.getvalue())
        self.assertEqual([argv[:3] for argv in calls], [["docker", "context", "inspect"]])


class DockerContextChecks(unittest.TestCase):
    """The wrapper, its --exec child and the checks use one checked local context (no Docker needed)."""

    def run_hook(self, args, platform="linux", environ=CALLER, **fake):
        """Run the hook's main() with only `environ` and a checkout holding just supabase/config.toml."""
        hook = load(environ)
        docker = FakeDocker(hook, **fake)
        opener = lambda *_: types.SimpleNamespace(open=lambda *a, **k: Healthy())
        with tempfile.TemporaryDirectory() as directory, \
             patch.dict(hook, run=docker, build_opener=opener, ROOT=Path(directory)), \
             patch.dict("os.environ", environ, clear=True), \
             patch("subprocess.Popen", side_effect=AssertionError("no real commands")), \
             patch.object(sys, "platform", platform), \
             patch.object(sys, "argv", [str(HOOK)] + args), \
             patch("shutil.which", return_value="/bin/tool"), patch("os.chdir"), \
             patch("os.execvpe", side_effect=SystemExit(0)) as execute, \
             contextlib.redirect_stdout(io.StringIO()) as out, \
             contextlib.redirect_stderr(io.StringIO()) as err:
            (Path(directory) / "supabase").mkdir()
            (Path(directory) / "supabase/config.toml").touch()
            try:
                hook["main"]()
                code = None
            except SystemExit as result:
                code = result.code
        return code, docker.calls, execute, out.getvalue() + err.getvalue()

    def test_context_selection_ignores_the_callers_daemon(self):
        for platform, environ, expected in (
                ("darwin", {}, "desktop-linux"), ("linux", {}, "default"),
                ("darwin", CALLER, "desktop-linux"), ("linux", CALLER, "default"),
                ("linux", {"NYXIS_DOCKER_CONTEXT": ""}, "default"),
                ("linux", dict(CALLER, NYXIS_DOCKER_CONTEXT="rootless"), "rootless"),
                ("darwin", {"NYXIS_DOCKER_CONTEXT": "colima"}, "colima")):
            with self.subTest(platform=platform, environ=environ), patch.object(sys, "platform", platform):
                env = dict(environ, DOCKER_CONFIG="/caller/config", UNRELATED="kept")
                self.assertEqual(nyxis_docker.context(env), expected)
                scrubbed = nyxis_local.scrub_docker_env(dict(env))
                self.assertEqual(scrubbed["DOCKER_CONTEXT"], expected)
                self.assertFalse(set(DAEMON) & set(scrubbed))
                self.assertEqual((scrubbed["DOCKER_CONFIG"], scrubbed["UNRELATED"]), ("/caller/config", "kept"))

    def test_invalid_context_name_stops_before_any_command(self):
        for name in ("-H", "--host=tcp://" + SECRET, "tcp://203.0.113.1:2375", "a", SECRET + " x",
                     "../" + SECRET, SECRET + "\n", "default;" + SECRET):
            with self.subTest(name=name):
                with self.assertRaises(ValueError):
                    nyxis_docker.context({"NYXIS_DOCKER_CONTEXT": name})
                code, calls, execute, output = self.run_hook([], environ={"NYXIS_DOCKER_CONTEXT": name})
                self.assertEqual((code, calls), (75, []))
                self.assertNotIn(SECRET, output)
                with self.assertRaises(SystemExit) as result:  # a check script run directly
                    nyxis_local.scrub_docker_env({"NYXIS_DOCKER_CONTEXT": name})
                self.assertNotIn(SECRET, str(result.exception.code))

    def test_only_that_context_on_a_unix_socket_is_accepted(self):
        good = inspect("default", "unix:///var/run/docker.sock")
        self.assertEqual(nyxis_docker.unix_endpoint(good, "default"), "unix:///var/run/docker.sock")
        entry = json.loads(good)[0]
        broken = [inspect("default", host) for host in NOT_UNIX] + [
            inspect("other", "unix:///var/run/docker.sock"), json.dumps([entry, entry]).encode(),
            b"[]", b"{}", b"null", b'"unix:///var/run/docker.sock"', b"not json", b"\xff",
            json.dumps([{"Name": "default"}]).encode(),
            json.dumps([{"Name": "default", "Endpoints": None}]).encode(),
            json.dumps([{"Name": "default", "Endpoints": {"docker": {}}}]).encode(),
            json.dumps([{"Name": "default", "Endpoints": {"docker": {"Host": None}}}]).encode(),
            json.dumps([{"Name": "default", "Endpoints": {"docker": {"Host": 1}}}]).encode(),
            json.dumps([{"Endpoints": entry["Endpoints"]}]).encode()]
        for raw in broken:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                nyxis_docker.unix_endpoint(raw, "default")

    def test_linux_start_pins_the_checked_context(self):
        code, calls, _, output = self.run_hook([])
        self.assertIsNone(code)
        self.assertIn("ready:", output)
        commands = [argv for argv, _ in calls]
        self.assertEqual(commands[:2], [["docker", "context", "inspect", "default"],
                                        ["docker", "--context", "default", "info"]])
        self.assertIn(["supabase", "start"], commands)
        self.assertIn(["docker", "--context", "default", "exec", "supabase_db_nyxis",
                       "psql", "-U", "postgres", "-d", "postgres", "-Atqc", "SELECT 1"], commands)
        for argv, env in calls:
            self.assertIn(argv[0], ("docker", "supabase"))
            if argv[0] == "docker" and argv[1] != "context":
                self.assertEqual(argv[1:3], ["--context", "default"])
            self.assertEqual(env["DOCKER_CONTEXT"], "default")
            self.assertFalse(set(DAEMON) & set(env))
            # The Docker/Supabase command environment never receives the local credentials.
            self.assertNotIn(SECRET, json.dumps(env))

    def test_linux_never_starts_a_daemon(self):
        code, calls, _, output = self.run_hook([], info=(1,))
        self.assertEqual(code, 75)
        self.assertEqual([argv for argv, _ in calls], [["docker", "context", "inspect", "default"],
                                                       ["docker", "--context", "default", "info"]])
        self.assertIn("not reachable", output)

    def test_macos_still_starts_only_docker_desktop(self):
        code, calls, _, _ = self.run_hook([], platform="darwin", environ={}, info=(1, 0))
        self.assertIsNone(code)
        commands = [argv for argv, _ in calls]
        self.assertEqual(commands[:4], [["docker", "context", "inspect", "desktop-linux"],
                                        ["docker", "--context", "desktop-linux", "info"],
                                        ["open", "-a", "Docker"],
                                        ["docker", "--context", "desktop-linux", "info"]])
        self.assertIn(["supabase", "start"], commands)
        code, calls, _, _ = self.run_hook([], platform="darwin", environ={"NYXIS_DOCKER_CONTEXT": "colima"},
                                          hosts={"colima": "unix:///Users/u/.colima/docker.sock"}, info=(1,))
        self.assertEqual(code, 75)
        self.assertNotIn(["open", "-a", "Docker"], [argv for argv, _ in calls])

    def test_unusable_context_stops_before_supabase(self):
        cases = [{"default": host} for host in NOT_UNIX] + [
            {}, {"default": b"not json"}, {"default": b"[]"}, {"default": inspect("other", "unix:///x.sock")}]
        for args in ([], ["--exec", "sample"]):
            for hosts in cases:
                with self.subTest(args=args, hosts=hosts):
                    code, calls, execute, output = self.run_hook(args, hosts=hosts)
                    self.assertEqual(code, 75)
                    self.assertEqual([argv for argv, _ in calls], [["docker", "context", "inspect", "default"]])
                    execute.assert_not_called()
                    self.assertNotIn(SECRET, output)

    def test_exec_child_gets_the_checked_settings_and_credentials(self):
        for environ, expected in ((CALLER, "default"), (dict(CALLER, NYXIS_DOCKER_CONTEXT="rootless"), "rootless")):
            with self.subTest(expected=expected):
                code, calls, execute, _ = self.run_hook(["--exec", "sample", "8080"], environ=environ,
                                                        hosts={expected: "unix:///run/user/1000/docker.sock"})
                self.assertEqual(code, 0)
                self.assertEqual([argv for argv, _ in calls], [["docker", "context", "inspect", expected],
                                                               ["supabase", "status", "--output", "json"]])
                command, argv, child = execute.call_args.args
                self.assertEqual((command, argv), ("sample", ["sample", "8080"]))
                self.assertEqual(child["DOCKER_CONTEXT"], expected)
                self.assertFalse(set(DAEMON) & set(child))
                self.assertEqual(child["NYXIS_SUPABASE_SERVICE_ROLE_KEY"], SECRET)
                # A check started by the child selects the same context from what it inherits.
                with patch.object(sys, "platform", "linux"):
                    self.assertEqual(nyxis_local.scrub_docker_env(dict(child))["DOCKER_CONTEXT"], expected)
                for _, env in calls:
                    self.assertNotIn(SECRET, json.dumps(env))

    def test_unsupported_platform_stops_before_any_command(self):
        for args in ([], ["--exec", "sample"]):
            with self.subTest(args=args):
                code, calls, execute, _ = self.run_hook(args, platform="win32")
                self.assertEqual((code, calls), (75, []))
                execute.assert_not_called()

    def test_cloud_exec_needs_no_docker_settings(self):
        hook = load({})
        cloud = {"NYXIS_SUPABASE_URL": "https://example.supabase.co", "NYXIS_SUPABASE_ANON_KEY": SECRET,
                 "NYXIS_DOCKER_CONTEXT": "--host=tcp://203.0.113.1"}
        with tempfile.TemporaryDirectory() as directory, \
             patch.dict(hook, ROOT=Path(directory), run=lambda *a, **k: self.fail("Docker not needed")), \
             patch("subprocess.Popen", side_effect=AssertionError("no real commands")), \
             patch.dict("os.environ", cloud, clear=True), patch.object(sys, "platform", "win32"), \
             patch.object(sys, "argv", [str(HOOK), "--exec-cloud", "sample"]), patch("os.chdir"), \
             patch("os.execvpe", side_effect=SystemExit(0)) as execute, \
             patch("shutil.which", side_effect=AssertionError("Docker not needed")):
            with self.assertRaises(SystemExit):
                hook["main"]()
        self.assertEqual(execute.call_args.args[2]["NYXIS_SUPABASE_ANON_KEY"], SECRET)

    def test_checks_inspect_the_pinned_context(self):
        with patch.object(sys, "platform", "linux"):
            env = nyxis_local.scrub_docker_env(dict(CALLER))
        for returncode, raw, accepted in ((0, inspect("default", "unix:///var/run/docker.sock"), True),
                                          (0, inspect("default", "tcp://203.0.113.1:2375"), False),
                                          (0, inspect("other", "unix:///var/run/docker.sock"), False),
                                          (0, b"not json", False), (1, b"", False)):
            seen = []
            def fake(argv, **kwargs):
                seen.append((argv, kwargs["env"]))
                return subprocess.CompletedProcess(argv, returncode, raw, b"")
            with self.subTest(raw=raw, returncode=returncode), patch("subprocess.run", fake):
                if accepted:
                    nyxis_local.require_local_docker(env)
                else:
                    with self.assertRaises(AssertionError):
                        nyxis_local.require_local_docker(env)
                self.assertEqual(seen, [(["docker", "context", "inspect", "default"], env)])

    def test_no_script_hard_codes_a_context(self):
        for path in sorted([*HOOK.parent.glob("*.py"), *HOOK.parent.glob("*.sh")]):
            if path.name not in ("nyxis_docker.py", Path(__file__).name):
                with self.subTest(path=path.name):
                    self.assertNotIn("desktop-linux", path.read_text())


if __name__ == "__main__":
    unittest.main()
