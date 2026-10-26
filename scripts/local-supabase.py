#!/usr/bin/env python3
"""Prepare local Supabase; --exec COMMAND passes credentials without writing them."""
import json
import os
from pathlib import Path
import shutil
import shlex
import signal
import subprocess
import sys
import time
from urllib.parse import urlsplit
from urllib.request import ProxyHandler, build_opener

ROOT = Path(__file__).resolve().parent.parent
ENV = os.environ.copy()
# Never target a remote Docker daemon, even if the caller selected one.
ENV.pop("DOCKER_HOST", None)
ENV.pop("DOCKER_TLS_VERIFY", None)
ENV.pop("DOCKER_CERT_PATH", None)
ENV["DOCKER_CONTEXT"] = "desktop-linux"
DEADLINE = time.monotonic() + 540


def interrupted(_signal, _frame):
    raise KeyboardInterrupt


def fail(message):
    print("local-supabase: " + message, file=sys.stderr, flush=True)
    raise SystemExit(75)


def say(message):
    print("local-supabase: " + message, flush=True)


def cloud_environment():
    """Read only the two cloud inputs, without executing shell expansions."""
    names = ("NYXIS_SUPABASE_URL", "NYXIS_SUPABASE_ANON_KEY")
    values = {name: os.environ[name] for name in names if name in os.environ}
    path = ROOT / ".env"
    if path.exists():
        try:
            for line in path.read_text().splitlines():
                line = line.strip()
                if line.startswith("export "):
                    line = line[7:].strip()
                name, sep, raw = line.partition("=")
                name = name.strip()
                if name not in names:
                    continue
                parts = shlex.split(raw, comments=True)
                if not sep or len(parts) != 1:
                    raise ValueError
                values[name] = parts[0]
        except (ValueError, UnicodeError, OSError):
            fail("cannot read cloud settings in .env (contents withheld).")
    if not values:
        return None
    try:
        url = urlsplit(values[names[0]])
        if (url.scheme != "https" or not url.hostname or
                not url.hostname.endswith(".supabase.co") or
                url.username or url.password or url.port not in (None, 443) or
                url.path not in ("", "/") or url.query or url.fragment or
                not values[names[1]]):
            raise ValueError
    except (KeyError, ValueError):
        fail("cloud settings require a Supabase HTTPS project URL and anon key (values withheld).")
    values[names[0]] = values[names[0]].rstrip("/")
    return values


def run(argv, timeout=30, check=True):
    remaining = min(timeout, DEADLINE - time.monotonic())
    if remaining <= 0:
        fail("preparation deadline exceeded; retry after checking Docker.")
    # Capture output: Supabase prints credentials even on normal startup.
    proc = subprocess.Popen(argv, cwd=ROOT, env=ENV, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=remaining)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
        fail(argv[0] + " timed out or was interrupted; output withheld (may contain secrets).")
    if check and proc.returncode:
        fail(argv[0] + " failed (exit " + str(proc.returncode) +
             "); inspect it locally. Output withheld (may contain secrets).")
    return proc.returncode, out


def status():
    _, raw = run(["supabase", "status", "--output", "json"])
    try:
        data = json.loads(raw)
        db = urlsplit(data["DB_URL"])
        api = urlsplit(data["API_URL"])
        if (db.scheme not in ("postgres", "postgresql") or
                db.hostname not in ("127.0.0.1", "localhost", "::1") or
                db.port != 55322 or db.path != "/postgres" or
                api.scheme != "http" or api.hostname != "127.0.0.1" or
                api.port != 55321 or api.username or api.password):
            fail("unexpected local service endpoints; check supabase/config.toml.")
        return data
    except (ValueError, KeyError, TypeError):
        fail("invalid Supabase status response (contents withheld).")


def main():
    execute = len(sys.argv) > 2 and sys.argv[1] == "--exec"
    cloud_execute = len(sys.argv) > 2 and sys.argv[1] == "--exec-cloud"
    if len(sys.argv) != 1 and not (execute or cloud_execute):
        fail("usage: scripts/local-supabase.py [--exec|--exec-cloud COMMAND ARG ...]")
    if not execute:
        cloud = cloud_environment()
        if cloud_execute:
            if cloud is None:
                fail("set NYXIS_SUPABASE_URL and NYXIS_SUPABASE_ANON_KEY in .env.")
            child_env = os.environ.copy()
            child_env.update(cloud)
            os.chdir(ROOT)
            os.execvpe(sys.argv[2], sys.argv[2:], child_env)
        if cloud:
            say("cloud settings loaded; use scripts/local-supabase.py --exec-cloud COMMAND for cloud checks. Values withheld; connectivity not yet verified.")
    for tool in ("docker", "supabase"):
        if not shutil.which(tool):
            fail(tool + " is missing from PATH.")
    if not (ROOT / "supabase/config.toml").is_file():
        fail("restore the committed supabase/config.toml (this script never runs supabase init).")
    _, raw_context = run(["docker", "context", "inspect", "desktop-linux"])
    try:
        endpoint = json.loads(raw_context)[0]["Endpoints"]["docker"]["Host"]
        if not endpoint.startswith("unix:///"):
            fail("desktop-linux must use a local Unix socket.")
    except (ValueError, KeyError, IndexError, TypeError):
        fail("cannot identify the local Docker Desktop endpoint.")
    if not execute:
        if sys.platform != "darwin":
            fail("this script expects macOS Docker Desktop (desktop-linux context).")
        if run(["docker", "info"], check=False)[0]:
            say("starting Docker Desktop...")
            run(["open", "-a", "Docker"])
            until = time.monotonic() + 120
            while run(["docker", "info"], timeout=10, check=False)[0]:
                if time.monotonic() >= until:
                    fail("Docker did not become ready within 120 seconds.")
                time.sleep(2)
        say("starting/checking local Supabase (first image download can take several minutes)...")
        run(["supabase", "start"], timeout=400)
    data = status()
    if execute:
        child_env = os.environ.copy()
        child_env["NYXIS_DATABASE_URL"] = data["DB_URL"]
        child_env["NYXIS_SUPABASE_URL"] = data["API_URL"]
        for source, target in (("ANON_KEY", "NYXIS_SUPABASE_ANON_KEY"),
                               ("SERVICE_ROLE_KEY", "NYXIS_SUPABASE_SERVICE_ROLE_KEY")):
            child_env.pop(target, None)
            if source in data:
                child_env[target] = data[source]
        os.chdir(ROOT)
        os.execvpe(sys.argv[2], sys.argv[2:], child_env)
    # Actual SQL, rather than just a socket or container existence check.
    _, result = run(["docker", "exec", "supabase_db_nyxis", "psql", "-U", "postgres",
                     "-d", "postgres", "-Atqc", "SELECT 1"])
    if result.strip() != b"1":
        fail("local PostgreSQL query failed.")
    try:
        opener = build_opener(ProxyHandler({}))
        for path in ("/auth/v1/health", "/auth/v1/.well-known/jwks.json"):
            with opener.open(data["API_URL"] + path, timeout=10) as response:
                if response.status != 200:
                    fail("local Auth health check failed.")
    except Exception:
        fail("local Auth/JWKS HTTP check failed.")
    say("ready: PostgreSQL SELECT 1 and Auth/JWKS HTTP checks passed; no application data changed.")


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, interrupted)
    try:
        main()
    except KeyboardInterrupt:
        fail("preparation interrupted.")
    except OSError:
        fail("local command or service unavailable; check Docker, Supabase and PATH.")
