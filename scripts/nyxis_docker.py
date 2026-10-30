"""The local Docker daemon that local-supabase.py and the local checks use (no side effects on import).

The context is `NYXIS_DOCKER_CONTEXT` when set, else Docker Desktop's `desktop-linux` on macOS and
`default` on Linux, which without DOCKER_HOST is the daemon's own Unix socket. The caller's
DOCKER_HOST, DOCKER_CONTEXT and TLS settings are never used. Callers run every Docker command with the
scrubbed environment and an explicit `--context`, after `docker context inspect` shows a Unix socket.
A Unix socket can still be forwarded to another machine (ssh -L); this cannot detect that.
"""
import json
import re
import sys

# How a caller's shell could pick another daemon; scrub() removes all of them.
CALLER_SETTINGS = ('DOCKER_HOST', 'DOCKER_TLS', 'DOCKER_TLS_VERIFY', 'DOCKER_CERT_PATH', 'DOCKER_CONTEXT')
# Docker's rule for context names; it also keeps the name from being parsed as an option.
CONTEXT_NAME = re.compile(r'[a-zA-Z0-9][a-zA-Z0-9_.+-]+')
DESKTOP = 'desktop-linux'  # Docker Desktop's context on macOS


def context(environ):
    """The selected context name; ValueError when NYXIS_DOCKER_CONTEXT is not a context name."""
    name = environ.get('NYXIS_DOCKER_CONTEXT') or (DESKTOP if sys.platform == 'darwin' else 'default')
    if not CONTEXT_NAME.fullmatch(name):
        raise ValueError('NYXIS_DOCKER_CONTEXT is not a Docker context name')
    return name


def scrub(env):
    """Drop the caller's daemon settings from `env` and pin the selected context; returns `env`."""
    name = context(env)
    for setting in CALLER_SETTINGS:
        env.pop(setting, None)
    env['DOCKER_CONTEXT'] = name
    return env


def unix_endpoint(raw, name):
    """The endpoint in `docker context inspect NAME` output; ValueError unless it is exactly
    that context and its endpoint is a Unix socket."""
    try:
        [entry] = json.loads(raw)
        host = entry['Endpoints']['docker']['Host']
        valid = entry['Name'] == name and isinstance(host, str) and host.startswith('unix:///')
    except (ValueError, TypeError, KeyError):
        valid = False
    if not valid:
        raise ValueError('not a local Unix socket context')
    return host
