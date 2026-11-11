#!/usr/bin/env python3
"""Check that the official sample and its READMEs offer no password-based sign-up or sign-in.

Supabase Auth cannot disable password sign-up/sign-in on its own while the email provider
(magic link / one-time code) is enabled, so nyxis does not ask the Auth REST API to reject
passwords. Instead the official frontend and the READMEs must not use or describe a password
path. This script greps the frontend sources (app/, components/, lib/, tests/) and the READMEs
for `grant_type=password`, `signInWithPassword`, `signUp`, a password input (`type="password"`)
and the word "password" outside "passwordless" (case-insensitive). Exit 0 when none is found.

Run from the repository root: python3 -B scripts/check-no-password-auth.py
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "examples/bulletin-board/frontend"
SOURCE_DIRS = ["app", "components", "lib", "tests"]
SOURCE_SUFFIXES = {".ts", ".tsx", ".js", ".jsx", ".cjs", ".mjs", ".css", ".json", ".md"}
READMES = ["examples/bulletin-board/README.md", "README.md", "README.ja.md"]

PATTERNS = [
    ("grant_type=password", re.compile(r"grant_type=password")),
    ("signInWithPassword", re.compile(r"signInWithPassword")),
    ("signUp", re.compile(r"\bsignUp\b")),
    ('type="password"', re.compile(r"""type\s*=\s*["']password["']""")),
    ("password (not passwordless)", re.compile(r"password(?!less)", re.IGNORECASE)),
]


def files() -> list[Path]:
    out: list[Path] = []
    for name in SOURCE_DIRS:
        base = FRONTEND / name
        if not base.is_dir():
            raise SystemExit("missing frontend directory: %s" % base.relative_to(ROOT))
        out.extend(p for p in sorted(base.rglob("*")) if p.is_file() and p.suffix in SOURCE_SUFFIXES)
    for name in READMES:
        p = ROOT / name
        if not p.is_file():
            raise SystemExit("missing README: %s" % name)
        out.append(p)
    return out


def main() -> int:
    hits = 0
    scanned = files()
    for path in scanned:
        text = path.read_text(encoding="utf-8", errors="replace")
        for lineno, line in enumerate(text.splitlines(), 1):
            for label, pattern in PATTERNS:
                if pattern.search(line):
                    hits += 1
                    print("FAIL %s:%d [%s] %s" % (path.relative_to(ROOT), lineno, label, line.strip()[:160]))
    print("scanned %d files; %d hits" % (len(scanned), hits))
    if hits:
        return 1
    print("no password sign-up/sign-in path in the official sample or the READMEs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
