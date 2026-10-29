#!/usr/bin/env python3
"""Check that every commit in a range carries a Developer Certificate of Origin sign-off.

    python3 scripts/check-dco.py <range>...        e.g.  base..head
    python3 scripts/check-dco.py -C <repo> <range>
    python3 scripts/check-dco.py --self-test       regression check against throwaway git fixtures

A commit passes when its message contains a trailer line of the form
`Signed-off-by: Name <email>`. Merge commits are skipped (they carry no authored
change of their own). Exit 0 when every commit in the range passes, exit 1 when at
least one commit lacks the trailer (each offending commit is listed), exit 2 on usage
or git errors. Only the standard library and the `git` command are used.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

SIGNOFF = re.compile(r"^Signed-off-by: \S.* <[^<>@\s]+@[^<>@\s]+>\s*$", re.MULTILINE)
RECORD = "%H%x1f%P%x1f%s%x1f%B%x1e"


def git(repo, *args):
    p = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(p.stderr.strip() or f"git {' '.join(args)} failed")
    return p.stdout


def commits(repo, ranges):
    out = git(repo, "log", f"--format={RECORD}", *ranges)
    result = []
    for record in out.split("\x1e"):
        if not record.strip():
            continue
        sha, parents, subject, body = record.lstrip("\n").split("\x1f", 3)
        result.append((sha, parents.split(), subject, body))
    return result


def check(repo, ranges):
    """Return the list of (sha, subject) without a sign-off among the non-merge commits."""
    return [(sha, subject) for sha, parents, subject, body in commits(repo, ranges)
            if len(parents) < 2 and not SIGNOFF.search(body)]


def main_check(args):
    try:
        missing = check(args.repo, args.ranges)
        total = len([c for c in commits(args.repo, args.ranges) if len(c[1]) < 2])
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if missing:
        print(f"{len(missing)} of {total} commit(s) lack a Signed-off-by trailer:")
        for sha, subject in missing:
            print(f"  {sha[:12]} {subject}")
        print("Sign your commits with `git commit -s` (or `git rebase --signoff`) and push again.")
        return 1
    print(f"all {total} commit(s) carry a Signed-off-by trailer")
    return 0


# ---- regression check against throwaway fixtures ---------------------------------------

def fixture_env():
    """A hermetic git environment: no user, system, or injected configuration and no hooks."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_CONFIG_")}
    env.update({
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_AUTHOR_NAME": "Fixture Author", "GIT_AUTHOR_EMAIL": "author@example.com",
        "GIT_COMMITTER_NAME": "Fixture Author", "GIT_COMMITTER_EMAIL": "author@example.com",
        "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z", "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z",
    })
    return env


def run_fixture_git(repo, env, *args):
    p = subprocess.run(["git", "-C", repo, *args], env=env, capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"fixture git {' '.join(args)} failed: {p.stderr.strip()}")
    return p.stdout.strip()


def commit_file(repo, env, name, message):
    with open(os.path.join(repo, name), "w") as f:
        f.write(message + "\n")
    run_fixture_git(repo, env, "add", "--", name)
    p = subprocess.run(["git", "-C", repo, "commit", "-q", "-F", "-"], env=env, input=message,
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"fixture commit failed: {p.stderr.strip()}")
    return run_fixture_git(repo, env, "rev-parse", "HEAD")


def cli(repo, env, *ranges):
    p = subprocess.run([sys.executable, "-I", os.path.abspath(__file__), "-C", repo, *ranges],
                       env=env, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def self_test():
    env = fixture_env()
    env["GIT_CONFIG_PARAMETERS"] = "'core.hooksPath=/dev/null'"
    failures = []

    def expect(label, cond):
        print(("ok   " if cond else "FAIL ") + label)
        if not cond:
            failures.append(label)

    signed = "Signed-off-by: Fixture Author <author@example.com>"
    with tempfile.TemporaryDirectory(prefix="nyxis-dco-") as tmp:
        repo = os.path.join(tmp, "repo")
        os.mkdir(repo)
        run_fixture_git(repo, env, "init", "-q", "-b", "main")
        base = commit_file(repo, env, "base.txt", "base commit\n\n" + signed)
        s1 = commit_file(repo, env, "a.txt", "first signed change\n\n" + signed)
        s2 = commit_file(repo, env, "b.txt", "second signed change\n\nSome body text.\n\n" + signed)
        # A column where every commit is signed off passes.
        rc, out = cli(repo, env, f"{base}..{s2}")
        expect("signed column: exit 0", rc == 0 and "all 2 commit(s)" in out)
        # A column with an unsigned commit fails and names exactly that commit.
        u1 = commit_file(repo, env, "c.txt", "unsigned change")
        s3 = commit_file(repo, env, "d.txt", "third signed change\n\n" + signed)
        rc, out = cli(repo, env, f"{base}..{s3}")
        expect("unsigned column: exit 1", rc == 1)
        expect("unsigned column: names the unsigned commit", u1[:12] in out and "unsigned change" in out)
        expect("unsigned column: does not name signed commits",
               all(sha[:12] not in out for sha in (s1, s2, s3)))
        # A malformed trailer (no email, or sign-off text that is not a trailer line) does not count.
        m1 = commit_file(repo, env, "e.txt", "malformed trailer\n\nSigned-off-by: Nobody")
        m2 = commit_file(repo, env, "f.txt", "mentioned in prose\n\nThis is Signed-off-by: X <x@example.com> in a sentence.")
        rc, out = cli(repo, env, f"{s3}..{m2}")
        expect("malformed trailers: exit 1 for both", rc == 1 and m1[:12] in out and m2[:12] in out)
        # A sign-off anywhere in the body (not only the last line) is accepted; merge commits are skipped.
        run_fixture_git(repo, env, "checkout", "-q", "-b", "topic", s3)
        t1 = commit_file(repo, env, "g.txt", "topic change\n\n" + signed + "\nReviewed-by: Someone <s@example.com>")
        run_fixture_git(repo, env, "checkout", "-q", "main")
        run_fixture_git(repo, env, "checkout", "-q", "-b", "merged", s3)
        run_fixture_git(repo, env, "merge", "-q", "--no-ff", "-m", "merge topic (no sign-off)", "topic")
        merged = run_fixture_git(repo, env, "rev-parse", "HEAD")
        rc, out = cli(repo, env, f"{s3}..{merged}")
        expect("merge commit skipped, trailer before another trailer accepted",
               rc == 0 and "all 1 commit(s)" in out and t1 != merged)
        # Several ranges are checked together as one set (git log semantics); an empty range passes;
        # a bad range is a usage error.
        rc, out = cli(repo, env, f"{s3}..{t1}", f"{s3}..{merged}")
        expect("several ranges", rc == 0 and "all 1 commit(s)" in out)
        run_fixture_git(repo, env, "checkout", "-q", "-b", "other", s3)
        u2 = commit_file(repo, env, "h.txt", "unsigned change on another branch")
        rc, out = cli(repo, env, f"{s3}..{u2}", f"{s3}..{merged}")
        expect("several ranges with an unsigned commit", rc == 1 and u2[:12] in out and t1[:12] not in out)
        rc, out = cli(repo, env, f"{s2}..{s2}")
        expect("empty range: exit 0", rc == 0 and "all 0 commit(s)" in out)
        rc, out = cli(repo, env, "no-such-ref..HEAD")
        expect("unknown ref: exit 2", rc == 2)
    if failures:
        print(f"\n{len(failures)} regression check(s) failed", file=sys.stderr)
        return 1
    print("\nall regression checks passed")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-C", dest="repo", default=".", help="repository to inspect (default: current directory)")
    ap.add_argument("--self-test", action="store_true", help="run the regression check against throwaway fixtures")
    ap.add_argument("ranges", nargs="*", help="commit ranges as accepted by git log, e.g. base..head")
    args = ap.parse_args()
    if args.self_test:
        if args.ranges:
            ap.error("--self-test takes no range")
        raise SystemExit(self_test())
    if not args.ranges:
        ap.error("a commit range is required (e.g. base..head)")
    raise SystemExit(main_check(args))


if __name__ == "__main__":
    main()
