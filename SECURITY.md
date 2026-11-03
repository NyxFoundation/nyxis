# Security Policy

## Reporting a vulnerability

Please do not report security vulnerabilities through public issues, pull requests, or discussions.

Report them privately through GitHub's private vulnerability reporting: open
[Report a vulnerability](https://github.com/NyxFoundation/nyxis/security/advisories/new) on the
**Security** tab of this repository. Only the maintainers can read the report.

Please include:

- the version of Nyxis you tested (the `version` in `lakefile.lean`, or the release tag);
- what the vulnerability lets an attacker do, and which component it concerns (the HTTP
  boundary, JWT verification, the Cedar evaluation, the PostgreSQL driver, a sample, or the
  proofs and the trusted assumptions in [ASSUMPTIONS.md](ASSUMPTIONS.md));
- steps to reproduce, if you have them.

A maintainer acknowledges the report, keeps you informed while it is investigated, and credits
you in the advisory unless you prefer otherwise.

## What counts as a vulnerability

Nyxis promises one property, proven in Lean: no sequence of HTTP requests can cause an
authenticated principal to read, modify, delete, or grant access to data beyond its legitimate
permissions. Of particular interest are:

- a way to violate that property in a backend built on Nyxis, including through the
  parts that the proofs trust rather than prove (see [ASSUMPTIONS.md](ASSUMPTIONS.md));
- a gap between what [ASSUMPTIONS.md](ASSUMPTIONS.md) states and what the implementation does;
- a way for a handler to have effects other than action calls, bypassing the build-time checks;
- information disclosure at the HTTP boundary (caching, headers, error responses);
- a weakness in dependency pinning or in the build that could let unreviewed code into a build.

## Supported versions

Nyxis is under development. Security fixes are made in the latest release only; please upgrade
before reporting an issue that a newer release may already address.

## Disclosure

A fix is published in a new release, and the advisory is published after that release. Please
give the maintainers a reasonable time to release a fix before disclosing the issue publicly.
