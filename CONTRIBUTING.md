# Contributing to Nyxis

Thank you for your interest in Nyxis. This page explains how contributions reach the project, what we ask of every commit, and what continuous integration checks.

## How pull requests are incorporated

Nyxis is developed in a private canonical repository. This public repository receives one commit per release, so its `main` branch contains only release commits.

Pull requests are welcome here, and they are reviewed here, but they are **not merged on GitHub**. Instead:

1. A maintainer reviews your pull request and discusses changes with you in the pull request.
2. Once accepted, the maintainer incorporates the change into the canonical repository. Your pull request receives a comment saying that it has been incorporated and will be published with the next release.
3. The next release commit carries your name as a co-author (`Co-authored-by`), and the release notes credit your contribution.
4. When that release is published, your pull request is closed with a comment naming the version it was incorporated in (for example "incorporated in v0.2.0").

Because of this flow, an incorporated pull request shows as *closed* rather than *merged* on GitHub. The release commit and the release notes are the record of your contribution.

Bug reports and questions are welcome as issues.

## Developer Certificate of Origin

Nyxis does not use a contributor license agreement. Instead, every commit in a pull request must carry a [Developer Certificate of Origin](https://developercertificate.org/) sign-off, which certifies that you have the right to submit the change under the project's [MIT License](LICENSE).

A sign-off is a trailer line at the end of the commit message:

```
Signed-off-by: Your Name <you@example.com>
```

Git adds it for you when you commit with the `-s` flag:

```sh
git commit -s
```

To add sign-offs to commits you have already made, rebase with `git rebase --signoff` and push again. Continuous integration checks that every commit in a pull request is signed off (`scripts/check-dco.py`); a pull request with an unsigned commit will not be accepted until it is fixed.

## Continuous integration

Every pull request and every push to `main` runs `.github/workflows/ci.yml` on GitHub-hosted runners (`ubuntu-latest`). It builds the core, the proofs, and the two official samples, checks the axioms of every theorem, validates the Cedar schema and policies of the samples, runs the static checks under `scripts/`, and checks the DCO sign-off of the pull request's commits.

The integration tests that need Docker and a local Supabase are not run by this workflow. Please run them locally before opening a pull request that touches the runtime or the samples; see [docs/local-supabase.md](docs/local-supabase.md) (in Japanese).

## Before you open a pull request

- Build and check locally, as in the [README](README.md): `python3 scripts/prepare-dependencies.py`, `lake build`, and `lake env lean Test/Axioms.lean`. Build the samples with `lake build --dir examples/bulletin-board/backend` and `lake build --dir examples/team-docs/backend`.
- Keep the proofs honest. Changes that weaken a theorem, add an axiom, or route around the checker (`sorry`, `unsafe`, `implemented_by`, `extern` in application code) are not accepted. A change to the statement of the main theorem or to the trusted assumptions in [ASSUMPTIONS.md](ASSUMPTIONS.md) needs discussion in an issue first.
- The Cedar schema and policies of the official samples are approved sources. Please propose changes to them in an issue before changing them in a pull request.
- Keep handlers free of effects other than action calls on the authorization layer; `lake build` enforces this, and `scripts/check-handler-effects.sh` is the regression check.
- Sign off every commit (see above).

## License

By contributing, you agree that your contributions are licensed under the project's [MIT License](LICENSE).
