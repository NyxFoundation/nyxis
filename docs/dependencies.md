# Preparing the pinned dependencies

JWT verification uses the approved lean-jose / jose-libcrypto / lean-libcrypto.
The transitive dependencies are lean-json / leancrypto. They are included in the main Lake dependencies and use the OpenSSL backend.
lean-pq is also fetched through this preparation path, at the same revision as before.
The existing Lake dependencies on Cedar and batteries are kept.

```sh
python3 scripts/prepare-dependencies.py
lake build
sh scripts/check-installed-jwt.sh
```

Requires Python 3.12 or later, the OpenSSL CLI, pkg-config, libcrypto and libpq development files, and a C compiler.
`scripts/dependencies.json` pins each dependency's upstream revision and the SHA256 of the fetched archive.
The preparation script runs no Git commands; it places the sources fetched and verified over HTTPS
in `.lake/vendor/`, outside Git management. Licenses and the upstream Lean/C sources are kept.
Runs after the first fetch only verify the sources, and keep the build outputs.
If `.lake/vendor/` is renamed or moved, delete `.lake/build/bin` and `.lake/vendor/lean-libcrypto/.lake/build` and rebuild,
because on macOS the absolute path of lean-libcrypto's dylib is embedded in the executables.
If existing sources or the pinned information do not match, the script fails without overwriting.

The upstream Lake configurations are changed to point dependencies at relative paths in the pinned cache, and their toolchain is aligned with the main package.
In lean-json, only `linter.deprecated` for theorem names deprecated in Lean v4.34.1 is suppressed,
and every other `warningAsError` is kept. Cryptography, JOSE parsing and proof code are not changed.
The upstream configurations can be seen at [the pinned revision of lean-json](https://github.com/paulbutcher/lean-json/blob/c7323a3eb8323fb16ee451de495ff91192453aa5/lakefile.lean)
and [the pinned revision of jose-libcrypto](https://github.com/paulbutcher/jose-libcrypto/blob/d722d4a55c9dfebffe69dde58d8087ae3c004e09/lakefile.lean).

`checkJwtDependency` is a check-only executable. It generates a temporary key with OpenSSL and checks 11 cases:
a valid JWT, a bad signature, a modified sub, the expiry boundary, an expired token, a wrong issuer, a wrong audience,
2 alg none cases, an unknown kid, and a missing exp.
The key and generated JWTs are kept only in a temporary directory and deleted on exit.
`sh scripts/check-handler-effects.sh` also rejects a direct import of `JoseLibcrypto` from the app.

This is an adoption check of the dependencies, not a check of the main path (HTTPS fetch of the JWKS, JWT verification, real DB).
For checks of the main path, see [how to check with local Supabase](local-supabase.md).
