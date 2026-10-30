#!/usr/bin/env python3
"""The link-argument definitions must be the same in every lakefile that carries a copy.

Lake does not propagate link arguments to the requiring package, so `postgresLinkArgs` and
`cryptoShimLinkArgs` are defined in the root `lakefile.lean` and copied into both samples (the
README tells applications to copy them too). A fix that reaches only one copy builds here and
fails elsewhere, so this check requires the copies to be identical, character for character, and
each lakefile to use both in `moreLinkArgs`. No build, no network.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LAKEFILES = ['lakefile.lean',
             'examples/bulletin-board/backend/lakefile.lean',
             'examples/team-docs/backend/lakefile.lean']
DEFINITIONS = ['postgresLinkArgs', 'cryptoShimLinkArgs']


def definition(text, name, path):
    """The top-level `def <name>` up to the next blank line, or None."""
    m = re.search(rf'^def {re.escape(name)}\b.*?(?=\n\n|\Z)', text, re.MULTILINE | re.DOTALL)
    return m.group(0) if m else None


def main():
    problems = []
    texts = {path: (ROOT / path).read_text() for path in LAKEFILES}
    for name in DEFINITIONS:
        copies = {path: definition(text, name, path) for path, text in texts.items()}
        missing = [path for path, copy in copies.items() if copy is None]
        for path in missing:
            problems.append(f'{path}: no definition of {name}')
        present = {path: copy for path, copy in copies.items() if copy is not None}
        if len(set(present.values())) > 1:
            reference = present[LAKEFILES[0]] if LAKEFILES[0] in present else next(iter(present.values()))
            for path, copy in present.items():
                if copy != reference:
                    problems.append(f'{path}: {name} differs from {LAKEFILES[0]}')
    for path, text in texts.items():
        uses = re.search(r'^\s*moreLinkArgs\s*:=\s*(.*)$', text, re.MULTILINE)
        if not uses:
            problems.append(f'{path}: no moreLinkArgs')
            continue
        for name in DEFINITIONS:
            if name not in uses.group(1):
                problems.append(f'{path}: moreLinkArgs does not use {name}')
    readme = (ROOT / 'README.md').read_text()
    for name in DEFINITIONS:
        if f'`{name}`' not in readme:
            problems.append(f'README.md: does not tell applications to copy {name}')
    if problems:
        print('link arguments: ' + str(len(problems)) + ' problem(s)', file=sys.stderr)
        for p in problems:
            print('  ' + p, file=sys.stderr)
        return 1
    print(f'link arguments: {len(DEFINITIONS)} definitions identical across {len(LAKEFILES)} lakefiles, '
          'each used in moreLinkArgs, both named in README.md')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
