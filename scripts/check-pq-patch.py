#!/usr/bin/env python3
"""Reproduce the approved patched source from its locked archive, without git."""
import importlib.util
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('prepare', ROOT / 'scripts/prepare-dependencies.py')
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


def main():
    with tempfile.TemporaryDirectory(prefix='nyxis-pq-patch-') as temporary:
        prepare.CACHE = Path(temporary)
        prepare.LOCK = {'lean-pq': prepare.LOCK['lean-pq']}
        prepare.install()
        prepare.install()
        installed = prepare.CACHE / 'lean-pq'
        assert prepare.digest_tree(installed) == prepare.digest_tree(ROOT / '.lake/vendor/lean-pq')
        source = installed / 'LeanPq/extern.c'
        source.write_text(source.read_text() + '\n')
        try:
            prepare.install()
        except RuntimeError:
            pass
        else:
            raise AssertionError('modified source accepted')
    print('check-pq-patch: locked archive/patch reproduced installed tree; modification rejected')


if __name__ == '__main__':
    main()
