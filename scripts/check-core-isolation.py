#!/usr/bin/env python3
"""Build the core and audit its axioms with application sources outside the repository.
Run sequentially with other Lake commands. Always restore moved sources, including on signals.
"""
from pathlib import Path
import signal
import subprocess
import tempfile

if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parents[1]


def interrupted(signum, frame):
    raise KeyboardInterrupt(f'signal {signum}')


def main():
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, interrupted)
    paths = [ROOT / 'Nyxis.lean', ROOT / 'Test.lean', ROOT / 'lakefile.lean',
             *sorted((ROOT / 'Nyxis').rglob('*')),
             *sorted((ROOT / 'Test').rglob('*'))]
    for path in paths:
        if path.is_file():
            assert all(term not in path.read_text() for term in
                       ('examples/', 'BulletinBoard', 'Sample', 'sample')), path
    print('core/application references: 0', flush=True)
    # Same filesystem as the repository: Path.rename cannot cross devices (tmpfs /tmp on Linux).
    with tempfile.TemporaryDirectory(prefix='nyxis-core-isolation-', dir=ROOT.parent) as directory:
        moved = []
        try:
            for name in ('examples',):
                source = ROOT / name
                if source.exists():
                    destination = Path(directory) / name
                    source.rename(destination)
                    moved.append((source, destination))
            for command in (['lake', 'build'], ['lake', 'env', 'lean', 'Test/Axioms.lean']):
                result = subprocess.run(command, cwd=ROOT)
                print(' '.join(command), 'exit', result.returncode, flush=True)
                if result.returncode:
                    raise SystemExit(result.returncode)
        finally:
            for source, destination in reversed(moved):
                destination.rename(source)
    print('application sources restored', flush=True)


if __name__ == '__main__':
    main()
