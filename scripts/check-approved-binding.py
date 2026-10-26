#!/usr/bin/env python3
"""Well-typed replacements of the deployment's authorization sources must fail the startup build.
The declaration (`nyxis_approved`) and the Cedar files are never modified. Always restore
the application source and rebuild. Run sequentially with every other Lake/mutation check.
"""
from pathlib import Path
import signal
import subprocess
import tempfile

if not __debug__:
    raise SystemExit('assertions disabled')
root = Path(__file__).resolve().parent.parent / 'examples/bulletin-board/backend'
source = root / 'BulletinBoard/Server.lean'


def interrupted(signum, frame):
    raise KeyboardInterrupt(f'signal {signum}')


for sig in (signal.SIGTERM, signal.SIGHUP):
    signal.signal(sig, interrupted)

original = source.read_bytes()
old = '  sources := Approved.sources\n'
assert original.decode().count(old) == 1
permit_all = ('[{ id := "permit-all", effect := .permit, principalScope := .principalScope .any, '
              'actionScope := .actionScope .any, resourceScope := .resourceScope .any, condition := [] }]')
variants = {
    'empty-policies': '  sources := ⟨Approved.schema, []⟩\n',
    'permit-all': f'  sources := ⟨Approved.schema, {permit_all}⟩\n',
    'alternate-sources': '  sources := replacement\n',
}
# A separately declared, well-typed value outside the canonical declaration.
replacement_def = 'def replacement : Nyxis.Approved := ⟨Approved.schema, []⟩\n\n'
with tempfile.TemporaryDirectory(prefix='nyxis-approved-binding-') as tmp:
    try:
        for name, value in variants.items():
            text = original.decode().replace(old, value)
            if name == 'alternate-sources':
                text = text.replace('def deployment :', replacement_def + 'def deployment :')
            source.write_text(text)
            # The fixture itself must typecheck: the rejection is startup's equality, not a syntax error.
            check = subprocess.run(['lake', 'env', 'lean', 'BulletinBoard/Server.lean'], cwd=root,
                                   capture_output=True, text=True, timeout=180)
            assert check.returncode == 0, f'{name}: invalid fixture\n{check.stdout}{check.stderr}'
            result = subprocess.run(['lake', 'build', 'sample'], cwd=root,
                                    capture_output=True, text=True, timeout=180)
            output = result.stdout + result.stderr
            Path(tmp, name + '.log').write_text(output)
            assert result.returncode != 0, f'{name}: replacement reached startup'
            assert 'error: Main.lean:' in output and 'rfl' in output, output
            print(f'{name}: well typed sources; sample build exit {result.returncode}, startup equality rejected')
    finally:
        source.write_bytes(original)
        restored = subprocess.run(['lake', 'build'], cwd=root, capture_output=True, text=True, timeout=180)
        assert restored.returncode == 0, restored.stdout + restored.stderr
        print('restored: lake build exit 0')
