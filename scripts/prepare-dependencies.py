#!/usr/bin/env python3
"""Install the approved, locked JWT and PostgreSQL sources without git. Run before the first lake build.
Lake configuration/toolchains are adapted; lean-pq receives the approved ownership patch.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
LOCK = json.loads((ROOT / 'scripts/dependencies.json').read_text())
CACHE = ROOT / '.lake/vendor'


def digest_tree(path):
    digest = hashlib.sha256()
    for file in sorted(path.rglob('*')):
        relative = file.relative_to(path)
        if '.lake' in relative.parts or relative.name in {'nyxis-source.json', 'lake-manifest.json'}:
            continue
        if file.is_file():
            digest.update(str(relative).encode() + b'\0' + file.read_bytes() + b'\0')
    return digest.hexdigest()


def pq_metadata():
    metadata = json.loads((ROOT / 'scripts/patches/lean-pq-ownership.json').read_text())
    patch = (ROOT / 'scripts/patches/lean-pq-ownership.patch').read_bytes()
    if (metadata['revision'] != LOCK['lean-pq']['revision'] or
            hashlib.sha256(patch).hexdigest() != metadata['patch_sha256']):
        raise RuntimeError('lean-pq: patch identity mismatch')
    return metadata, patch


def pq_matches(path, metadata, stage):
    return all(hashlib.sha256((path / name).read_bytes()).hexdigest() == hashes[stage]
               for name, hashes in metadata['files'].items())


def pq_patch(path):
    metadata, patch = pq_metadata()
    def matches(stage):
        return pq_matches(path, metadata, stage)
    if not matches('before'):
        raise RuntimeError('lean-pq: patch input mismatch')
    subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-d', str(path)],
                   input=patch, check=True, stdout=subprocess.DEVNULL)
    if not matches('after'):
        raise RuntimeError('lean-pq: patch output mismatch')
    return metadata['patch_sha256']


def install():
    CACHE.mkdir(parents=True, exist_ok=True)
    for name, pin in LOCK.items():
        destination = CACHE / name
        marker = destination / 'nyxis-source.json'
        patch_metadata = pq_metadata()[0] if name == 'lean-pq' else None
        patch_id = patch_metadata['patch_sha256'] if patch_metadata else None
        if destination.exists():
            expected = {'pin': pin, 'toolchain': (ROOT / 'lean-toolchain').read_text(),
                        'adaptation': 1, 'tree': digest_tree(destination)}
            actual = json.loads(marker.read_text()) if marker.is_file() else None
            if actual and 'patch' in actual:
                expected['patch'] = patch_id
                if not patch_metadata or not pq_matches(destination, patch_metadata, 'after'):
                    raise RuntimeError(f'{name}: patched source digest mismatch')
            if actual != expected:
                raise RuntimeError(f'{name}: existing sources differ from the locked installation')
            if name == 'lean-pq' and 'patch' not in actual:
                expected['patch'] = pq_patch(destination)
                expected['tree'] = digest_tree(destination)
                marker.write_text(json.dumps(expected, indent=2) + '\n')
            print(f'{name}: locked sources verified' + (' (approved ownership patch)' if patch_id else ''))
            continue
        with tempfile.TemporaryDirectory(prefix='prepare-', dir=CACHE) as temporary:
            work = Path(temporary)
            owner = pin.get('owner', 'paulbutcher')
            url = f'https://codeload.github.com/{owner}/{name}/tar.gz/{pin["revision"]}'
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
            if hashlib.sha256(data).hexdigest() != pin['sha256']:
                raise RuntimeError(f'{name}: archive digest mismatch')
            archive = work / 'source.tgz'
            archive.write_bytes(data)
            with tarfile.open(archive) as source:
                source.extractall(work, filter='data')
            path = work / f'{name}-{pin["revision"]}'
            config = path / 'lakefile.lean'
            text = config.read_text()
            def dependency(match):
                repo = match[2].rsplit('/', 1)[-1]
                if repo not in LOCK:
                    raise RuntimeError(f'{name}: unapproved dependency {repo}')
                return f'require {match[1]} from "../{repo}"'
            text = re.sub(r'require (\S+) from git "([^"]+)" @ "[^"]+"', dependency, text)
            if 'from git' in text:
                raise RuntimeError(f'{name}: unsupported git dependency')
            if name == 'lean-json':
                old = '⟨`warningAsError, true⟩'
                if text.count(old) != 1:
                    raise RuntimeError('lean-json: unexpected compatibility configuration')
                text = text.replace(old, old + ', ⟨`linter.deprecated, false⟩')
            config.write_text(text)
            (path / 'lake-manifest.json').unlink(missing_ok=True)
            toolchain = (ROOT / 'lean-toolchain').read_text()
            (path / 'lean-toolchain').write_text(toolchain)
            metadata = {'pin': pin, 'toolchain': toolchain, 'adaptation': 1}
            if name == 'lean-pq':
                metadata['patch'] = pq_patch(path)
            metadata['tree'] = digest_tree(path)
            (path / 'nyxis-source.json').write_text(json.dumps(metadata, indent=2) + '\n')
            shutil.move(str(path), destination)
        print(f'{name}: installed {pin["revision"]} (archive SHA256 verified)')


if __name__ == '__main__':
    install()
