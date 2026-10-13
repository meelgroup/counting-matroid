#!/usr/bin/env python3
"""Snapshot a solution without compiling it or modifying the trusted baseline."""
import argparse, hashlib, json, os
from pathlib import Path

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source', type=Path, help='current Lean project (defaults to the original project)')
args = parser.parse_args()
baseline = root / 'baseline'
manifest_bytes = (root / 'contract.json').read_bytes()
if hashlib.sha256(manifest_bytes).hexdigest() != (root / 'contract.sha256').read_text().strip():
    raise SystemExit('Contract manifest changed; review the trusted baseline.')
manifest = json.loads(manifest_bytes)
source = (args.source or Path(manifest['sourceProject'])).resolve()
def digest(data): return hashlib.sha256(data).hexdigest()
for name, expected in manifest['baselineFiles'].items():
    file = baseline / name
    if file.is_symlink() or digest(file.read_bytes()) != expected:
        raise SystemExit('Trusted baseline changed: ' + name)
for name, expected in manifest['trustedSources'].items():
    file = source / name
    if file.is_symlink() or digest(file.read_bytes()) != expected:
        raise SystemExit('Project contract changed: ' + name + '. Review it; do not replace the baseline merely to pass verification.')
skip = {'.git', '.lake', '.blueprint', '.tex2lean', 'node_modules', 'scratch', 'build', 'out'}
sources = {}
for directory, dirs, files in os.walk(source, followlinks=False):
    at = Path(directory)
    dirs[:] = sorted(d for d in dirs if d not in skip and not d.startswith('.') and not (at / d).resolve().is_relative_to(root))
    for d in dirs:
        if (at / d).is_symlink(): raise SystemExit('Source directory is a symlink: ' + str(at / d))
    for name in sorted(files):
        if not name.endswith('.lean') or name.startswith('.') or name == 'lakefile.lean': continue
        file = at / name
        if file.is_symlink(): raise SystemExit('Source file is a symlink: ' + str(file))
        relative = file.relative_to(source).as_posix()
        if relative in {'Challenge.lean', 'Solution.lean'}:
            raise SystemExit('Project uses reserved Comparator module: ' + relative)
        sources[relative] = file.read_bytes()
if manifest['theoremFile'] not in sources: raise SystemExit('The solution theorem module is missing.')
for name, data in sources.items():
    if (source / name).read_bytes() != data: raise SystemExit('Source changed during capture: ' + name)
key = digest(json.dumps({k: digest(v) for k, v in sorted(sources.items())}, sort_keys=True).encode())
exports = root / 'exports'
destination = exports / key
if destination.exists():
    for name, data in sources.items():
        if not (destination / name).is_file() or (destination / name).read_bytes() != data:
            raise SystemExit('Existing solution export changed: ' + name)
    for name, expected in manifest['baselineFiles'].items():
        if digest((destination / name).read_bytes()) != expected:
            raise SystemExit('Existing export baseline changed: ' + name)
else:
    exports.mkdir(exist_ok=True)
    # Preserve a failed preparation instead of deleting or replacing it.
    import tempfile
    attempt = Path(tempfile.mkdtemp(prefix='preparing-', dir=exports))
    # Copy only certified source/configuration, never a previously built .lake.
    for name, expected in manifest['baselineFiles'].items():
        data = (baseline / name).read_bytes()
        if digest(data) != expected: raise SystemExit('Baseline changed during capture: ' + name)
        target = attempt / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    for name, data in sources.items():
        if name in manifest['baselineFiles']:
            if digest(data) != manifest['baselineFiles'][name]:
                raise SystemExit('Solution would overwrite trusted baseline: ' + name)
            continue
        target = attempt / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    # Recheck contract inputs after source reads and before exposing the export.
    for name, expected in manifest['trustedSources'].items():
        if digest((source / name).read_bytes()) != expected:
            raise SystemExit('Contract changed during capture: ' + name)
    attempt.rename(destination)
print(destination)
print('Fresh checking environment: review the challenge and Lake configuration, then run:')
print('  Keep the copied lake-manifest.json; do not run lake update.')
print('  lake exe cache get  # only when using a trusted Mathlib cache')
print('  sh verify.sh /absolute/path/to/comparator')
print('Do not build Solution before invoking Comparator in this checking environment.')
