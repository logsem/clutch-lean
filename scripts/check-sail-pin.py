#!/usr/bin/env python3
"""Check the unmodified upstream Sail extraction and its runtime dependency."""
import hashlib
import json
import re
from pathlib import Path
import tomllib

root = Path(__file__).resolve().parent.parent
provenance = tomllib.loads((root / 'sail-import/PROVENANCE.toml').read_text())
files = sorted([root / 'RiscvZkvm/Sail.lean', *(root / 'RiscvZkvm/Sail').glob('*.lean')], key=str)
def original_bytes(p):
    if p.name == 'RiscvExtras.lean':
        return (root / 'sail-import/RiscvExtras.upstream.lean.txt').read_bytes()
    return p.read_bytes()

lines = ''.join(
    f'{hashlib.sha256(original_bytes(p)).hexdigest()}  ./{p.relative_to(root)}\n' for p in files
)
actual = hashlib.sha256(lines.encode()).hexdigest()
assert actual == provenance['extraction']['model_sha256'], ('model hash', actual)
assert len(files) == provenance['extraction']['expected_lean_files'], ('model count', len(files))
config = root / provenance['extraction']['config_file']
assert hashlib.sha256(config.read_bytes()).hexdigest() == provenance['extraction']['config_sha256']
manifest = json.loads((root / 'lake-manifest.json').read_text())
runtime = next(p for p in manifest['packages'] if p['name'] == 'Sail')
assert runtime['type'] == 'path' and Path(runtime['dir']) == Path('runtime/lean-sail')
pins = json.loads((root / 'sail-import/runtime-files.json').read_text())
for name, digest in pins.items():
    data = (root / 'runtime/lean-sail' / name).read_bytes()
    if name == 'Sail.lean':
        data, shim = data.split(b'\n-- Lean 4.35', 1)
        expected = (root / 'sail-import/lean-4.35-assert-shim.lean.txt').read_bytes()
        assert b'\n-- Lean 4.35' + shim == expected, 'runtime parser shims'
    assert hashlib.sha256(data).hexdigest() == digest, ('runtime delta', name)
assert (root / 'RiscvZkvm/Sail/RiscvExtras.lean').read_bytes() == (root / 'sail-import/RiscvExtras.lean').read_bytes()
binders = json.loads((root / 'sail-import/strict-binders.json').read_text())
assert binders['source_model_sha256'] == provenance['extraction']['model_sha256']
shim_source = (root / 'runtime/lean-sail/Sail.lean').read_text()
actual_binders = []
for module, declaration, kind, arguments in re.findall(
        r'^  \(`([^,]+), `([^,]+), "(def|abbrev)", (.+)\)[,\]]?$', shim_source, re.M):
    parameters = re.findall(r'\(`([^,]+), "([^"]+)"\)', arguments)
    actual_binders.append({'module': module, 'declaration': declaration,
                           'kind': kind, 'binders': [list(p) for p in parameters]})
assert actual_binders == [{k: v for k, v in e.items() if k != 'certificate'}
                          for e in binders['entries']], 'explicit binder whitelist'
certificates = (root / 'Tests/StrictSourceEquivalence.lean').read_text()
for entry in binders['entries']:
    name = entry['certificate']
    assert re.search(r'^theorem ' + re.escape(name) + r'\b', certificates, re.M), name
configuration = tomllib.loads((root / 'lakefile.toml').read_text())
for library in configuration.get('lean_lib', []):
    options = configuration.get('leanOptions', {}) | library.get('leanOptions', {})
    for option in ['autoImplicit', 'relaxedAutoImplicit']:
        assert options.get(option) is False, ('implicit binders enabled', library['name'], option)
print(f'OK: {len(files) - 1} upstream generated/support files, original Extras, config, runtime')
