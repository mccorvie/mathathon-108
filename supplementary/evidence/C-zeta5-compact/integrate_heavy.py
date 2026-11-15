#!/usr/bin/env python3
"""COMPUTED C4 integration, only after the heavy provider's final gate passes.
Codex GPT-6.1 sol lane C; re-derivation of Fauzan's theorem reusing Firsching's
Apache-2.0 formalisation (mo271/Zeta5 be1c0d82; Comparator metadata Paul-Lez).
Does not prove a statement or replace a receiving gate.
"""
from pathlib import Path
import hashlib
import json
import shutil

root = Path(__file__).resolve().parent
producer = root.parent / 'C-heavy-analysis'
receipt = producer / 'log/LEAN_CHECK.md'
assert receipt.is_file() and '**Overall: PASS**' in receipt.read_text(), 'Heavy final gate not ready'
assert 'HeavyInstance.heavy_finite_real_bound' in receipt.read_text(), 'Wrong provider gate'
assert (producer / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
incoming = json.loads((producer / 'SOURCE_MANIFEST.json').read_text())
added = []
overlaps = []
cache_products = 0
for module, record in incoming['modules'].items():
    relative = Path(record['destination'])
    source = producer / relative
    destination = root / relative
    data = source.read_bytes()
    assert sha(data) == record['sha256'], module
    if destination.exists():
        assert destination.read_bytes() == data, ('Heavy source conflict', module)
        overlaps.append(module)
        continue
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    copied = dict(record)
    copied['source'] = str(source.resolve())
    manifest['modules'][module] = copied
    added.append(module)
    stem = Path(module.replace('.', '/'))
    for subtree in ['lib/lean', 'ir']:
        folder = producer / '.lake/build' / subtree / stem.parent
        if not folder.exists():
            continue
        for product in folder.glob(stem.name + '.*'):
            if product.is_file():
                output = root / '.lake/build' / subtree / stem.parent / product.name
                output.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(product, output)
                cache_products += 1
(root / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
roots = sorted({name.split('.')[0] for name in manifest['modules']} |
               {'Assembly', 'ArithmeticEntry', 'ClosingEntry', 'HeavyEntry'})
config = (root / 'lakefile.toml').read_text().split('[[lean_lib]]', 1)[0]
config = config.replace('defaultTargets = ["ClosingEntry"]', 'defaultTargets = ["HeavyEntry"]')
config += ''.join('\n[[lean_lib]]\nname = ' + json.dumps(name) + '\n' for name in roots)
(root / 'lakefile.toml').write_text(config)
receipt_out = dict(status='COMPUTED exact heavy-source integration; receiving gate required',
    author='Codex GPT-6.1 sol lane C', added=added, overlaps=overlaps,
    warm_products_copied=cache_products,
    producer_gate_sha256=sha(receipt.read_bytes()),
    mathematical_body_changes=0)
(root / 'HEAVY_INTEGRATION.json').write_text(json.dumps(receipt_out, indent=2) + '\n')
print(json.dumps(dict(added=len(added), exact_overlaps=len(overlaps),
                     warm_products_copied=cache_products)))
