#!/usr/bin/env python3
"""COMPUTED source-only compact project export, Codex GPT-6.1 sol lane C.
Re-derivation of Fauzan's theorem reusing Firsching's formalisation
(mo271/Zeta5 be1c0d82, Apache-2.0; Comparator metadata Paul-Lez).
Exports the actual proved import closure; a separate project gate follows.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

root = Path(__file__).resolve().parent
report = (root / 'log/LEAN_CHECK.md').read_text()
assert '**Overall: PASS**' in report and 'CCompactZeta5.irrational_five' in report
audit = json.loads((root / 'SIZE_COMPACT.json').read_text())['current']
assert audit['root'] == 'CompactEntry'
assert 'Apery.EnergyFinal' not in audit['modules']
assert not any(name.startswith(('Apery.Table.U', 'Apery.Table.V', 'Apery.Table2'))
               for name in audit['modules'])
output = root / 'project'
output.mkdir(exist_ok=True)
records = []
products = 0
for name, row in audit['modules'].items():
    relative = Path(row['path'])
    source = root / relative
    data = source.read_bytes()
    assert hashlib.sha256(data).hexdigest() == row['sha256'], name
    destination = output / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        assert destination.read_bytes() == data, ('Refusing to overwrite changed export', name)
    else:
        shutil.copy2(source, destination)
    records.append(dict(module=name, path=str(relative), sha256=row['sha256'], lines=row['lines']))
    stem = Path(name.replace('.', '/'))
    for tree in ['lib/lean', 'ir']:
        folder = root / '.lake/build' / tree / stem.parent
        if folder.exists():
            for product in folder.glob(stem.name + '.*'):
                if product.is_file():
                    copied = output / '.lake/build' / tree / stem.parent / product.name
                    copied.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(product, copied)
                    products += 1
roots = sorted({name.split('.')[0] for name in audit['modules']})
config = (root / 'lakefile.toml').read_text().split('[[lean_lib]]', 1)[0]
config = re.sub(r'defaultTargets = \[[^\n]*\]', 'defaultTargets = ["CompactEntry"]', config)
config += ''.join('\n[[lean_lib]]\nname = ' + json.dumps(name) + '\n' for name in roots)
(output / 'lakefile.toml').write_text(config)
for name in ['lean-toolchain', 'lake-manifest.json', 'LICENSE', 'NOTICE']:
    shutil.copy2(root / name, output / name)
packages = output / '.lake/packages'
packages.parent.mkdir(exist_ok=True)
if not packages.exists():
    packages.symlink_to((root / '.lake/packages').resolve(), target_is_directory=True)
(output / 'SOURCE_MANIFEST.json').write_text(json.dumps(dict(
    status='COMPUTED source-only standalone compact export; separate gate required',
    author='Codex GPT-6.1 sol lane C', root='CompactEntry', files=records,
    local_files=len(records), local_lines=sum(row['lines'] for row in records),
    mathematical_source_changes=0, old_fine_energy_chunks=0,
    warm_products_copied=products), indent=2) + '\n')
(output / 'README.md').write_text('''# Compact ζ(5) re-derivation

A re-derivation of Fauzan's theorem reusing Moritz Firsching's formalisation
(mo271/Zeta5@be1c0d82, Apache-2.0; Comparator metadata by Paul-Lez).
The event general-s arithmetic chain is specialized at (5,6); lane U supplies
the coarse169-cell field certificate and actual closing inequality.
No new or independent irrationality theorem is claimed.

The target is CCompactZeta5.irrational_five, with literal conclusion
`∃ x, Irrational x ∧ riemannZeta 5 = x` and no caller hypotheses.
Its parent receiving project passes the final4.35gate, standard three axioms.
This standalone export's separate gate receipt is placed in log/LEAN_CHECK.md.

Build with Lean/Mathlib4.35.0:

```sh
lake exe cache get
lake build
```

All local source dependencies are here. Mathlib and PNT are pinned in the
manifest; there is no path dependency. Ignored warm-cache links are only a
local convenience. A clean checkout fetches the pinned dependencies normally.
LICENSE/NOTICE and source attribution headers must be preserved.

COMPUTED:282local Lean files /69,392lines, including16,960lines of new field
certificate and27,040lines of event scalar cells. No old fine energy chunks
or unreachable heavy fallback are included. Upstream's main-theorem closure
is209files /138,236lines:49.8%fewer source lines, with more files. The initial
forecast of far more than half reduction was not achieved. Full comparison,
scope, transcripts and build history live in the parent evidence folder.
Only the integrator upgrades labels after the submitted-project gate,
verbatim report statement and recorded cross-family comparison.
''')
print(json.dumps(dict(project=str(output), source_files=len(records),
    source_lines=sum(row['lines'] for row in records), warm_products_copied=products)))
