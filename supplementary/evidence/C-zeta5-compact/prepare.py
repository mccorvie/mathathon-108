#!/usr/bin/env python3
"""COMPUTED E600 preparation; Codex lane C. Writes only this C project.
Re-derivation of Fauzan's theorem reusing Firsching's Apache-2.0 formalisation
(mo271/Zeta5 be1c0d82; Comparator metadata Paul-Lez). No target proofs added.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

HERE = Path(__file__).resolve().parent
EVIDENCE = HERE.parent
CANONICAL = EVIDENCE / 'L-unified-lean'
UPSTREAM = Path.home() / 'mathathon-cache/108/zeta5'
sha = lambda data: hashlib.sha256(data).hexdigest()

u_source = EVIDENCE / 'U-compact-prior-route/ProposedInterfaces.lean'
original = u_source.read_text()
adapted = original.replace('import Statement\n', 'import BRealStatement\n', 1)
adapted = adapted.replace('NOT TYPECHECKED.', 'Original proposal not typechecked; C0 typecheck recorded in log/TYPECHECK.log.')
(HERE / 'AnalyticInterface.lean').write_text(adapted)
manifest = {'author': 'Codex lane C driver, E600', 'status': 'COMPUTED source preparation only',
            'modules': {}, 'adaptations': [{'source': str(u_source),
            'destination': 'AnalyticInterface.lean', 'original_sha256': sha(u_source.read_bytes()),
            'changes': 'Statement import renamed BRealStatement for canonical unified namespace; status comment updated; target bodies unchanged'}]}
pending = ['Interface']
while pending:
    module = pending.pop()
    if module in manifest['modules']:
        continue
    relative = Path(module.replace('.', '/') + '.lean')
    destination = HERE / relative
    if module in ['Interface', 'AnalyticInterface']:
        source = destination
    else:
        source = CANONICAL / relative
        if not source.is_file():
            source = UPSTREAM / relative
        assert source.is_file(), (module, source)
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            assert destination.read_bytes() == source.read_bytes(), module
        else:
            shutil.copy2(source, destination)
    contents = destination.read_bytes()
    imports = []
    for line in contents.decode().splitlines():
        if line.startswith('import '):
            imports.extend(line[7:].split())
    local = []
    for dependency in imports:
        if dependency.split('.')[0] not in ['Mathlib', 'Lean', 'Std', 'PrimeNumberTheoremAnd']:
            local.append(dependency)
            pending.append(dependency)
    manifest['modules'][module] = {'source': str(source), 'destination': str(relative),
        'sha256': sha(contents), 'local_imports': local, 'imports': imports}

roots = sorted({name.split('.')[0] for name in manifest['modules']})
# Preserve the warm v4.35 context/options; each C build has its own .lake.
config = (CANONICAL / 'v435/lakefile.toml').read_text().split('[[lean_lib]]', 1)[0]
config = config.replace('defaultTargets = ["Unified108"]', 'defaultTargets = ["Interface"]')
config += ''.join('\n[[lean_lib]]\nname = ' + json.dumps(root) + '\n' for root in roots)
(HERE / 'lakefile.toml').write_text(config)
(HERE / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
lock = json.loads((CANONICAL / 'v435/lake-manifest.json').read_text())
(HERE / 'lake-manifest.json').write_text(json.dumps(lock, indent=2) + '\n')
(HERE / '.lake').mkdir(exist_ok=True)
packages = HERE / '.lake/packages'
if not packages.exists():
    packages.symlink_to((CANONICAL / 'v435/.lake/packages').resolve(), target_is_directory=True)
# Copy only byte-matched, version-correct compiled prerequisites, never target products.
copied = []
for module, entry in manifest['modules'].items():
    if module in ['Interface', 'AnalyticInterface']:
        continue
    relative = Path(module.replace('.', '/'))
    parent = CANONICAL / 'v435/.lake/build/lib/lean' / relative.parent
    if not parent.exists():
        continue
    for source in parent.glob(relative.name + '.*'):
        if source.is_file():
            destination = HERE / '.lake/build/lib/lean' / relative.parent / source.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            copied.append(str(destination.relative_to(HERE)))
manifest['warm_products_copied'] = copied
manifest['toolchain'] = 'leanprover/lean4:v4.35.0'
manifest['pnt_revision'] = '127b50e33f6033e2147921167a117af96d9ba4ea'
manifest['mathlib_revision'] = next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib')
(HERE / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copy2(UPSTREAM / 'LICENSE', HERE / 'LICENSE')
(HERE / 'log').mkdir(exist_ok=True)
print('Prepared', len(manifest['modules']), 'local source modules; copied', len(copied), 'warm products.')
