#!/usr/bin/env python3
"""COMPUTED canonical source assembly, Codex native outer_sum, E432 lane B.

Only this new probe is written. Mathematical bodies are exact source copies;
Statement/GammaCells are import-only adapters. check_sources.py replays the
shared-body comparisons. No compiled cache products are copied by this script.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re
import shutil

r = Path(__file__).resolve().parent
e = r.parent
bases = [e/'B-normalizer-limit', e/'B-inner-sum', e/'B-inner-explicit']
choices = {
    'RangeTargets': bases[0]/'RangeTargets.lean',
    'OuterTargets': bases[0]/'OuterTargets.lean',
    'ExplicitTargets': bases[0]/'ExplicitTargets.lean',
    'Dictionary': bases[1]/'Dictionary.lean',
    'ContinuousClasses': bases[2]/'ContinuousClasses.lean',
}
adapters = {
    'Statement': '/- Import-only canonical E420 target adapter; exact body is in ExplicitTargets.lean. -/\nimport ExplicitTargets\n',
    'GammaCells': '/- Import-only canonical gamma-cell adapter; identical bodies are retained in full Continuity.lean. -/\nimport Continuity\n',
}

pending = ['Completion', 'InnerSum', 'InnerLocal']
done = {}
coalesced = []
while pending:
    mod = pending.pop()
    if mod in done:
        continue
    rel = Path(mod.replace('.', '/')+'.lean')
    if mod in adapters:
        data = adapters[mod].encode()
        source = None
        dst = rel
    else:
        candidates = []
        for base in bases:
            p = base/rel
            if not p.exists():
                p = base/'vendor'/rel
            if p.exists():
                candidates.append(p)
        if mod in choices:
            p = choices[mod]
        else:
            assert candidates, mod
            p = candidates[0]
            for q in candidates[1:]:
                if p.read_bytes() != q.read_bytes():
                    diff = '\n'.join(list(difflib.unified_diff(
                        p.read_text().splitlines(), q.read_text().splitlines(), n=1))[:20])
                    raise RuntimeError(f'unexpected source conflict {mod}\n{diff}')
        data = p.read_bytes()
        source = str(p)
        dst = Path('vendor')/rel if mod.split('.')[0] in ('Mathathon', 'Zeta5S') else rel
        if len(candidates) > 1:
            coalesced.append(dict(module=mod, canonical=str(p), origins=[str(q) for q in candidates],
                                  identical=all(p.read_bytes() == q.read_bytes() for q in candidates)))
    q = r/dst
    q.parent.mkdir(parents=True, exist_ok=True)
    q.write_bytes(data)
    deps = []
    for line in data.decode().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.split('.')[0] not in ('Mathlib', 'PrimeNumberTheoremAnd', 'Lean', 'Std'):
                    deps.append(dep)
                    pending.append(dep)
    done[mod] = dict(source=source, destination=str(dst), sha256=hashlib.sha256(data).hexdigest(),
                     imports=deps, adapter=mod in adapters)

for name in ('lean-toolchain', 'lake-manifest.json'):
    shutil.copy2(bases[0]/name, r/name)
roots = sorted({m.split('.')[0] for m in done})
lines = ['name = "BFullBridge"', 'defaultTargets = ["Final"]', '[leanOptions]',
         'autoImplicit = false', 'relaxedAutoImplicit = false',
         '[[require]]', 'name = "mathlib"', 'scope = "leanprover-community"',
         'git = "https://github.com/leanprover-community/mathlib4.git"', 'rev = "v4.33.1"',
         '[[require]]', 'name = "PrimeNumberTheoremAnd"',
         'git = "https://github.com/mo271/PrimeNumberTheoremAnd"',
         'rev = "04d81b2a68ea3548b9990813fdc463c78511f412"']
for name in roots+['Final']:
    lines += ['[[lean_lib]]', f'name = "{name}"']
    if name in ('Mathathon', 'Zeta5S'):
        lines += ['srcDir = "vendor"']
(r/'lakefile.toml').write_text('\n'.join(lines)+'\n')
(r/'.lake').mkdir(exist_ok=True)
packages = r/'.lake/packages'
if not packages.exists():
    packages.symlink_to('/tmp/lane-b-zeta5/.lake/packages', target_is_directory=True)
licenses = []
for name in ('LICENSE.Zeta5-Apache-2.0', 'NOTICE.L-zeta5-general-s'):
    p = bases[0]/name
    if not p.exists():
        p = bases[2]/name
    if p.exists():
        shutil.copy2(p, r/name)
        licenses.append(dict(source=str(p), destination=name,
                             sha256=hashlib.sha256(p.read_bytes()).hexdigest()))

(r/'SOURCE_MANIFEST.json').write_text(json.dumps(dict(
    status='COMPUTED exact canonical sources plus two import-only adapters; see build-check.json for build status',
    author='Codex native outer_sum,E432laneB', modules=done, licenses=licenses,
    coalesced_sources=coalesced), indent=2)+'\n')
print('Prepared', len(done), 'modules,', len(licenses), 'licenses; adapters', list(adapters))
