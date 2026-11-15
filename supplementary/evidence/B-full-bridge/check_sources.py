#!/usr/bin/env python3
"""COMPUTED exact-source and canonical-body replay, Codex outer_sum E432.

This reads frozen origins and writes only this probe's computed audit files.
It does not run Lean and does not give a human statement-comparison verdict.
"""
from pathlib import Path
import hashlib
import json
import re

r = Path(__file__).resolve().parent
e = r.parent
repo = r.parents[3]
manifest = json.loads((r / 'SOURCE_MANIFEST.json').read_text())

def digest(data):
    return hashlib.sha256(data).hexdigest()

def origin(path):
    p = Path(path)
    return p if p.is_absolute() else repo / p

adapters = {
    'Statement': '/- Import-only canonical E420 target adapter; exact body is in ExplicitTargets.lean. -/\nimport ExplicitTargets\n',
    'GammaCells': '/- Import-only canonical gamma-cell adapter; identical bodies are retained in full Continuity.lean. -/\nimport Continuity\n',
}
exact = 0
for name, row in manifest['modules'].items():
    data = (r / row['destination']).read_bytes()
    assert digest(data) == row['sha256'], name
    if row['adapter']:
        assert data == adapters[name].encode(), name
    else:
        assert data == origin(row['source']).read_bytes(), name
        exact += 1
for row in manifest['licenses']:
    data = (r / row['destination']).read_bytes()
    assert digest(data) == row['sha256']
    assert data == origin(row['source']).read_bytes()

assert (r / 'RangeTargets.lean').read_bytes() == (e / 'B-range-statements/Statement.lean').read_bytes()
assert (r / 'ExplicitTargets.lean').read_bytes() == (e / 'B-inner-explicit/Statement.lean').read_bytes()

# E429 Dictionary changes only which literal target module is imported.
def nonimports(path):
    return '\n'.join(x for x in path.read_text().splitlines() if not x.startswith('import ') and x.strip())
assert nonimports(e / 'B-inner-explicit/Dictionary.lean') == nonimports(r / 'Dictionary.lean')

# E420's full module contains E429's continuous-class body unchanged.
short = (e / 'B-inner-sum/ContinuousClasses.lean').read_text()
full = (r / 'ContinuousClasses.lean').read_text()
short_body = short[short.index('def aCount'):short.rindex('\nend\n')]
extra = full.index('theorem finite_class_integral_approx')
extra_doc = full.rfind('/--', 0, extra)
full_body = full[full.index('def aCount'):extra_doc].rstrip()
assert short_body.rstrip() == full_body

# E429's ClassCells was an extraction, now unused: full ClassSums is canonical.
def definition(text, name):
    start = re.search(r'(?m)^(?:noncomputable )?def ' + name + r'\b', text).start()
    tail = text[start:]
    stop = re.search(r'\n\n|\n(?=(?:noncomputable )?def |end\b)', tail)
    return tail[:stop.start() if stop else len(tail)].rstrip()
cells = (e / 'B-inner-sum/ClassCells.lean').read_text()
sums = (r / 'ClassSums.lean').read_text()
four = ['cvLo', 'cvHi', 'bcoef', 'ccount']
for name in four:
    assert definition(cells, name) == definition(sums, name), name
assert 'ClassCells' not in manifest['modules']

# E420's GammaCells was an exact extraction of E429 Continuity.
gamma = (e / 'B-inner-explicit/GammaCells.lean').read_text()
continuity = (r / 'Continuity.lean').read_text()
gamma_body = gamma[gamma.index('def gammaTable'):gamma.rindex('\nend\n')]
continuity_body = continuity[continuity.index('def gammaTable'):continuity.index('theorem continuousAt_floorCast')].rstrip()
assert gamma_body.rstrip() == continuity_body

source_check = dict(status='COMPUTED exact source/hash replay; not a human verdict',
    modules=len(manifest['modules']), licenses=len(manifest['licenses']),
    exact_source_modules=exact, import_only_adapters=sorted(adapters),
    canonical_target_definitions_byte_exact=True, all_pass=True)
(r / 'source_check.json').write_text(json.dumps(source_check, indent=2) + '\n')
shared = dict(status='COMPUTED exact shared-body coalescing checks; not a human verdict',
    canonical_ContinuousClasses='B-inner-explicit/ContinuousClasses.lean',
    shared_ContinuousClasses_body_exact=True, only_extra_theorem='finite_class_integral_approx',
    Dictionary_import_only_change=True, ClassCells_not_in_import_closure=True,
    four_definitions_exact=four, Statement_import_adapter='ExplicitTargets',
    GammaCells_import_adapter='Continuity',
    three_gamma_cell_bodies_exact=['gammaTable', 'gammaCells', 'integral_gamma_cells'], all_pass=True)
(r / 'CANONICAL_SHARED_CHECK.json').write_text(json.dumps(shared, indent=2) + '\n')
print(json.dumps(source_check))
