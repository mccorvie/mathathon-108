#!/usr/bin/env python3
"""COMPUTED source checks for C0 only, Codex lane C.
Re-derivation of Fauzan's theorem reusing Firsching's formalisation
(Apache-2.0, mo271/Zeta5 be1c0d82; Comparator metadata Paul-Lez).
No target proposition is proved or certified by this script.
"""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
manifest = json.loads((here / 'SOURCE_MANIFEST.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
copied = []
for name, record in manifest['modules'].items():
    data = (here / record['destination']).read_bytes()
    assert sha(data) == record['sha256'], name
    if name not in ['Interface', 'AnalyticInterface']:
        source = Path(record['source'])
        if source.is_file():
            assert data == source.read_bytes(), name
        copied.append(name)
interface = (here / 'Interface.lean').read_text()
assert not re.search(r'^(?:theorem|lemma|axiom)\s', interface, re.M)
assert 'def IrrationalFiveStatement : Prop := ∃ x, Irrational x ∧ riemannZeta 5 = x' in interface
assert 'normalizerSharp 5 6 (40 * n) (3 * n) 400' in interface
assert 'explicitAllocation 5 6 (40 * n) (3 * n) 400' in interface
assert 'def ClosingStatement : Prop := Mathathon.P108.thetaPkg 5 6 (3 / 40) 400 u < 0' in interface
result = dict(status='COMPUTED C0 source integrity only; no target proof',
    author='Codex lane C', local_modules=len(manifest['modules']),
    byte_exact_copied_modules=len(copied), interface_target_proofs=0,
    exact_upstream_conclusion=True, actual_sharp_normalizer=True,
    actual_explicit_allocation=True, actual_closing_object=True)
(here / 'SOURCE_CHECK.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
