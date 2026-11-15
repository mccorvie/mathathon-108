"""COMPUTED final receipts; code stays byte-exact after successful gate.
Codex lane C. Fauzan/Firsching re-derivation, no novelty claim.
"""
from pathlib import Path
import json,hashlib,shutil,datetime
P=Path(__file__).resolve().parent;Q=P/'final/project'
gate=(Q/'log/LEAN_CHECK.md').read_text();assert '**Overall: PASS**' in gate
for name in ['CCertificateSplit.irrational_five','CSplitField.local_field_certificate','SplitClosing.closing_neg']:assert name in gate
shutil.copy2(Q/'log/LEAN_CHECK.md',P/'FINAL_GATE.md')
s=json.loads((P/'SIZE_FINAL_STANDALONE.json').read_text());c=s['current']
assert c['files']==s['physical_project_files']==258 and c['lines']==s['physical_project_lines']==34746
assert c['lines']<52044
old=P.parent/'C-zeta5-compact/project';snap=json.loads((P/'FALLBACK_SNAPSHOT.json').read_text())
for r in snap['files']:assert hashlib.sha256((old/r['path']).read_bytes()).hexdigest()==r['sha256']
reused=[];adapted=[];fresh=[]
for m,r in c['modules'].items():
 data=(Q/r['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==r['sha256']
 f=old/r['path']
 if not f.exists():fresh.append(r['path'])
 elif f.read_bytes()==data:reused.append(r['path'])
 else:adapted.append(r['path'])
assert sorted(adapted)==['ArithInterface.lean','CArithProofs.lean','Interface.lean']
result=dict(author='Codex lane C',evidence='E612',formal_status='LEAN-CHECKED',size_status='COMPUTED',forecast_status='HEURISTIC',
 completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),project=str(Q),declaration='CCertificateSplit.irrational_five',
 statement='∃ x : ℝ, Irrational x ∧ riemannZeta 5 = (x : ℂ)',caller_hypotheses=[],axioms=['propext','Classical.choice','Quot.sound'],
 toolchain='leanprover/lean4:v4.35.0',mathlib='v4.35.0',gate_declarations=5,receiver_gate='FULL_RECEIVER_FINAL.md',standalone_gate='FINAL_GATE.md',
 files=258,lines=34746,unit=s['unit'],baseline_files=282,baseline_lines=69392,reduction_percent=s['reduction_percent'],saved_lines=34646,
 frozen_forecast_lines=35123,forecast_minus_actual_lines=377,forecast_error_percent=100*377/35123,
 T='-32999/5000',B=21,M=1000000,u='-2650371/2000000',closing_cells=153,field_cells=129,primitive_rows=3548,primitive_blocks=57,
 old_reused_byte_exact_modules=len(reused),numeric_instance_adaptations=adapted,new_certificate_and_adapter_modules=len(fresh),
 fallback_E607_hashes_unchanged=len(snap['files']),checkpoint_E611_lines=45184,
 review='Other-family statement comparison and submitted-project integration belong to integrator/L; no label upgrade here.',
 attribution='Fauzan re-derivation reusing Moritz Firsching mo271/Zeta5@be1c0d82, Apache-2.0; Comparator metadata Paul-Lez; event U18/U22/U53/U58 and C workers credited.')
(P/'FINAL_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
(Q/'README.md').write_text('''# Compact numerical certificate variant

**LEAN-CHECKED:** `CCertificateSplit.irrational_five` passes the final gate on
Lean/Mathlib v4.35.0,5/5 declarations, standard three axioms only. Its exact
conclusion is `∃ x, Irrational x ∧ riemannZeta 5 = ↑x`, with no hypotheses.
Human/report statement comparison remains the integrator's responsibility.

This is a re-derivation of Fauzan's theorem reusing Moritz Firsching's
mo271/Zeta5@be1c0d82 formalisation (Apache-2.0; Comparator metadata Paul-Lez),
with attributed event arithmetic and analytic work. No new or independent
irrationality theorem is claimed.

**COMPUTED:**258local Lean files/34746physical source lines, including every
numerical datum, helper and local import. This equals the full import closure.
Baseline E607 has69392lines, so the reduction is49.9279456%. External
Mathlib/PNT are excluded equally from both counts. SOURCE_MANIFEST.json and
log/LEAN_CHECK.md contain the hashes and gate; parent evidence has the study,
source audit, provenance and native transcripts.

Only the numerical certificates and their necessary instances are revised:
T=-32999/5000, finite prefixB=21, arithmetic cutoffM=1000000,
u=-2650371/2000000;153closing cells,129field cells,3548primitive rows.
The reused non-numerical proof bodies remain byte-exact; three instance files
change numerical constants. The finite certificate predicates are discharged with `decide +kernel`.
E607 remains unchanged in the parent repository.

Build with `lake exe cache get`, then `lake build`. Pins and the manifest
are committed; ignored local cache links are only a warm-build convenience,
never a path dependency. The standalone final gate included a successful
build. No clean-build speed claim is made.
''')
freeze=[]
for r in c['modules'].values():freeze.append(dict(path=r['path'],sha256=r['sha256'],lines=r['lines']))
for name in ['lean-toolchain','lakefile.toml','lake-manifest.json','LICENSE','NOTICE','README.md']:
 f=Q/name;freeze.append(dict(path=name,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
(P/'FINAL_SOURCE_FREEZE.json').write_text(json.dumps(dict(author='Codex lane C',status='COMPUTED immutable final source/config/documentation hashes after gate',created_utc=result['completed_utc'],project=str(Q),files=freeze),indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['files','lines','reduction_percent','old_reused_byte_exact_modules','numeric_instance_adaptations','new_certificate_and_adapter_modules','fallback_E607_hashes_unchanged']},indent=2))
