"""COMPUTED exact-grid selection; source-line estimates remain HEURISTIC.
Codex lane C; Fauzan re-derivation using Firsching, Apache-2.0.
No Lean invocation. Readable physical source-line cost, including helpers.
"""
from fractions import Fraction as F
from pathlib import Path
import json,datetime,hashlib
p=Path(__file__).resolve().parent; evidence=p.parent
closing=json.loads((evidence/'C-split-closing/LOCAL_REFINEMENT.json').read_text())
field=json.loads((evidence/'C-split-field/FRONTIER.json').read_text())
snapshot=json.loads((p/'FALLBACK_SNAPSHOT.json').read_text())
fixed=snapshot['fixed_noncertificate_lines']; baseline=snapshot['baseline_lines']
rows=[]
for f in field['rows']:
 t=F(str(f['T']))
 cs=[c for c in closing['rows'] if F(c['T_decimal'])==t and F(c['reserve_exact'])>=F(1,10000)]
 if not cs:continue
 c=min(cs,key=lambda c:(c['predicted_generic_closing_lines'], -F(c['reserve_exact'])))
 rows.append(dict(T=str(t),T_decimal=str(f['T']),B=c['B'],M=c['M'],Qupper=c['Qupper'],
  closing_cells=c['cells'],field_cells=f['cells'],closing_lines=c['predicted_generic_closing_lines'],
  field_low=f['generic_low'],field_high=f['generic_high'],fixed_lines=fixed,
  whole_low=fixed+c['predicted_generic_closing_lines']+f['generic_low'],
  whole_high=fixed+c['predicted_generic_closing_lines']+f['generic_high'],
  reserve_exact=c['reserve_exact'],reserve=c['reserve'],u=c['Uupper_exact']))
rows.sort(key=lambda x:(x['whole_high'], -F(x['reserve_exact'])))
selected=rows[0]
assert selected['whole_high']<=baseline*3//4
checks=[]
for f in snapshot['files']:
 q=evidence/'C-zeta5-compact/project'/f['path']
 checks.append(hashlib.sha256(q.read_bytes()).hexdigest()==f['sha256'])
assert all(checks)
result=dict(author='Codex lane C',status='COMPUTED exact arithmetic; HEURISTIC physical source-line predictions',
 attribution='Fauzan re-derivation using Moritz Firsching mo271/Zeta5; Paul-Lez Comparator metadata; Apache-2.0',
 created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_lines=baseline,
 build_threshold_lines=baseline*3//4,selected=selected,rows=rows,
 stress_extra_lines=800,stress_whole_lines=selected['whole_high']+800,
 conservative_reduction_percent=100*(1-selected['whole_high']/baseline),
 closing_only_checkpoint_lines=fixed+16960+selected['closing_lines'],
 fallback_hashes_unchanged=len(checks),
 decision='QUALIFIED for build after 21:30:11 PT; minimum over tested feasible grid, not global optimum',
 rules=['No proof-term golf','No Lean before computation window closes','E607 untouched','Stop 23:00 PT',
 'Every readable data/helper/import line counted; actual whole import closure supersedes prediction'])
if (p/'DECISION.json').exists():
 frozen=json.loads((p/'DECISION.json').read_text());assert frozen['selected']==result['selected']
 (p/'RECHECK.json').write_text(json.dumps(dict(status='COMPUTED unchanged frozen selection and fallback hashes',verified_utc=result['created_utc'],original_prediction_utc=frozen['created_utc'],selected=result['selected'],fallback_hashes_unchanged=len(checks)),indent=2)+'\n')
else:
 (p/'DECISION.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# E608 split computation','', '**COMPUTED:** exact rational witness checks and selection in `select_split.py`; **HEURISTIC:** all source-line forecasts below.','',
'Fauzan re-derivation reusing Moritz Firsching\'s formalisation; Paul-Lez Comparator metadata. No novelty claim.','',
'Computation window: Sat 21:00:11–21:30:11 PT. No Lean invocation or `.lean` edit during this window.','',
'| T | B | M | Closing lines | Field lines (upper) | Whole project (upper) | Exact reserve (decimal) |',
'|---|---:|---:|---:|---:|---:|---:|']
for x in rows:lines.append(f"| {x['T_decimal']} | {x['B']} | {x['M']} | {x['closing_lines']} | {x['field_high']} | {x['whole_high']} | {x['reserve']:.10f} |")
lines+=['',f"**HEURISTIC selected forecast:** {selected['whole_high']:,} whole-project Lean source lines, {result['conservative_reduction_percent']:.2f}% below 69,392. Includes {fixed:,} fixed lines and all proposed numerical helpers/data; +800 stress lines gives {result['stress_whole_lines']:,}. Build threshold is 52,044.",
'',f"**COMPUTED selection:** T={selected['T']}, B={selected['B']}, M={selected['M']}, Q≤{selected['Qupper']}, u={selected['u']}; exact reserve {selected['reserve_exact']}. Minimum tested source-cost split, not a global minimum.",
'', '**HEURISTIC checkpoint:** replace closing certificate first; retaining the full old field cover predicts '+str(result['closing_only_checkpoint_lines'])+' lines and also qualifies. Then attempt the data-driven field certificate. Physical readable source lines throughout; no proof-term packing.',
'', f"**COMPUTED immutability:** all {len(checks)} frozen E607 hashes unchanged. Build in new lane C folders only. Stop at 23:00 with most recent final-gate PASS; retain E607 if no new variant passes.",
'', 'Evidence: `../C-split-closing/LOCAL_REFINEMENT.json`, `../C-split-field/FRONTIER.json`, `../C-split-numeric/ALL_PRIMITIVES.json`; code, schema validation and source references in those folders.']
if not (p/'README.md').exists():(p/'README.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:result[k] for k in ['selected','stress_whole_lines','closing_only_checkpoint_lines','fallback_hashes_unchanged']},indent=2))
