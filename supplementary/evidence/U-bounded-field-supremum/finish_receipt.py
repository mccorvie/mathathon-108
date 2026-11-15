"""COMPUTED exact gate/source receipt and human sheet. No human status upgrade."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,re,hashlib,shutil
B=Path('problems/108-zeta-odd-autopsy/evidence');p=B/'U-bounded-field-supremum';h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();now=datetime.now(ZoneInfo('America/Los_Angeles'))
g=(p/'log/LEAN_CHECK.md').read_text();assert '**Overall: PASS**' in g
rows=re.findall(r'^\| `([^`]+)` \| \*\*PASS\*\* \| (.*?) \|',g,re.M);assert len(rows)==10
raw=(p/'.lake/final-build.stdout').read_text();axioms=[]
for d,ax in rows:
 assert ax=='propext, Classical.choice, Quot.sound'
 line="'"+d+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
 assert raw.count(line)==1,(d,raw.count(line));axioms.append(line)
(p/'log/parent-axioms.txt').write_text('\n'.join(axioms)+'\n')
for f in ['final-build.stdout','final-build.stderr','positive-build.stdout','positive-build.stderr','attempt1-positive-build.stdout','attempt1-positive-build.stderr','attempt2-positive-build.stdout','attempt2-positive-build.stderr','parent-gate.stdout','parent-gate.stderr']:
 shutil.copyfile(p/'.lake'/f,p/'log'/f)
# All direct/transitive logical source copies remain frozen.
q=B/'U-extended-field-margin';m=json.loads((q/'parent-source-check.json').read_text())
for f,v in m['local_sources'].items():assert h(q/f)==v
q=B/'U-borel-ae-field';s=json.loads((q/'source-sha256.json').read_text())
for f,v in s['local_sources'].items():assert h(q/f)==v
for f,v in s['licenses'].items():assert h(q/f)==v
other={}
for name,src in [('U-field-coercivity','FieldCoercivity.lean'),('U-extended-optimization','ExtendedOptimization.lean')]:
 q=B/name;prev=json.loads((q/'parent-source-check.json').read_text());assert h(q/src)==prev.get('main_source_sha256',prev.get('source_sha256'))
 other[name]={'source':src,'source_sha256':h(q/src),'lakefile_sha256':h(q/'lakefile.toml'),'manifest_sha256':h(q/'lake-manifest.json'),'toolchain_sha256':h(q/'lean-toolchain')}
manifest=json.loads((p/'lake-manifest.json').read_text());deps={a['name']:a for a in manifest['packages']};assert deps['mathlib']['rev']=='0df444a360eaa60ab8c11dca51a86af692955474'
for name,folder in [('UExtendedOptimization','U-extended-optimization'),('UFieldCoercivity','U-field-coercivity')]:assert deps[name]['dir']=='../'+folder
refs=[('Mathlib/Analysis/SpecialFunctions/Log/Basic.lean','303-319','log_sqrt and log_le_self'),('Mathlib/Data/EReal/Basic.lean','576,614-645','ofReal/ENNReal coercion and its order/nonnegativity'),('Mathlib/Data/EReal/Operations.lean','282,388','EReal neg_le_zero and monotone subtraction'),('Mathlib/Data/EReal/Inv.lean','154-160','nonnegative multiplication monotonicity')]
rec={'status':'COMPUTED source/config seal and completed-gate receipt; no human comparison','source_sealed_at_pt':now.isoformat(),'gate_run':'2026-11-14T18:01-08:00','gate_declarations':[a for a,_ in rows],'gate_sha256':h(p/'log/LEAN_CHECK.md'),'local_sources':{f:h(p/f) for f in ['PositiveEnvelope.lean','BoundedFieldSupremum.lean']},'local_config':{f:h(p/f) for f in ['lakefile.toml','lake-manifest.json','lean-toolchain']},'direct_dependencies':other,'unchanged_previous_closure_sources':{'E234':len(m['local_sources']),'E231':len(s['local_sources'])},'license_hashes_checked':len(s['licenses']),'mathlib_sources':[{'path':'.lake/packages/mathlib/'+f,'lines':ls,'use':use,'sha256':h(Path('.lake/packages/mathlib')/f)} for f,ls,use in refs],'all_axiom_outputs_standard_three':True,'failed_positive_envelope_attempts':'Two logical failed stages preserved; none credited. One repeated shell invocation with wrong cwd repeated the first failure; native transcript discloses it. Final build and gate completed exit0.'}
(p/'parent-source-check.json').write_text(json.dumps(rec,indent=2)+'\n')
(p/'README.md').write_text('''# E239 / U44: finite actual field supremum and unconditional optimized real margin

Author: Codex driver for [team member], lane U, event work14November2026.

**LEAN-CHECKED — Completed supporting gate.** Ten selected declarations PASS in the repository gate, run18:01PT, Lean/Mathlibv4.33.1. All transitive axiom lists are exactly [propext, Classical.choice, Quot.sound]. Exact types are in log/LEAN_CHECK.md and completed exit0 compiler prints in log/parent-axioms.txt. Positive-envelope failed stages are archived separately and receive no credit. The source/configuration seal is in parent-source-check.json.

**CONJECTURE — Overall/human status.** E201/I4 remain CONJECTURE: “Lean gate passes; statement not yet compared.” No human verdict. The theorem concerns exactly E237's explicit Borel class, not an asserted equivalence with the paper's admissibility class.

**LEAN-CHECKED — Genuine global field bound.** For any real Borel rho with almost-everywhere |y|<=R and mass37/40, and every t>=0, the actual extended potential is at most2*(37/40)*sqrt(t+max(R,0)). This upper bound allows atoms and an infinite negative part; it does not infer ordinary section integrability everywhere. E238 proves5sqrt(t)-3<=V6(t) using the ORIGINAL J interval integrals with genuine endpoint integrability. Combining sqrt(t+max(R,0))<=sqrt(t)+sqrt(max(R,0)) and4*(37/40)<5 gives the explicit global extended-field majorant

    2*potential(t)-V6(t) <= (37/10)*sqrt(max(R,0))+3.

Thus the actual EReal fieldSup is not+infinity, with no supplied H or field-growth/finiteness premise.

**LEAN-CHECKED — Actual optimized real consequences.** For every finite atomless real Borel rho with almost-everywhere bounded carrier, mass37/40 and ordinarily Integrable self-product logarithm, the actual fieldSup is finite at BOTH ends: E237 excludes-infinity and this probe excludes+infinity. Therefore the REAL actual optimized energy

    (37/40)*fieldSup(rho).toReal - actual_nested_log_energy(rho) + C6

exceeds-139/100, and the literal thetaPkg(7,6,3/40,M,that energy)>9/10 for EVERY REAL M>=40. There is no supplied field majorant, numeric energy floor or field-supremum-finiteness premise.

**LEAN-CHECKED — Finite real infimum value.** Every optimized EReal objective in E237's explicit class is finite. The actual square15 trial belongs to that class, so its finite objective bounds the infimum from above. The fixed uniform witness bounds it from below. Hence the explicit nonempty-class EReal infimum is finite at both ends and its actual real value exceeds-139/100. No minimizer or attainment statement is made.

**PROOF-DRAFT — Human proof route.** Mathlib log(sqrt x)=logx/2 and logu<=u yield logx<=2sqrtx even at zero. The triangle inequality and the carrier bound give the positive-kernel envelope. Lower-integral monotonicity and the exact mass give its integrated bound. The negative-part lower integral is nonnegative, so subtracting it can only decrease the extended potential; no negative-part finiteness is needed. E238's genuine J estimates give the confining field lower bound. The explicit majorant bounds its supremum. E237 then supplies the actual optimized witness/floor/package statements, with its finite-supremum condition now discharged. Class nonemptiness and the uniform witness give a finite infimum. The strict infimum conclusion uses one fixed uniform witness, not separate pointwise strictness alone.

**COMPUTED — Parent/source verification.** The two own logical source files import the frozen E237 and E238 projects. All4 E234 and153 heavy E231 logical source hashes,2 licenses, both direct dependency source/configuration hashes and4 consulted Mathlib files were revalidated. No copied proof/import adapter, root pin edit, Mathathon edit or vendor mutation. Earlier failures were term-order/EReal-negation API mismatches; the final actual source builds and all10 gates pass. Raw tracked compiler logs are copied only after process completion.

**CITED — Attribution.** The canonical angular/log-energy proof implementation is Moritz Firsching's pinned mo271/Zeta5 code; Paul-Lez contributed Comparator metadata. Earlier exact source maps/licenses and the pre-event [team member] fixed-s7 audit credit remain intact. E238's actual integral-field estimate and E237's optimization are event work by the named Codex driver/native worker. Additional envelope/coercion/order facts use Mathlib at the pinned commit. No novelty or first-formalization claim; see ../U-energy-witness-lean/ATTRIBUTION.md.

**CONJECTURE — Remaining boundary.** Finite bounded atomless mass37/40 and self-log-product integrability are still explicit. A paper local-mass condition is not silently identified with them. No full admissibility equivalence, real determinant upper bound, E13 valuation bridge or irrationality theorem is proved here. This completes the current U actual-energy/optimization chain; the human-proposed compact-zeta5 lane can reuse these canonical arcsine/field definitions, but still needs a PRIMAL upper certificate rather than this dual lower certificate.

**COMPUTED — Reproduction.** From repository root with the frozen relative dependencies present:

```sh
ulimit -n 16384
PATH=/Users/[user]/.elan/bin:$PATH python3 scripts/lean_check.py --root problems/108-zeta-odd-autopsy/evidence/U-bounded-field-supremum --lib BoundedFieldSupremum --decl U44.positive_lintegral_sqrt_upper --decl U44.extendedPotential_sqrt_upper --decl U44.field_explicit_majorant --decl U44.fieldSup_ne_top --decl U44.optimized_energy_floor_real --decl U44.package_margin_optimized --decl U44.optimizedEnergy_finite --decl U44.optimalEnergy_ne_top --decl U44.optimalEnergy_ne_bot --decl U44.optimal_energy_floor_real
```

Exact human comparison types and blank receipt are in HUMAN_SHEET.md.
''')
types=g.split('## Statements (a human must compare each with the claim in the report)\n',1)[1].split('## Source scan',1)[0]
(p/'HUMAN_SHEET.md').write_text('''# E239 exact optimized real-energy comparison

**CONJECTURE — Human status.** No human verdict. “Lean gate passes; statement not yet compared.” Compare the explicit E237 class and model before applying to a paper-defined U(6;rho) or U*(6).

**LEAN-CHECKED — Exact successful statements.** Ten-target repository gate PASS18:01PT; standard three axioms only. The following type blocks are copied exactly from log/LEAN_CHECK.md.

'''+types+'''\n**CITED — Model references.** E237/HUMAN_SHEET.md has the seven exact definitions of fieldValues,fieldSup,selfEnergy,optimizedEnergy,ComparisonClass,objectiveValues and optimalEnergy. E234/HUMAN_SHEET.md has the canonical explicit extended potential. All are imported unchanged; this probe adds no alternative model definition. E238 uses the actual J(a,t)=interval-integral log(t+u^2) and V6 from the same frozen dependency.

**PROOF-DRAFT — Points to compare.** Verify actual fieldSup is bounded by the explicit real majorant, not an assumed scalar. Negative-part finiteness is not claimed at every point; finite fieldSup follows from an upper envelope. Check ordinary self-product-log integrability and atomlessness remain explicit. For the real infimum, check both finite bounds and actual sigma nonemptiness. For compact-zeta5 work, this is a dual LOWER certificate, not the required primal UPPER certificate.

Human name/date: ____________________
Per-declaration model/statement comparison: ____________________
Paper-class inclusion checked or remaining gap: ____________________
Finite-supremum/infimum interpretation checked: ____________________
Verdict and BOARD record: ____________________
''')
print('E239 receipt complete',now.isoformat(),'10gates,2ownlogical sources; explicit finite optimized real objective and infimum.')
