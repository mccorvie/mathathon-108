# E239 / U44: finite actual field supremum and unconditional optimized real margin

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
