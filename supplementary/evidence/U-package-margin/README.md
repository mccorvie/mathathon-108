# E213 / U18: arithmetic cell of the defined package margin

Author: Codex, lane U for [team member]; event work, Sat Nov 14 2026, started 13:46 PT.
Integrator's assignment/cap started 13:44 PT; bounded checkpoint 14:29 PT.
Agents working on: `u5_energy_explainer` only. Parent owns the repository gate, logs, board, and Git.

**CONJECTURE — Overall status and scope.** The statements below are complete Lean proof candidates about the **literal root package definitions**, accepted by direct Lean v4.33.1 compilation with standard axioms only. The parent performs the separate repository gate and human statement comparison. The overall analytic result remains CONJECTURE. No theorem here derives Fauzan's valuation bounds (E13), identifies the analytic input with a measure-theoretic infimum, or proves irrationality or rationality of a zeta value.

## Final all-real-cutoff composition

**CONJECTURE — `U18.arithmetic_allM_strict`.** For every real \(M\ge40\),

\[
\frac{229}{100}<\operatorname{Mathathon.P108.thetaPkg}(7,6,3/40,M,0).
\]

There is no assumed numerical cutoff bound in this theorem: `arithmetic200_strong` discharges the tail theorem's required 200-cutoff premise. The finite prefix theorem covers real cutoffs from 40 through 200; E217/U22's `arithmetic_tail_gt_exact` covers every real cutoff at least 200.

**CONJECTURE — `U18.theta_allM_gt`.** For all real \(M\ge40\) and all real \(U>-139/100\),

\[
\frac9{10}<\operatorname{Mathathon.P108.thetaPkg}(7,6,3/40,M,U).
\]

**CONJECTURE — Explicit witness corollaries.** `theta_allM_lb6Square15` substitutes the E206 explicit expression for every real cutoff at least 40, while `theta_allM_of_witness_le` permits any real input above that expression. The measure-theoretic identification of that expression remains a separate dependency.

**COMPUTED — Final composition check.** `AllM.lean` and the three unchanged copied E217 tail modules compile under Lean v4.33.1. All four final main declarations print exactly `[propext, Classical.choice, Quot.sound]`. Logical source/configuration froze at 14:33:23 PT for the parent's combined gate. The parent M200 gate previously passed all five requested targets; its output is retained in `log/LEAN_CHECK-M200.md`. No human status upgrade is made here.

## Milestone a: the requested cutoff

**CONJECTURE — `U18.theta200_gt`.** For every real \(U>-139/100\),

\[
\frac9{10}<\operatorname{Mathathon.P108.thetaPkg}
 \left(7,6,\frac3{40},200,U\right).
\]

The target uses the unchanged definitions copied from `Mathathon/P108/`: `innerR`, `innerGamma`, `innerN`, `Iout`, and `thetaPkg` retain their names and exact bodies. The last definition is

\[
\Theta(s,\nu,\alpha,M,U)
=U+I_{\rm out}(s,\nu,\alpha)
+\frac{(s+1)(1-\alpha)}M
+\int_3^M\frac{R_{s,\nu,\alpha}(x)}{x^3}\,dx.
\]

**CONJECTURE — Strong arithmetic certificate.** `U18.arithmetic200_strong` proves

\[
\frac{2323}{1000}<
I_{\rm out}(7,6,3/40)+\frac{8(1-3/40)}{200}
+\int_3^{200}\frac{R_{7,6,3/40}(x)}{x^3}\,dx.
\]

`arithmetic200_lower` records the weaker \(229/100\) lower bound used by the requested sign theorem. `innerIntegral200_value` proves the full exact rational integral from the definitions; no stored rational value is a premise.

**CONJECTURE — Combination with E206.** `U18.theta200_lb6Square15` substitutes the explicit expression `U11.lb6Square15` from E206, using its existing proof `U11.lb6Square15_gt`; `theta200_of_witness_le` covers any real \(U\) above that expression. This is a statement about that explicit expression and the defined package. Its identification as a lower bound for every admissible comparison-measure energy is a separate analytic dependency.

## Finite part of milestone b

**CONJECTURE — `U18.theta200_le_of_40_le_le200`.** For all real \(40\le M\le200\) and all real \(U\),

\[
\Theta(7,6,3/40,200,U)\le\Theta(7,6,3/40,M,U).
\]

Thus, by transitivity with `theta200_gt`, the same strict \(9/10\) sign bound holds throughout this finite real interval. The monotonicity statement is a separately compiled theorem in `PrefixBounds.lean`; the transitivity is stated here without adding another import to the frozen milestone-a gate snapshot.

**CONJECTURE — Tail composition scope.** The final `AllM.lean` combines this finite prefix with the separate worker's E217/U22 tail proof. The overall analytic theorem remains CONJECTURE and is limited to the literal package definitions stated above.

## How the exact arithmetic is proved

**CONJECTURE — Kernel proof structure.** The interval \([3,200]\) is partitioned into 1,676 rational pieces. For each real \(x\) strictly inside a piece, the proof fixes the relevant integer floors, splits the inner \(z\)-integral at two affine breakpoints, and proves the constant value of `gammaIntegrand` on each open subinterval. Open-interval congruence discards only the endpoint values. This proves an affine identity \(R(x)=a+bx\) on the whole real piece, rather than checking a grid of points. A generic lemma then integrates \((a+bx)/x^3\) exactly, and interval concatenation assembles the pieces. `Iout_7_6 = 27071/16000` comes from the unchanged root `OuterValues.lean` proof.

There are 84 generated chunk modules, each containing at most 20 affine identities and exact integrals. `generate.py` uses the earlier event `margin/theta.py` to propose the partition and rational coefficients, but every proposal is re-proved from the copied root definitions in Lean. A finite-sample affine fit in the generator is not accepted as a mathematical premise. `generated.json` labels those inputs as proposals. The final exact rational recombination is recorded in `comparison.json`, where it matches the stored `certify/out/A.json` key `7:6`; that stored value is used only as a comparison, not read by the generator or assumed by the theorem.

**CONJECTURE — Finite-prefix proof structure.** On the 1,360 pieces covering \([40,200]\), the affine expression is bounded above by \((37/5)x\). `U18.affine_piece_theta_antitone` in `PrefixCore.lean` converts this into a comparison between a variable cutoff inside the piece and its right endpoint. `PrefixBounds.lean` concatenates these comparisons backward to the cutoff 200. Its parameter \(M\) is real, not an integer grid index.

## Tail proof reuse and earlier scout

**CONJECTURE — Compiled period identity.** `PeriodShift.lean` proves `U18.innerR_period40`, for every real \(x\):

\[
R(x+40)-R(x)=222+74\left(\{x\}-6\{3x/40\}\right),
\]

where the braces mean the literal real expressions \(t-\lfloor t\rfloor\). Its proof uses the root `integral_ell`, floor translation, and algebra; no finite numerical checks enter that proof. The direct compiler output is in `period-shift.log`.

**COMPUTED — Tail scout only.** `tail_scout.py` supplies exact proposed polynomial coefficients for \(F,Q,G\) on 340 baseline pieces in \([200,240]\), where

\[
F(x)=\frac{37}{40}\left(6+2\{x\}-12\{3x/40\}\right),\quad
Q(x)=R(x)-xF(x),\quad
G(x)=\int_{200}^x(F(t)-37/40)\,dt.
\]

The exact polynomial range calculation gives \(G\) between \(-37/180\) and \(37/2\), \(Q\) between 0 and \(2790/1849\), and the proposed mean of \(F\) is \(37/40\); 3,060 exact sample checks of translated pieces also pass. These scout ranges and coefficients are **not** a Lean proof of the global primitive bound or tail inequality. The final composition instead reuses the separate worker's fully compiled E217 tail proof, which uses its own weaker sufficient analytic bounds. The scout is retained only as a historical computation.

## Compilation, attribution, and reproduction

**COMPUTED — Checks performed.** All 84 chunk modules, `MarginPieces.lean`, `UPackageMargin.lean`, `PrefixCore.lean`, `PrefixBounds.lean`, and `PeriodShift.lean` were accepted by direct Lean v4.33.1 compilation. The final margin and finite-prefix axiom lists contain only

```text
[propext, Classical.choice, Quot.sound]
```

The source has no proof admissions, native-evaluation tactic, SAT-backed decision tactic, or newly declared axiom. `StatementAudit.lean` is prepared to dump the literal definitions and main statements for comparison. Its 14:24 attempt found a missing chunk object during the parent's fresh Lake trace rebuild; `statement-audit.log` preserves that incomplete attempt, and the parent gate provides the final audit. `compiler-main.log`, `compiler-prefix.log`, `statement-audit.log`, and the chunk JSON/log records preserve actual outputs; the parent gate status is recorded separately by the driver.

The probe has its own v4.33.1 toolchain/Lake configuration. Its ignored `.lake/packages` symlink reads the existing package cache. The root event-source closure is exactly `InnerShift`, `Integrable`, `OuterDefs`, `OuterValues`, and `SStep`; those source files are copied byte-for-byte, retaining Claude Opus 5.5's original attribution. E206's five `Witness/` files are copied unchanged from the earlier event proof by Codex. `source-manifest.json` and `provenance.json` record paths, hashes, and checks. No root file, prior clone, other evidence folder, or shared log was edited.

From this folder, after the pinned dependencies and copied support modules are built:

```sh
python3 generate.py 20
python3 build_chunks.py
python3 finish_build.py
/Users/[user]/.elan/bin/lake env lean -DautoImplicit=false StatementAudit.lean
```

`build_chunks.py` uses four local Lean processes, without spawning agents or using OpenMath OS. Later-stage running logs were written under `/private/tmp` and archived after completion. An earlier tracked build stdout was rewritten during sync; `chunk-build.json` retains all 84 exit codes and elapsed times, while individual chunk logs and the final aggregate compiler remain the verification evidence.

Final combined gate command, from the repository root:

```sh
python3 scripts/lean_check.py --root problems/108-zeta-odd-autopsy/evidence/U-package-margin --lib AllM --decl U18.arithmetic_allM_strict --decl U18.theta_allM_gt --decl U18.theta_allM_lb6Square15 --decl U18.theta_allM_of_witness_le --decl U18.theta200_le_of_40_le_le200
```

The final theorem is in `AllM`; its imports include `UPackageMargin`, `PrefixBounds`, and `PackageTail.Bound`. `lakefile.toml` registers all supporting libraries and includes `AllM`/`PrefixBounds` in `defaultTargets`, so a fresh build does not rely on copied object files. The three `PackageTail/` source files are byte-exact E217 event work, with exact original paths, line ranges, and hashes in `composition-source-manifest.json`. `composition-provenance.json` supplies the updated frozen-source checksums; `composition-build.json` and `composition-*.log` retain actual final compilation outputs. To repeat only the final composition using the existing cutoff trace cache, run `python3 compose_build.py` (after building `PeriodShift`). Parent owns the gate, claim-label decisions, shared-log/source rows, transcript preservation, and Git. No novelty verdict is made here.

Metadata checkpoint completed at 14:27:57 PT on Nov 14 2026. Logical sources and configuration remain frozen for the parent gate.

Final composition metadata completed at 14:34:17 PT; logical/configuration source remains frozen.
