# E414 conditional real bound
**LEAN-CHECKED parent update17:53:** the original finite real-bound target now has NOconfiguration premise (Closuregate4/4PASS6.691s), and its actual fixed-s leading-U bound has NOfinite-bound premise (Leadinggate3/3PASS6.677s). Humancomparisonpending. Exacttypes/standardaxioms: log/FULL_REAL_BOUND_LEAN_CHECK.md andLEADING_LEAN_CHECK.md; seePARENT_STATUS.md. Earlier conditional milestones below are retained as history.


Codex, lane B, November 14, 2026.

**PROOF-DRAFT:** `RealProof.lean` proves the posted `RealBoundFromConfigurationStatement`, with precisely the unchanged named `PriorConfigurationEnergyStatement` as premise. It concludes the exact `RealBoundStatement` for every natural s>=2 and n>=1, for actual AperyS.FS, actual zetaS, actual Apery.U and actual B5 constant. The separate `Closure.lean` now derives that exact configuration premise from unchanged prior `energy_ineq_final` and supplies `real_bound_unconditional`; `Leading.lean` then supplies both actual fixed-s asymptotic endpoints. Parent gates are complete as above; human statement comparison remains pending.

**PROOF-DRAFT:** `Scalar.lean` identifies actual D and SS with the fixed-shape legacy definitions by definitional equality. The scalar is positive. The scalar Stirling estimate follows the pinned upstream proof, independently of s. Actual FS positivity follows from scalar positivity and the actual Gram determinant positivity already proved in B11.

**PROOF-DRAFT:** `Pointwise.lean:integrand_le` sets K=40n and t_i=(y_i/K)^2. Positivity and injectivity transfer from y to t. The Vandermonde logarithm separates into scaling and pair-energy terms. The two Riemann-sum estimates for log D and the actual density envelope give the same fixed external field as upstream. Only the density polynomial degree becomes s. The unchanged configuration hypothesis then yields exp(Aconst(n))*product g_(s,K)(y_i), with the field losses 5h and 6h log K retained exactly.

**PROOF-DRAFT:** `IntegralBound.lean:log_delta_le` uses the actual E415 determinant identity, its unconditional integrability, and almost-everywhere positivity/injectivity of product Lebesgue configurations. The product envelope is integrable by B5 and its integral factors. Each one-variable integral is at most C(s,2pi)*K^(s+1). The factor 1/h! is at most 1. Taking logarithms gives Aconst(n)+h*(log C(s,2pi)+(s+1)log K), with no moment or determinant-identification premise.

**PROOF-DRAFT:** `RealProof.lean:real_bound` adds the scalar estimate and determinant estimate. The K^2 log K terms cancel. Actual `Apery.energy_const` bounds the combined energy coefficient by actual U. The remaining log K coefficient is 16+(s+1)+6=s+23; the linear coefficient is (12log2+17)+6+log C=12log2+23+log C. This is exactly the target inequality. `real_bound_from_configuration` packages it as the unchanged target implication.

**CITED:** The proof follows Firsching and Paul-Lez, mo271/Zeta5 commit be1c0d82070da93c343f93bffd495b8ebc323645: Apery/RealBound.lean:36-109; Apery/EnergyBound.lean:27-194,243-303; tiny reindexing helper Apery/EnergyAtoms.lean:19-25. Apache-2.0; see LICENSE, NOTICE and PROOF_MANIFEST.json. The source is prior work and no novelty is claimed.

**COMPUTED:** `build.json` records the successful default RealProof build on Lean v4.33.1. `build.log` retains the six standard-only axiom lists. `check_source.py` checks all 49 copied-module hashes, the four adapted-module hashes, and the original Statement.lean target hash. Cached products only accelerate checking; they are not claimed as verification.

Commands from this folder:

```sh
PATH=/tmp/lean-4.33.1-linux/bin:$PATH lake build
PATH=/tmp/lean-4.33.1-linux/bin:$PATH lake env lean Audit.lean
python3 check_source.py
```
