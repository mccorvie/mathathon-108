# E436: symbolic sufficient criterion on the fixed Hankel template

Codex for [team member], lane B. **LEAN-CHECKED:** the official
`scripts/lean_check.py --final` gate passes all **17 declarations** on
Lean/Mathlib 4.35.0, including the real-series and standard-zeta headlines.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
`RESULT.json` preserves the exact command, source hashes and native receipts;
`log/LEAN_CHECK.md` contains the printed theorem statements.

For natural s, nu in the literal `ParameterScope` (odd s>=5, even
2<=nu<=10), natural M>=40, and a real u, suppose that for every epsilon>0,
eventually

```
0 < FS_s,nu,40n,3n,37n(xi(s)),
log(FS_s,nu,40n,3n,37n(xi(s))) <= (u+epsilon)*(40n)^2.
```

Then `thetaPkg s nu (3/40) M u < 0` implies that xi(s) is irrational.
`xi_eq_zetaS` identifies xi with the canonical actual real zeta series, and
`riemannZeta_eq_xi` identifies its complex coercion with Mathlib's zeta for
s>=2. `criterion_standard` gives the upstream real-witness conclusion:
there exists an irrational real x with riemannZeta(s)=x.

**LEAN-CHECKED scope:** degree, finite arithmetic side conditions, integer
normalization and normalizer growth are proved inside this project. The
only mathematical inputs to the headline beyond the parameter conditions
are the supplied positive analytic leading bound and negative actual package.
The template fixes K=40n, N=3n, h=37n, alpha=3/40 and E432's literal explicit
allocation. No all-allocation optimum or determinant-content equality is
asserted. The theorem does not supply analytic or sign bounds for new zeta
values. The named non-vacuity instance is C's (5,6,400) route; its producer
names and precise formal-status boundary are recorded in ZetaBridge.lean.

**CITED / adaptation:** GeneralDegree retains Firsching's generic affine
determinant lemma in a new helper namespace and proves the actual functional
is affine, giving FS.natDegree<=h without any s/nu hypothesis. GeneralArith
instantiates E311 and E432 symbolically. Assembly generalizes C's existing
delta/8 proof, and imports the unchanged Apery integer-polynomial criterion.
ZetaBridge uses E416's zeta-identification proof. Source headers/maps retain
Fauzan, Moritz Firsching's mo271/Zeta5@be1c0d82, Paul-Lez Comparator metadata,
the team's pre-event [team handle] machinery and PNT credits. No novelty claim.

**COMPUTED source routing:** CriterionStatement.lean is the byte-exact active
alias of the statement-review file Statement.lean. Import only the former;
the latter is a review copy and would collide with the bridge dependency's
generic Statement module. The package uses the standalone final-version
B bridge as a local Lake dependency. ModelAudit.lean and DEFINITION_INDEX.md
provide the custom model definitions for the required other-family statement
comparison; Mathlib primitives keep their library meanings.

To reproduce, fetch the pinned dependencies, obtain the Mathlib cache, then
run the exact command in RESULT.json. The actual cache preflight here passed
9046 up-to-date targets; no Mathlib source build was scheduled. The initial
audit requested a nonexistent helper name (irrationality_of_main_estimate);
that failed audit is retained in log/INITIAL_GATE_WRONG_HELPER_NAME.md.
The corrected declared name is irrational_of_main_estimate, and the final
17-declaration audit passes. Source code did not change to hide that error.

**Status:** submission-project gating, verbatim report statements and the
other-model-family definition comparison remain for the integrator/W/L
workflow under AGENTS section2. Human review is not a prerequisite.
