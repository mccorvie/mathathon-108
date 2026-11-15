# Skeptic review of `W-step-bounds/README.md` (two-sided s-step bound)

**This is a same-family review.** The reviewer is Claude Opus 5.5, a fresh-context Claude Code subagent, and the author is
also Claude. It is not a second-family review and not a human check. Sun 15 Nov 2026, 07:15–07:40 PT.

**Scope.** The README sections "Setting", "Statement" (Theorem, Corollaries 1 and 2, the Values table and its two remarks),
"Proof", and "The ζ(5) side, and what this does and does not prove about ζ(7)". Also the report's Claim 2 Statement sentence
and the paragraph `\paragraph{The step at every choice of parameters` (`report/report.tex`, lines 309 and 322–327).

**Ground truth used.** `../../scope_alpha_beta/pkg_ab.py`, imported read-only. Its `PkgAB.R`, `Tout`, `outer_parts`,
`I_out`, `int_R_x3` and `A_M` are the reference. The team scan files `../../scope_alpha_beta/out/scan_*.json` are read-only.

**Independence.** All code here is my own (`rv_core.py`), written from derivation_beta §3. It does not import or copy
`../bounds.py` or any check script. I read the loading lines of `../check_scan.py` and `../zeta5_side.py` only after
my own count disagreed with theirs, to find out which cells "651" means.

**Overall verdict: the theorem and both corollaries hold (PASS).** As statements about pkg_ab's formulas, every proof step is
correct and every hypothesis the proof uses is stated. I found no counterexample: 0 violations at 50 in-domain edge points,
600 random in-domain points (2 seeds) and 754 scan cells, and pkg_ab's exact `I_out` agrees with my own exact integral
everywhere. The problems are in the numbers and the wording around the theorem (tasks 4 and 5: PARTIAL):
- the cell count;
- two lower bounds rounded up;
- "ζ(5) closes" used for "ζ(5)'s floor is negative";
- the reference to E62 as a "ceiling";
- in the report, the hypothesis (iii) left implicit, and one "at every choice" that is too broad.

---

## Task 1. Statement against proof: **PASS** (with wording notes)

**The reduction to the outer integral holds in pkg_ab exactly.**
- *Inner range.* `PkgAB.R` depends on s only through `c_in = s` in Γ. So R_{s+2} − R_s = 2[Σ(T − b)(b_z − a_z) + σ]. This
  equals 2[H_L x − (ν/2)·αx] = 2βx, because ∫_0^{1/2} ℓ(w, z) dz = w for every real w. I checked this exactly at 320 rational
  x ∈ [3, 400] over 8 parameter sets, including α = 0, odd ν and ν = 45 (`rv_exact.out` §A).
- *The M-free step.* With `A_M = I_out + (s+1)β/M + ∫_3^M R/x³` the step is ΔI_out + 2β/M + 2β(1/3 − 1/M) = ΔI_out + 2β/3.
  This is exact at M = 3, 40 and 97/2 (§A).
- *The outer range above y = 1.* In pkg_ab, `Tout` for 1 < y ≤ 2β is only the normaliser term −2β⌊1/y⌋ + Σ_j(2β − jy)₊,
  so it does not depend on s at all, whether or not (iii) holds. I checked this at 240 points, including two parameter sets
  where (iii) fails (§B). (iii) is needed only so that this pkg_ab formula is the derived package (derivation_beta §3,
  Prop. 4.3's p > K case); the inequality does not use it.
- *The normaliser on (1/3, 1].* It is the same s-free term and cancels.
- *Agreement with pkg_ab.* So Θ(s+2) − Θ(s) = 2β/3 + ∫_{1/3}^{1}[g_{s+2} − g_s] dy with g = cost + min(r̂, z). My own exact
  integral of this equals `PkgAB(s+2).I_out() − PkgAB(s).I_out()` + 2β/3 at every in-domain point I tried: 50 edge points
  (§H), 2 × 300 random points (§J) and every 5th scan cell (`rv_numbers.out` §3).
- *How the scan computes the step.* `scan.py` builds `A7 = A5 + (I_out7 − I_out5) + 2β/3` and `sstep` from the same
  identity. So the scan's floor7 − floor5 equals the step by construction (difference ≤ 6.7e−16). The scan does not test
  Prop. 1′ itself; that rests on the derivation's check C3 and on §A here.

**Hypotheses the proof uses, and where they are stated.**
- 0 ≤ α ≤ 1/3, for d ≥ 0 and for the closed form of ∫P. The domain states α < 1/6, which is stronger and is what the
  derivation needs.
- ν an integer, so that the m_i are integers in the δ/e table. This is stated ("any integer ν ≥ 0").
- s odd. Stated.
- z ≥ 0. The proof does not use it; it is only needed for pkg_ab to be defined (`Tout` raises otherwise).
- (iii). Only for the identification above.

Nothing the proof needs is missing. I also probed the integrality hypothesis: at 426 random points with non-integer ν
(`rv_real_nu.out`) the bounds still held. The proof's per-index step does fail there (e(m) = 1 > δ(m) = m + 2 for
m ∈ (−2, −1)), so integrality is genuinely used.

**What the statement covers beyond the derivation (scope notes, not errors).**
- *ν.* The domain allows "any integer ν ≥ 0", but derivation_beta §0, §5 and §6 derive the package only for even ν ≤ 10.
  Odd ν and ν ≤ 22 rest on E732 and E733, which have same-family reviews only. The README says this only for L_a ≥ 0. For
  other ν the theorem is a statement about pkg_ab's formulas.
- *α = 0.* pkg_ab cannot evaluate Θ at α = 0: `int_R_x3` raises ZeroDivisionError in `inner_breaks`, and C* contains
  log α. At α = 0 the step identity holds at the level of R (§A), and the bound holds (6 edge points, §H).
- *s = 3.* Covered, with (iii) A < 1 as the binding condition. At the template (iii) fails at s = 3 for every even ν ≥ 2,
  since A = 1 + (ν − 2)α ≥ 1.
- *β > 1.* The outer integral runs to 2β, and the part above 1 cancels as shown. I tested β = 2, 199/100, 12/5 and 5/2 with
  s = 9 to 13. For β > 2, `outer_kinks` lists 2β/j only for j ≤ 11. The adaptive `pieces` still integrates exactly, and
  pkg_ab agreed with my integral.
- *Saturation "at both s and s+2".* This is redundant, because z_{s+2} ≤ z_s pointwise (checked, §D). Saturation at s + 2
  is enough.
- *Where U-freeness comes from.* The Theorem says "the step is free of both [M and U], by Prop. 1′". M-freeness comes from
  Prop. 1′ plus the crude term. U-freeness comes from U(ν, α, β; ρ) not depending on s (derivation_beta §4), not from
  Prop. 1′.

## Task 2. The proof steps against pkg_ab's formula: **PASS**

- *The decomposition.* My `rv_core.Out`, written from the derivation text, equals `PkgAB.outer_parts` (cost, z, rank)
  exactly at 1620 evaluations, including y = 1/2 and y = 1 (§C). The cost is (s+2)P + Σ d(ℓ)c_s(ℓ), where c_s(ℓ) sums over
  i = 0..ℓ−3, as in the README. The rank term is min(r̂_s, z_s), and the normaliser terms are s-free.
- *Densities.* d(2k) = α − m ≥ 0. d(2k+1) = m − u ≥ 0: if m = α this needs v ≤ y, which holds because y > 1/(k+1); if m = v
  it needs α ≤ y, which holds because α ≤ 1/3 < y. d(2k+2) = u ≥ 0, and the three sum to α. Checked at 5000 random
  (α ≤ 1/3, y) (§E).
- *The per-index facts.* For integer m, δ(m) = (m+2)₊ − (m)₊ is 2, 2, 1, 0 for m ≥ 1, m = 0, m = −1 and m ≤ −2. With
  e = 1[m ∈ {−1, 0}], this gives e ≤ δ ≤ 2.
- *Summing over i.* 0 ≤ Δz1(ℓ) ≤ Δc(ℓ) ≤ 2(ℓ − 2), checked directly from the definitions for s = 3..29, ν = 0..49 and
  ℓ = 2..8. Δz = Σ d Σ_i e(m_i) ≤ Σ d Δc, since d ≥ 0.
- *Monotonicity in s.* r̂ and z are both nonincreasing in s (3000 random points).
- *The min inequality.* For a ≥ a′ and b ≥ b′, 0 ≤ min(a, b) − min(a′, b′) ≤ (a − a′) + (b − b′). In fact it is ≤ max(a − a′,
  b − b′), which would sharpen the lower bound to 2P − (Δr̂ − Δz)₊; the bound as written is not wrong.
- *The pointwise bounds.* Upper: ΔT = 2P + ΣdΔc + [bracket ≤ 0] ≤ 2P + 2Σd(ℓ−2) = 2(1 − y). Lower: ΔT ≥ 2P + ΣdΔc − Δr̂ −
  Δz ≥ 2P − Δr̂. Both hold at 10 000 random points on `PkgAB.outer_parts`, with no z ≥ 0 required (§I).
- *∫P by hand.* Σ_ℓ d(ℓ)(ℓ−2) = (α−m)(2k−2) + (m−u)(2k−1) + u·2k = 2α(k−1) + m + u.
  - k = 1, y ∈ (1/2, 1]: ∫ min(α, 1−y) dy = ∫_0^{1/2} min(α, t) dt = α/2 − α²/2, valid for α ≤ 1/2. ∫(α + 1 − 2y)₊ dy =
    α²/4, valid for α ≤ 1. The sum is **α/2 − α²/4**.
  - k = 2, y ∈ (1/3, 1/2]: ∫ 2α dy = α/3. ∫ min(α, 1 − 2y) dy = ½∫_0^{1/3} min(α, t) dt = α/6 − α²/4, valid for **α ≤ 1/3**.
    ∫(α + 1 − 3y)₊ dy = α²/6, valid for α ≤ 1/2. The sum is **α/2 − α²/12**.
  - So ∫_{1/3}^1 P dy = 2/9 − (α − α²/3) = **2/9 − α + α²/3, exactly for 0 ≤ α ≤ 1/3.** Confirmed by my exact piecewise
    integral at 11 values in [0, 1/3]. It differs at α = 17/50, 2/5 and 1/2 (§E), so the README's stated range is right.
    Both partial integrals are also confirmed (§E).
- *J_s ≤ (2/3)β.* r̂ ≤ β on an interval of length 2/3, and J_{s+2} ≥ 0. My closed form for J equals my integrator at 600
  random points (§G).
- *The uniform floor.* f(α) = 4/9 − 2α + (2/3)α² has f′ = −2 + (4/3)α < 0, and f(1/6) = 4/9 − 1/3 + 1/54 = **7/54** exactly.
  So f > 7/54 on [0, 1/6). The floor is never attained: under (iii), r̂_s(1) = 0, so J_s < 2β/3.

## Task 3. Independent numerics: **PASS**

All values are exact Fractions. The step is `2β/3 + PkgAB(s+2).I_out() − PkgAB(s).I_out()`. The domain test is mine: an
exact infimum of z over the closure of (1/3, 1], plus (iii).

**Edge points (§H; 62 points, 50 of them in the domain).** In every in-domain point pkg_ab equals my step and both bounds
hold. The points tested were:
- α = 0, including the saturation edge β = 2/3;
- α = 1/6 − 10⁻⁶ and α = 39/240;
- β exactly at the s + 2 saturation edge β*, and β* + 10⁻⁶, for 9 choices of (s, ν, α);
- β = 2, 199/100, 12/5 and 5/2;
- A = r_s − 1/1000 for s = 3, 5, 7, 9 and 11;
- ν = 1, 21, 31, 45 and 61;
- cells where z binds and Δz > 0, e.g. (s, ν, α, β) = (3, 9, 1/10, 2/5);
- the four template rows.

**Out-of-domain points (12).** These were β between the saturation edges at s and at s + 2, A = r_s exactly, and points
below saturation. pkg_ab raises ValueError below saturation (6 points). Where it runs, the bounds still hold for the formula.

**Random points (§J; `rv_exact.out` seed 20261115, `rv_exact_seed7.out` seed 7).** 300 + 300 in-domain points with s ∈ {3,
…, 11}, ν ∈ 0..40 and α ∈ [0, 1/6), with β biased to β* and to the (iii) edge. Results:
- 0 mismatches with pkg_ab and 0 violations.
- **Both bounds are attained with equality** (step − lower = 0 and upper − step = 0 both occur), so neither side can be
  improved uniformly. Examples:
  - lower = step at (s, ν, α, β) = (9, 40, 0, 26867/20000) and (7, 21, 1/40, 7/12);
  - upper = step at (11, 4, 85693/514194, 2/3) and (7, 2, 1/8, 2/3);
  - both at (3, 5, 0, 2/3).
- lower/step: minimum 0.598 (seed 7: 0.542), median 0.975.

**pkg_ab's saturation test is approximate** (`rv_zmin_probe.out`). `PkgAB.zmin` samples each piece at l + (r−l)/10⁶. At
β = β* − 10⁻⁹ it returns about +5·10⁻⁸ although the exact infimum is −10⁻⁹. `I_out` then raises, so no wrong step value is
produced. The scan's `admissible` flag could only be wrong within about 5·10⁻⁸ of the edge. Every one of the 754 scan cells
passes my exact domain test.

**The scan's exact data (`rv_numbers.out` §3).** 0 lower and 0 upper violations on all 754 rows of the four scan files that
lie in the README domain. The lower/true ratio is 0.6123 to 0.9956, median 0.8426, which matches the README's "0.612–0.996,
median 0.842".

## Task 4. The numbers: **PARTIAL**

**Confirmed exactly** (`rv_numbers.out` §1, §2, §5).

| item | claimed | recomputed |
|---|---|---|
| (3/40, 37/40, 6): lower / true / upper | 1991/2400, 751/768, 191/180 | same |
| ν = 8 | 3817/4800, 12817/14400 | same |
| ν = 10 | 43609/57600, 92111/115200 | same |
| ν = 2 | 2129/2400, 9929/9600 | same |
| `W-generic-step` column | 0.516, 0.463, 0.399, 0.589 | consistent with 2β/3 − J_5 (no clamp active); its formula was not reviewed |
| s ≥ 7 lower end at the template | ≥ 691/800 (s = 7..39, ν = 0..10) | min = 691/800 exactly, at (s, ν) = (7, 10). J_s = 0 for every ν ≤ 10 once s ≥ 11, so s ≤ 39 is enough; it also holds for s up to 99. 691/800 > 167/300 |
| `min_lower.py` row | 0.530 (ν ≤ 5), 0.279 (ν ≤ 10), 0.2319 at (13/80, 21/80, 15) | 0.5300, 0.2794, 0.2319 at (13/80, 21/80, 15) |

**The ζ(5)-side numbers.** These are floats from the scan (floor5 = A*(5) + LB with a float tail and a float LB), not
enclosures.

| README claim | recomputed | verdict |
|---|---|---|
| 651 cells | 651 = the **admissible** cells (L_a ≥ 0 and saturation) of **scan_coarse.json and scan_fine.json only**, with α < 1/6 and A < 2. The team scripts also list `cells_*.json`, but those are input cell lists with no results, and they never read `scan_lowbeta.json` or `scan_fine2.json`. With all four files there are 679 admissible cells, and 754 cells in the README domain (75 of them with L_a < 0) | **wording**: the set is not "the scan cells … in the domain" |
| floor5 ≥ −0.0836, deepest at (1/10, 39/40, 4) | −0.08363 at (1/10, 39/40, 4), the same on all three cell sets | OK |
| "ζ(5) closes at 194 cells, ν ∈ {2, 4, 6}" | floor5 < 0 at 194 cells, ν ∈ {2, 4, 6}. The scan's heuristic upper end top5 = A*(5) + U is negative at only 87 | **wording**: a negative floor means ζ(5) is not excluded, not that it closes |
| lower bound ≥ 0.484 at those cells | 0.48422 | OK |
| true step ≥ 0.790 at those cells | **0.78974** | **rounded up**: should be ≥ 0.789 |
| floor₇ ≥ floor₅ + lower ≥ +0.483 "at every cell" | +0.48347 at the 194 cells; **+0.48275** over all cells, at (13/80, 49/80, 6) | **rounded up** for "every cell": should be ≥ +0.482 |
| 7/54 alone leaves +0.046 | +0.04600 | OK |

The extra cells in scan_lowbeta.json and scan_fine2.json change none of these minima.

## Task 5. Overclaim check: **PARTIAL**

**What is right.**
- *Labels.* The README says "Theorem (PROOF-DRAFT; reported as CONJECTURE)". The report uses `\Written` = "CONJECTURE
  (written proof by an AI agent, not checked by a human)" and says "none of this is in Lean for β ≠ 1 − α". Neither presents
  the bound as proved or Lean-checked.
- *ζ(7).* Neither text claims that the step bound alone shows ζ(7) never closes. The README's "Not shown here" says a
  continuous bound on ζ(5)'s margin would be needed, and the report sends the whole-region statement to the interval cover
  of Claim 3.
- *L_a.* The README says plainly that the theorem ignores L_a ≥ 0.
- *Corollary 2's logic.* It is correct with the floor: if floor5 + lower > 0, then floor7 > 0.

**Wording I recommend changing.** None of these changes the theorem.

README:
1. Line 25. Old: "The inner allocation condition L_a ≥ 0 is needed for Θ to be the package's margin, but the bound does not
   use it." New: "The inner allocation condition L_a ≥ 0, and even ν ≤ 10 (E42; odd ν and ν ≤ 22 rest on E732 and E733), are
   needed for Θ to be the package's margin. The bound uses neither, so for other ν it is a statement about pkg_ab's formulas.
   Saturation at s + 2 implies saturation at s, because z is nonincreasing in s."
2. Line 30. Old: "(the step is free of both, by Prop. 1′)". New: "(the step is free of M by Prop. 1′ and the crude term, and
   of U because U does not depend on s, derivation_beta §4)".
3. Line 36. Old: "for every admissible (α, β, ν)". New: "for every (α, β, ν) in the domain". "Admissible" is not defined in
   the README, and in the scan it includes L_a.
4. Line 50. Old: "At β = 37/40 it is 191/180, E62 Proposition 2's written ceiling for s ≥ 7 (…). The theorem extends that
   ceiling to every (α, β, ν) and every s." New: "At β = 37/40 it is 191/180, the value that E62 Proposition 2 gives for the
   step once s ≥ s*(ν) = max(ν + 1, 7 + 6(ν − 2)α) (…). E62 does not state it as an upper bound; the theorem shows that
   2β/3 + 4/9 bounds the step at every s and every (α, β, ν) in the domain." E62's Proposition 2 is an equality for s ≥ s*(ν),
   not a ceiling for s ≥ 7.
5. Line 108. Old: "(2β/3 + I_out7 − I_out5 from `scan_*.json`, `cells_*.json`), 651 cells with α < 1/6 and A < 2". New:
   "(… from `scan_coarse.json` and `scan_fine.json`), the 651 admissible cells (L_a ≥ 0, saturation) with α < 1/6 and A < 2.
   With all four scan files: 679 admissible cells, and 754 in the README domain, with 0 violations (review/rv_numbers.out)."
6. Line 115. Old: "Over the 651 scan cells where both s = 5 and s = 7 are in the domain:". New: "Over the 651 admissible
   cells of the coarse and fine scans with α < 1/6 and A < 2 (FLOAT: floor₅ = A*(5) + LB from the scan). The same minima
   hold on all 754 cells of the four scan files that lie in the domain:".
7. Line 117. Old: "ζ(5) closes at 194 cells, all with ν ∈ {2, 4, 6}." New: "ζ(5)'s floor is negative at 194 cells, all with
   ν ∈ {2, 4, 6}. ζ(5) is not excluded there, and the scan's heuristic upper end is negative at 87 of them."
8. Line 118. Old: "and the true step is ≥ 0.790." New: "and the true step is ≥ 0.789."
9. Line 119. Old: "So floor₇ ≥ floor₅ + lower bound ≥ **+0.483** at every cell." New: "So floor₇ ≥ floor₅ + lower bound ≥
   +0.483 at those 194 cells, and ≥ +0.482 at every cell (minimum +0.4827 at (13/80, 49/80, 6))."
10. Line 123. Old: "This theorem explains it: a step costs at least 7/54, and at least about 0.48 wherever ζ(5) closes, while
    ζ(5) closes by at most about 0.08." New: "The theorem is consistent with it: a step costs at least 7/54 everywhere. On the
    scan grid it costs at least 0.484 wherever ζ(5)'s floor is negative, and that floor is never below −0.084 there (grid
    only, FLOAT)."

Report (`report/report.tex`):
- **R1 (line 309, Statement).** Old: "So $\Theta(7;\alpha,\beta,\nu)=\Theta(5;\alpha,\beta,\nu)+\mathrm{step}_{5\to7}
  (\alpha,\beta,\nu)$ at every choice:". New: "… at every admissible choice with $2\beta+\nu\alpha-1<2$, where the $s=5$
  formulas are derived:". Also change "at least $7/54$ at every choice" to "at every such choice".
  - Why: the report's admissible set (735 grid points with α < 1/6, Appendix) is defined with the s = 7 condition
    2β + να − 1 < 3. **56 of those points have 2 ≤ A < 3**, for example (3/40, 9/8, 10) and (1/10, 1, 10). There (iii)
    fails at s = 5, so the bound does not cover step 5→7. The later sentence "at every proportion where both are defined"
    is correct.
- **R2 (line 323).** Old: "For every odd $s\ge3$ and every admissible $(\alpha,\beta,\nu)$, with $0\le\alpha<1/6$ and the
  saturation condition at both $s$ and $s+2$,". New: "For every odd $s\ge3$ and every admissible $(\alpha,\beta,\nu)$ with
  $0\le\alpha<1/6$, $2\beta+\nu\alpha-1<(s-1)/2$, and the saturation condition at $s+2$ (which implies it at $s$),".
  - Why: (iii) is a hypothesis of the README theorem, and it binds at s = 3 and s = 5.
- **R3 (line 327).** Old: "The upper end is the ceiling of E62". New: "The upper end is the value that E62 (Proposition 2)
  gives for the step once $s\ge s^*(\nu)$; that it bounds the step at every $s$ is new here".
- **R4 (line 327).** Old: "at the $651$ scan cells where $s=5$ and $s=7$ are both admissible". New: "at the $679$ admissible
  scan cells with $2\beta+\nu\alpha-1<2$". The present check reads two of the four scan files, which gives 651; the results
  are the same on all 679.
- **R5 (line 327).** Old: "At the cells where $\zeta(5)$ closes". New: "At the cells where the floor of $\zeta(5)$ is
  negative".

---

## Replay (run from this folder)

| claim | command | expected output |
|---|---|---|
| Prop. 1′ in pkg_ab (R_{s+2} − R_s = 2βx); M-free A_M step | `python3 -B rv_exact.py 300 20261115 > rv_exact.out` | §A: two `[PASS]`, and one line noting that `int_R_x3` cannot run at α = 0 |
| Tout s-free on (1, 2β], also where (iii) fails | same | §B `[PASS]`, 240 points |
| own outer function == `PkgAB.outer_parts` | same | §C `[PASS]`, 1620 evaluations |
| e ≤ δ ≤ 2; 0 ≤ Δz1 ≤ Δc ≤ 2(ℓ−2); min inequality; monotone in s | same | §D: five `[PASS]` |
| ∫P = 2/9 − α + α²/3 for α ≤ 1/3 (fails at 17/50, 2/5, 1/2); partial integrals; d ≥ 0 | same | §E: table, then three `[PASS]` |
| f(1/6) = 7/54; f decreasing | same | §F: three `[PASS]` |
| J closed form; 0 ≤ J ≤ 2β/3 | same | §G: two `[PASS]` |
| 62 edge points: pkg == own, bounds hold (50 in domain) | same | §H: two `[PASS]`; "outside the domain (12 points): pkg_ab raised at 6; bounds hold … at 12 of 12" |
| pointwise bounds on `outer_parts` | same | §I: two `[PASS]`, 10000 points |
| 300 random domain points; bounds attained with equality | same | §J: two `[PASS]`; "tightest lower: … = 0", "tightest upper: … = 0"; `SUMMARY: 0 failed checks []` (about 20 s) |
| the same with a second seed | `python3 -B rv_exact.py 300 7 > rv_exact_seed7.out` | `SUMMARY: 0 failed checks []` |
| Values table, `W-generic-step` column consistency | `python3 -B rv_numbers.py > rv_numbers.out` | §1: four lines ending `MATCH` |
| s ≥ 7 lower end ≥ 691/800 | same | §2: "min = 691/800 … at s=7, nu=10; == 691/800: True; > 167/300: True" |
| scan exact data: 0 violations, ratio 0.612–0.996 | same | §3: "cells with alpha < 1/6 and A < 2: 754", "lower violations 0, upper violations 0", "lower/true: min 0.6123 median 0.8426 max 0.9956" |
| ζ(5) side, team set = 651 cells | same | §4 first block: "651 cells; min floor5 = -0.08363 at (1/10, 39/40, 4)", "floor5 < 0 at 194 cells, nu in [2, 4, 6]; top5 < 0 … at 87", "min true step = 0.78974", "min floor5 + lower = +0.48275 at (13/80, 49/80, 6)" |
| `min_lower.py` numbers | same | §5: "global min 0.2319 at (13/80, 21/80, 15)", "nu <= 5: 0.5300; nu <= 10: 0.2794" (about 5 s) |
| `PkgAB.zmin` is a sampled approximation | `python3 -B rv_zmin_probe.py > rv_zmin_probe.out` | at β* − 10⁻⁹: "exact zmin(s+2) = -1.000e-09  PkgAB.zmin = +4.9…e-08  pkg_ab test passes; I_out raises ValueError" |
| non-integer ν (outside the domain) | `python3 -B rv_real_nu.py 600 1 > rv_real_nu.out` | "426 points with non-integer nu …: lower violated at 0, upper at 0" |

Files: `rv_core.py` (own exact implementation), `rv_exact.py`, `rv_numbers.py`, `rv_zmin_probe.py`, `rv_real_nu.py`, and
their `.out` logs. No file outside `review/` was modified.
