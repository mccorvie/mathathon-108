# evidence/scope_alpha_beta: the criterion over (α, β = H/K), free Hankel size (#108)

**EVENT WORK**, Sat Nov 14 2026, 04:17-05:08 PT. Advocate: scope-alpha-beta (Claude Opus 5.5). No human has checked this.
Inputs imported read-only, never edited: `../margin/theta.py` (sha256 `2f1f90ad…`; only `pieces`, `affine_fit`, `_TEST`, `np_Uarc`,
and, in `check_e13.py`, theta's reading 'S' as the E13 reference), `../certify/ivlib.py` (`274e9def…`) and `../certify/run.py`
(`cc3be8d8…`; helpers `J_iv`, `Vinc_iv`, `padd/pint/pev/pdef/prange`), `../construction/out/beta_table.txt` (`948f39eb…`, E29).
Python 3.14, mpmath 1.3.0, numpy 2.4.6, scipy 1.18.0. No random numbers (SLSQP from fixed starts, fixed grids); the JSON floats can differ in their last bits between platforms.
At most 4 worker processes at any time.

## 1. Result (labels per AGENTS.md §2)

**(a) The package for free β (PROOF-DRAFT, `derivation_beta.md`).** Fauzan's bound package with an independent Hankel size
H = βK: inner range by Fauzan (4.4)-(4.8) with h → H (H_L = β + (ν/2)α in T); outer range by Fauzan's basis (4.11) for
Poly_(<r) plus Cauchy–Binet (H < r) or Xu's block basis (H > r), then Lemma 4.2 with zero count z_r + (H − r) and rank bound
2H + νN − K − r_s(p−1); normaliser and comparison measure with λ → β (Xu §3, CITED). Valid for α < 1/6, L_a ≥ 0 (La_check),
z_β ≥ 0 (outer saturation), 2β + να − 1 < r_s, even ν ≤ 10.

**(b) Exact identities (COMPUTED, `check_e13.py`, ALL PASS).** At β = 1 − α the package equals theta.py reading 'S' (= E13)
exactly: R(x) at 240 points, T_out(y) at 240 points, I_out and ∫_3^20 R/x³ for α = k/40 (k = 1..6) × s ∈ {5, 7} × ν ∈ {2, …, 10}
(60 rows); anchors Fauzan I_out = 127751/96000, Lai (103), audit 453803/288000, s-step 751/768; Prop. 1′ R = xF_β + Q at 1800
points with β ≠ λ; R_(s+2) − R_s = 2βx; U-free s-step 2β/3 + ΔI_out (18277/19200 at β = 17/20, 57667/57600 at β = 1).

**(c) The ζ(7) dual floor over (α, β) (COMPUTED; float scan, decisive cells certified).** Over the computed grid
(α = k/40, k = 1..8, β = m/40 ∈ [0.35, 1.125]; α = k/80, k = 8..13, β = m/80 ∈ [0.5, 0.75]; α = k/160, k = 21..23,
β = m/160 ∈ [0.5375, 0.58125]; ν ∈ {2, 4, 6, 8, 10}; 1486 cells, 931 admissible), for every admissible cell with α < 1/6:

  **min over even ν ≤ 10 of A*(7, ν; α, β) + LB(ν; α, β) ≥ +0.7573 > 0, so ζ(7) fails for every comparison measure.**

The minimum **over the computed grid** is **+0.757282 at (α, β, ν) = (11/80, 9/16, 8), certified by interval arithmetic at that cell** (A*(7) ∈ [0.1533886310,
0.1533886313], LB ≥ +0.603893831; `certify_min.py`). It sits **on the edge of the derivation's validity**: at α = 11/80 the
inner allocation test La_check fails (L_a < 0 possible near x = 3) for β ≤ 89/160, and the floor keeps decreasing toward that
edge (to +0.7537 at β = 43/80, inadmissible). Eleven cells are certified (`out/certified_cert_g*.json`), all > 0, including
the template cell (3/40, 37/40, 6): ≥ +0.904376 (E33 had +0.904155 with Fauzan's ρ as σ; our σ is better).

**(d) Below +0.8? Yes, in absolute terms; no, relative to the s-step.** 104 admissible valid cells have floor < +0.84 (all with
α ≥ 1/10, β ≤ 0.80) and 45 have floor < +0.80 (all with α ≥ 9/80, 0.5125 ≤ β ≤ 0.675). But at the minimum the s-step 2β/3 + ΔI_out is only 0.639 (0.978 at the template)
and the same template **fails at ζ(5)** (A*(5) + LB = +0.118 at ν = 8). Measured in s-steps, min floor7/step = 0.918 at
(1/10, 39/40, 4) against 0.925 at Fauzan's point; per unit β, min 0.914 at (3/40, 9/8, 4) against 0.978. So shrinking the Hankel
matrix lowers ζ(7)'s floor in proportion to the step (E30's "step ∝ H"), never toward 0 relative to it. Among cells where ζ(5)
is not excluded (A*(5) + LB < 0 at some ν), min floor7 = +0.7757 (11/80, 5/8); among cells where ζ(5) closes with our float
upper end (A*(5) + U < 0, U HEURISTIC), min floor7 = +0.8188 (9/80, 29/40). Romik's re-optimised +0.84 (E32, p. 20) lies inside
the range the free-β package reaches; that it is his (α, c) with c = β stays HEURISTIC (E31).

**(e) ζ(5) calibration (COMPUTED lower ends; upper ends HEURISTIC).** Best lower end A*(5) + LB = −0.0836 at (1/10, 39/40, 4);
best float upper end A*(5) + U = −0.0578 at (1/8, 9/10, 4), against Fauzan's point [−0.0735, −0.0581 (E33, certified)]. Freeing
(α, β) gives ζ(5) at most about 0.01 more room.

**(f) Check against E29's exact finite-K values (COMPUTED, `compare_e29.py`).** At α = 3/40, ν = 6, the package floor lies above
the exact e_H(7) at all 22 tabulated (K, H) (as Gauss's lemma requires in the limit): by +0.126..+0.156 (K = 40), +0.057..+0.076
(K = 80), +0.050..+0.062 (K = 120), shrinking with K. The β-minimum is at β ≈ 0.875 in the package and β ≈ 0.85 exactly (K = 80,
120); the d/dβ slopes of the ζ(7) values agree in sign on each side and in size to about 0.1-0.2 per unit β (K = 80: −0.42 vs
−0.44 at β 0.75-0.79, +0.26 vs +0.33 at 0.925-0.95). **The s-step's β-slope does not match:** package 0.19-0.40 per unit β,
exact 0.34-0.94 (K ≤ 120, not converged). The package's free-β gain at (3/40, ν = 6) is 0.006 (0.8983 at β = 0.875), about half
the exact 0.013-0.015 (E29).

**(g) Where the derivation stops being valid (PROOF-DRAFT boundaries, located by computation).** (i) α ≥ 1/6: two removed poles
share an outer class for K/3 < p ≤ 2N (Fauzan (4.9) needs 2N < p), so the class densities are wrong; α ∈ {7/40, 8/40} are the
formula's continuation only (min +0.7921, hatched in the figure). (ii) β below the La edge (inner allocation (4.4)): this is where
the ζ(7) floor is smallest on the grid; that the infimum over the continuous valid region is attained on this edge is NOT shown here (review E716, check 6; lane N's E730 and E733 cover the continuous region by interval arithmetic). (iii) β below the outer saturation
bound z_β = 0 (H fewer than the negative-weight rows): a different outer formula, not implemented. (iv) ν > 10 and odd ν: not
covered (as E15).

Not shown: anything off the computed grid (between grid points the statement is CONJECTURE: the floor moves by ≤ 0.002 per
1/160 step near the minimum); finite M (A_M ≥ A* is not re-certified for β ≠ λ); sharpness of the package (E25, E35).

## 2. Claims → commands → expected output (run from this folder)

| claim | command | expected output (key lines) | time |
|---|---|---|---|
| (b) exact identities | `python3 check_e13.py` | 60 `-> PASS` rows; `C2 … True … True … True … 751/768: True`; `C3 1800 points … PASS`; `ALL PASS: True` → `out/check_e13.log` | 1 min |
| (c) coarse scan | `python3 scan.py coarse workers=4` | `800 cells, 800 to do, 4 workers` … `wrote …/out/scan_coarse.json` | 4 min |
| (c) low-β, fine, finer | `python3 scan.py file:out/cells_lowbeta.json workers=4` (then `cells_fine.json`, `cells_fine2.json`) | writes `out/scan_out_cells_*.json`; we renamed them `scan_lowbeta.json`, `scan_fine.json`, `scan_fine2.json` | 2 + 1 + 0.5 min |
| (c)-(e) analysis, figure | `python3 analyze.py scan_coarse.json scan_lowbeta.json scan_fine.json scan_fine2.json` | `min = +0.757284 at alpha = 11/80, beta = 9/16, nu = 8`; `valid cells with floor < +0.84: 104; with floor < +0.80: 45`; ζ(5) lines as in (e) → `out/analysis.log`, `out/floor_alpha_beta.svg`, `out/decisive_cells.json` | 5 s |
| (c) certification | `python3 certify_min.py out/cert_g0.json N=1000` (and `cert_g1`, `cert_g2`) | `alpha=11/80 beta=9/16 nu=8: … => zeta(7) floor >= +0.757282  CERTIFIED > 0: True`; 11 lines, all True → `out/certified_cert_g*.json/.log` | 1.5 min each |
| (f) E29 comparison | `python3 compare_e29.py` | 22 rows, column `floor-exact` all positive; slope table → `out/compare_e29.log` | 30 s |

## 3. Methods in one paragraph each

**Arithmetic side.** `pkg_ab.PkgAB(s, ν, α, β)` mirrors theta.py's formulas with α, β explicit. A* = I_out + ∫_3^X0 R/x³ (exact
rationals, theta's verified affine pieces) + periodic tail: R(x + P) = R(x) + P·F(x) with P the least integer making αP, 2βP,
2H_L P integral (40, 80 or 160 here), checked exactly at k = 2, 3 (R(x + Pk) is quadratic in k). Scan: tail in float64 (4000
periods + F̄/X). Certification: 45 exact periods + the rigorous remainder of certify/run.py's `astar`, with 40 → P.

**Analytic side.** LB(σ) = I(σ) − ∫V dσ + C*(ν, α, β) for σ a nonnegative combination of 40 nested arcsine measures (19 nested
families: left ends 0 or decreasing), weights by a concave QP (SLSQP), rounded to rationals with exact mass β. Any σ of mass
β gives a valid bound (Lemma 2′); the families agree to about 0.002, and at (3/40, 37/40, 6) our LB −1.386943 is 0.0014 below
Romik's U_true = −1.3855 (E32), so the floors are within a few 10⁻³ of the package's optimum there. Certification: Jensen cells
(concave part) and chord cells (convex part), N = 1000 per component, 113-bit mpmath.iv (certify's method). U (upper end): the
same σ as a comparison measure with a float-grid M₀ (HEURISTIC; loose, since σ is optimised for LB, not for U).

## 4. Credit

Free Hankel size, degree theorem, positivity, the block basis for H > r, the field and C*(q, α, β): Xu,
Anchen0823/zeta9-research-notes@eb264a73 analytic-foundations.md §2-§3 (CITED). Inner allocation, outer basis, Lemma 4.2, (5.1)-(5.6):
Fauzan, Zenodo 22826419 v1 pp. 9-16 (CITED). The (s, ν) attribution and theta.py: E13, E9 (event work of other #108 agents).
The exact finite-K data: E29 (advocate:construction-changes). Romik's +0.84: E32 (Claude Opus 5 for D. Romik,
danromik/zeta5-irrationality@fc2fefa7 docs/zeta5-audit.tex p. 20). Ours: the arithmetic side for H ≠ K − N (inner h → H, Cauchy–Binet
outer bound for H < r, the common zero-count formula, the rank bound in H), the (α, β) scan and its certification.

## 5. Lean targets (for a formalizer; none attempted)

- `R_shift_beta`: for rationals α, β and integers s, ν, R_(s+2,ν,α,β)(x) − R_(s,ν,α,β)(x) = 2βx (finite piecewise identity, as
  E27's InnerShift with λ → β).
- `sstep_beta`: Θ_40(7) − Θ_40(5) = 18277/19200 at (α, β, ν) = (3/40, 17/20, 6) (exact rational, as E27's SStep).


## Corrections of Sun 06:53 PT (integrator, Claude Fable 5.2), after the Kimi review E716

The second-family review of `derivation_beta.md` (Kimi K3.1 Pro, `../W-presentation-draft/research-20261115/E716-beta-review/PARENT_REVIEW.md`) passed checks 1, 3, 4, 5 and 7 (Lemma 3′, Proposition 1′ and the step 2β/3, Proposition 4.1 with h → H, C*(ν, α, β) and Lemma 2′, the code against the formulas), failed check 2 and gave partial verdicts on checks 6 and 8. Applied here: (1) `derivation_beta.md` §0 no longer says that deg_X Δ_H = H for H < r; it uses deg ≤ H, which is all it needs; (2) +0.757 is called a minimum over the grid, and the sentence that the infimum is attained on the La edge is withdrawn; (3) the E29 comparison has 22 rows, not 21 (the log `out/compare_e29.log` is unchanged); (4) 'Deterministic' is replaced by what holds; (5) `PkgAB.zmin` is a sampled screen of the saturation condition, not an exact minimum: where the report needs the condition on a whole box it comes from lane N's interval enclosures (E730). No number of the scan changes.
