# E734: the ζ(7) floor below the saturation edge

Lane N, driver Claude Opus 5.5 on `[team machine]`, for [team member] ("get back to your research"). EVENT WORK, Sun Nov 15
2026, 07:25 to 09:10 PT.

**Why this region.** E730–E733 certify the floor on the derived and window regions, both of which require the outer saturation
condition z_β ≥ 0. Every weakest certified box sits at that edge. Below it, E42's outer formula is not valid. E63's
Proposition C gives the outer class cost on both sides of saturation (PROOF-DRAFT). The Codex review `A-e63-unsaturated-review`
passes it, and its exact implementation `density_cost` (in `exact_outer.py`) is imported here read-only. E63 itself used it
only for the step s → s + 2, and nobody had computed the ζ(7) floor below the edge.

**Status.** COMPUTED, floating point, at points, given PROOF-DRAFT steps: E63 Prop. C; E730's reductions; and, at odd ν, E732's
window allocation. The interval cover of the boxes below the edge is section 4. Not reviewed.

## 1. The outer cost below saturation (`unsat.py`)

- floor7 = A_inner(7) + I_out^C(7) + LB, where:
  - A_inner = `pkg_ab.A_star_float(iout=0)`, the inner range, which does not depend on saturation;
  - I_out^C = ∫_{1/3}^{1} Q_7(y) dy + ∫_{1/3}^{max(1,2β)} (−2β⌊1/y⌋ + Σ_j(2β − jy)₊) dy, with Q_7 from Prop. C;
  - LB = `lb_opt`.
- **Check (COMPUTED, exact rationals):** at 60 random saturated points I_out^C equals `pkg_ab.PkgAB.I_out` exactly, with
  difference 0.

## 2. The point scan, even ν ≤ 10, derived region below the edge (`scan.py` → `scan.json`, `scan.out`)

The grid is α = k/240 and β = m/80. A point is kept if it satisfies L_a ≥ 0 (La_check) and (iii), and z_min(s = 7) < 0. That
gives 4048 points, every one computed without error.

| ν | points | min floor7 | at (α, β) | z_min there |
|---|---|---|---|---|
| 2 | 1680 | +0.567 | (11/120, 1/10) | −0.567 |
| 4 | 1294 | +0.820 | (1/12, 7/40) | −0.492 |
| 6 | 812 | +0.785 | (13/80, 23/40) | −0.038 |
| 8 | 250 | +0.802 | (29/240, 1/2) | −0.006 |
| 10 | 12 | +0.995 | (7/80, 9/20) | −0.013 |

- **No dip at the edge.** Walking down through z = 0 at ν = 8, α = 1/8, the floor rises slightly: 0.777, then 0.789, then
  0.802 (β = 0.55, 0.50, 0.45). The last two points fail La_check, so they only show that the formula is continuous there.
- **The minimum is at ν = 2,** at the smallest admissible β. That β is about ν/24 + 1/120, attained at α = 1/12: 0.092,
  0.175, 0.258, 0.342 and 0.425 for ν = 2, 4, 6, 8, 10.

## 3. ν = 1 and β → 0: the margin goes to zero linearly (`smallbeta.py`, `tinybeta.py`)

**Window validity at small β** (exact continuum window feasibility, E733's `check_window3.feasible`, sampled on x ∈ [3, 40]):
- At ν = 1 the window allocation stays valid as β → 0, at every α tried (1/240 to 13/80), below saturation.
- At ν = 2 to 6 small β fails, near x ≈ 3.0 to 3.8. At ν = 2 the allocation is valid again from about β ≈ 0.08 at α = 1/12,
  where the floor is +0.47.

**The floor at ν = 1** uses the true odd-ν inner part:
A_inner(true) = A_inner(relaxed) + ∫_3^∞ (R_window − R_relaxed)/x³ dx (midpoint sum on [3, 300], step 1/500; tail ≤ 7·10⁻⁷).

| α | β | relaxed floor | window correction | true floor | true floor / β | upper end A* + U(σ) |
|---|---|---|---|---|---|---|
| 1/12 | 0.01 | 0.06646 | +0.00128 | 0.06774 | 6.77 | 0.06964 |
| 1/12 | 0.0025 | 0.01542 | +0.00167 | 0.01709 | 6.84 | 0.01757 |
| 1/12 | 0.001 | 0.00509 | +0.00176 | 0.00685 | 6.85 | 0.00704 |
| 1/12 | 0.00025 | **−0.00009** | +0.00180 | 0.00171 | 6.85 | 0.00176 |
| 3/20 | 0.001 | 0.00484 | +0.00183 | 0.00667 | 6.67 | 0.00685 |
| 1/40 | 0.001 | 0.00659 | +0.00045 | 0.00704 | 7.04 | 0.00725 |

- **The margin is ≈ 6.85·β** (COMPUTED, floating point). ζ(7) fails at every β > 0. Over the whole parameter space the
  infimum is 0, approached only at ν = 1 as β → 0. Per Hankel row (margin/β) it stays near 6.85, so this is the degenerate
  limit of a shrinking matrix, not a near-miss. The upper end (`pkg_ab.U_float` at lb_opt's σ, an admissible ρ) is within 3%
  of the floor, so this is the margin itself, not slack in the bound.
- **A caution.** The relaxed formulas, which are the even-ν formulas evaluated at odd ν, give a negative floor at β = 1/4000.
  That is an artifact. The true window inner part adds +0.0018, and the relaxed package is not Fauzan's at odd ν (E732).
- **Consequence for the statement.** "No (ν, α, β) closes ζ(7) within the package" holds pointwise. A uniform positive lower
  bound holds on the saturated region (E733: +0.482), not on the whole parameter space. E730's certified function bounds the
  inner remainder ∫Q/x³ by the constant −5/144, so it cannot certify the strip ν = 1, β → 0. That needs a bound which scales
  with β, as the true floor does. That is open.

## 4. Interval cover of the boxes earlier marked `invalid: saturation` (`box_unsat.py`, `cover_unsat.py`)

`box_unsat.floor_box_C` is E730's centred-form bound with Prop. C as the outer integrand: the exact value at the centre, plus
gradient hulls by forward mode through Q_7's min and max. On two saturated boxes it agrees with E730's bound, slightly weaker
(0.614 against 0.623, and 1.242 against 1.300).

The cover takes the 740 saturation-invalid boxes of E730 (even ν), E732 (odd ν) and E733 (ν = 1 to 24). Each is certified,
or invalid by E733's x = 3 window test or (iii), or split (to depth 3 in the final run).

**Result (COMPUTED + PROOF-DRAFT; `cover-unsat.json`, `cover-unsat.log`; 864 s on 10 cores, depth ≤ 3).** The run ended
with 4115 final boxes: 2822 certified, 568 invalid by the window test at x = 3, and 725 unresolved.
(A first 4-worker run was stopped after level 0. Its level-0 results are in `cover-unsat-level0-partial.json` and agree.)

- **Every unresolved box lies at small β:** β ≤ 0.019 at ν = 1, ≤ 0.031 at ν = 2, ≤ 0.07 at ν = 3 to 6, and less for larger ν.
  For ν ≥ 3 they all sit near α = 1/6, where the x = 3 test's right-hand side (1 − 6α)k vanishes. Many boxes touch β = 0, where
  the bound is −∞ (log 2β in the analytic part).
- **Classified by sampled window feasibility** (`classify_unresolved.py` → `classify-unresolved.json`). Five points per box,
  x ∈ [3, 12]; NOT rigorous:
  - **ν = 1: all 133 boxes are inside the window region.** This is the strip of section 3, where the true floor ≈ 6.85·β
    tends to 0. E730's certified function cannot reach it.
  - **ν ≥ 2: in all 592 boxes every sample is infeasible,** so they are outside the window region by sampling. The allocation
    fails where αx crosses 1/2 (x ≈ 1/(2α), 3.08 to 3.16 near α = 1/6), or near x ≈ 3.3 to 3.8 at ν = 2. A rigorous box test
    there, generalising the x = 3 test to x = 1/(2α)⁺, is the next step.
- **The certified boxes' bounds tend to 0 as β → 0** (the smallest certified bounds per ν are +0.0004 to +0.03, all at small
  β). So below saturation the cover proves positivity box by box, not a uniform margin. On the derived region below the edge
  (L_a ≥ 0, even ν ≤ 10), the point scan of section 2 gives at least +0.567.

## 5. A rigorous test that the small-β boxes at ν ≥ 2 lie outside the window region (`winbox.py`, `check_winbox.py`, `run_winbox.py`)

**The necessary condition at any inner point x** (PROOF-DRAFT; it generalises E733's x = 3 test).
- At x, the class types (ℓ_K, ℓ_N) occupy z-intervals of measure μ, with b = (ν/2)ℓ_N and c = b − ℓ_K/2.
- In a valid window allocation, L ≥ 0 gives Y_a ≥ c_a, so M := max c over the present types is at most max Y.
- The window gives Y_c ≥ M − 1, and L_c is an integer, so L_c ≥ max(0, ⌈M − 1 − c_c⌉).
- Hence the mean of Z, which is (2β + να)x, is at least RHS(α, x) = 2 Σ μ_c (L_c^min + b_c).
- So **(2β + να)x < RHS(α, x)** proves the allocation invalid at that prime. The finite-K corrections are O(x/p), so a strict
  inequality suffices.

**The box version.** Split the box's α-range at the points where the class structure at x changes. On each piece RHS is
affine in α, so its infimum is at the piece's ends: the end limits are computed exactly by linear extrapolation, and the
split points are checked directly. Compare with the largest left side, (2β₁ + να)x. Each box tries a list of x values:
- just above k/(2α₀), where classes with a new ℓ_N appear for every α in the box;
- just above q/2;
- a grid on (3, 8].

**Soundness (COMPUTED, `check_winbox.py`).**
- (a) 2815 random points flagged by the inequality: none is window-feasible at that x (E733's exact `feasible`).
- (b) At x = 3⁺ it agrees exactly with E733's test.
- (c) 288 random boxes proved outside: none of 8 random interior points per box is feasible at the proving x.

**Result (COMPUTED, `winbox-results.json`).**
- **All 592 unresolved boxes with ν ≥ 2 are proved outside the window region,** each at a recorded x, with no splitting
  needed.
- None of the 133 ν = 1 boxes can be excluded, which is consistent with their being inside.
- The mechanism: for α > 0 a class with ℓ_N ≥ 1 exists, and the window then forces at least one row on every class with a
  larger ℓ_K (or, past αx = 1/2, about ν − 1 rows everywhere). Small β cannot pay for that.
- **At α = 0 there is no such class.** The ν-free package (N = 0, the line α = 0) is window-valid at small β too. So the open
  strip is {ν = 1, β ≤ 0.019} together with the line α = 0 at small β, for any ν (ν-free). Along the line the floor behaves
  like the ν = 1 strip as α → 0 (≈ 7.0·β at α = 1/40); it was not computed at α = 0 itself, because `lb_opt` needs α > 0.

**What this adds to E730–E733.** The floor is positive on every certified box below the saturation edge as well.
- **Inside the window region, one strip is left open:** ν = 1 with β ≤ 0.019, where the floor is positive but ≈ 6.85·β
  (COMPUTED at points with the true window inner part).
- **Small β at ν ≥ 2 (α > 0) is outside the window region,** proved in section 5. The line α = 0 (ν-free) joins the open
  strip.

So, within the package, the uniform statement "≥ +0.482" holds on the saturated window region, and the margin's infimum over
the whole window region is 0, approached only along ν = 1, β → 0.

## Files

`unsat.py` (Prop. C outer cost, the exact check, floor7), `scan.py` → `scan.json`, `scan.out`; `smallbeta.py`, `tinybeta.py`;
`box_unsat.py`, `cover_unsat.py` → `cover-unsat.json`, `cover-unsat.log`, `cover-unsat.stdout`, `cover-unsat-level0-partial.json`;
`classify_unresolved.py` → `classify-unresolved.json`; `winbox.py`, `check_winbox.py`, `run_winbox.py` →
`winbox-results.json`; this README.
