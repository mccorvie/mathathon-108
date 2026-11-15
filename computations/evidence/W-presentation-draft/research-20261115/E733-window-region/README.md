# E733: the ζ(7) floor on the whole window region (closing E732's scope gap)

Lane N, driver Claude Opus 5.5 on `[team machine]`, asked by [team member] ("Extend the cover"). EVENT WORK, Sun Nov 15
2026, 06:05 to 06:20 PT (after the 06:00 cut-off).

**Status.** COMPUTED (E730's interval box bound), given PROOF-DRAFT steps (E730's reductions, E732's window allocation, the x = 3
test below). Two Lean lemmas give the ν ≥ 25 cut-off: `E730.window3_empty` for odd ν and `E730.window3_empty_even` for even ν.
**Review:** one local fresh-context Claude review, `local-review/REVIEW.md`, which is a same-family check. It found no
counterexample and no wrongly-invalid box. Checks 1–4 and 6 pass; check 5 (the ν ≥ 25 justification at even ν) and check 7
(wording) were partial, and both are fixed below. Lane N re-ran its scripts.

## What was missing

E730 and E732 certified the floor on the *derived region*, whose condition (i) is the sufficient test `La_check` (≥ 0, or ≥ 2
at odd ν). Fauzan's proof of Prop. 4.1 applies more widely: wherever the window allocation of E732 has L_a ≥ 0 at every class
and every inner prime. Call that the **window region**. E732's local review found window-valid points outside the derived
region, at ν = 23 and 24 and inside boxes that the cover's `La(x=3)` shortcut had marked invalid, and nothing certified them.

## The x = 3 test (PROOF-DRAFT; exactly sharp at x → 3+ on a sample, COMPUTED)

At x → 3+, every class has ℓ_K = 6, and ℓ_N ∈ {0, 1} (ℓ_N = 1 on measure 3α when 0 < α < 1/6).
- L_a ≥ 0 means Z ≥ b, so Z ≥ ν/2 on the ℓ_N = 1 classes.
- The window (Y_1 − Y_0 ≤ 1 at equal ℓ_K) gives Z_0 ≥ Z_1 − 1, and Z_0 is an integer, so Z_0 ≥ ⌈ν/2⌉ − 1.
- The mean of Z is 6β + 3να. Hence a necessary condition for the window region is **6β ≥ (1 − 6α)(⌈ν/2⌉ − 1)**.
- At finite K (the local review re-derived this exactly at a finite prime, where the condition is h − L₀ ≥ (m − N)k):
  - the mean is (h − L₀)/m, which is below the limit 2H_L x, so the necessary condition only gets stronger;
  - for x slightly above 3, the classes with ℓ_K = 7 all have ℓ_N = 1 and play no role;
  - primes with x ∈ (3, 3 + ε] exist for large K.

A box whose α > 0 part fails it at its corner (α₁, β₁) lies outside the window region. The line α = 0 is the ν-free package of
E730, which is covered there.

`check_window3.py` compares this inequality with exact window feasibility (a valid row assignment exists) at x = 3 + 10⁻⁶. It
drew 3000 random (ν ≤ 30, α, β) and kept the 2029 that satisfy (iii).
- Of 793 flagged points, none is feasible, so the test is sound.
- Of 1236 unflagged points, all are feasible, so on this sample the test is exactly feasibility at 3+.
- E732's reviewer checked 5 points at a finite prime, p = 200003. The test agrees with all 5.

**For α > 0, the window region is empty for every ν ≥ 25** (LEAN-CHECKED for the inequalities).
- Odd ν: k = ⌈ν/2⌉ − 1 = (ν − 1)/2, and (iii) with 0 < α ≤ 1/6 gives 6β < 12 − 3να ≤ (1 − 6α)k (`E730.window3_empty`).
- Even ν ≥ 26: k = ν/2 − 1 is *below* (ν − 1)/2. The 06:20 version wrongly applied the odd case here (the local review,
  check 5, caught it). Instead apply the lemma at ν − 1 ≥ 25, where (iii) still holds because α > 0
  (`E730.window3_empty_even`).
- At α = 0 the window region is ν-free and non-empty (β ∈ [2/3, 2)). E730's α = 0 column covers it.

## The extension (`extend.py`, `extend.json`, `extend.log`; 137 s on 7 cores)

Re-examined:
- the 1398 boxes that the earlier covers marked `La(x=3)` invalid (even ν = 12 to 22 from E730, odd ν = 1 to 21 from E732);
- full 320-box grids at ν = 23 and 24.

The even ν ≤ 10 covers never used the shortcut, so they need nothing. Each box is now certified (E730's `box2.floor_box`),
or invalid by (iii), saturation or the x = 3 test above, or split. **All 2038 boxes resolved at the first level, and none is
unresolved:**

| ν | newly certified | invalid: window(x=3) / saturation / (iii) | smallest new bound |
|---|---|---|---|
| 1 | 0 | 0 / 17 / 0 | none |
| 3 | 0 | 8 / 20 / 0 | none |
| 5 | 0 | 19 / 20 / 0 | none |
| 7 | 1 | 31 / 20 / 0 | +1.2116 |
| 9 | 13 | 42 / 8 / 0 | +0.7476 |
| 11 | 15 | 56 / 3 / 0 | +0.6847 |
| 12 | 12 | 56 / 0 / 0 | +0.7245 |
| 13 | 18 | 65 / 3 / 0 | +0.7589 |
| 14 | 12 | 65 / 1 / 0 | +0.7958 |
| 15 | 18 | 77 / 3 / 0 | +0.8375 |
| 16 | 13 | 77 / 1 / 0 | +0.8288 |
| 17 | 18 | 89 / 2 / 0 | +0.8335 |
| 18 | 13 | 89 / 0 / 0 | +0.8380 |
| 19 | 17 | 101 / 2 / 0 | +0.9148 |
| 20 | 12 | 101 / 1 / 0 | +0.9268 |
| 21 | 19 | 113 / 1 / 0 | +1.0208 |
| 22 | 13 | 113 / 0 / 0 | +1.0655 |
| 23 (full grid) | 62 | 125 / 3 / 130 | +1.0575 |
| 24 (full grid) | 52 | 125 / 3 / 140 | +1.1319 |

At even ν the window allocation is Fauzan's own (E732: the two match exactly), so E730's bound applies directly. At odd ν it
applies by E732's 1/8 argument.

**Check (`check_gap_points.py`, `check-gap-points.json`).** I took the 36 window-valid points that E732's review listed outside
the derived region (its `gap.json`). All 36 now lie in certified boxes. Each box bound is below the point's floor, which is
scan.cell's floor7, minus 1/144 at odd ν for the window correction. The smallest slack is +0.262.

## Result

**A*(7) + LB ≥ +0.482 > 0 at every point of the window region, for every ν ≥ 1 and 0 ≤ α < 1/6** (COMPUTED, given PROOF-DRAFT
steps). The window region is where Fauzan's Prop. 4.1 applies with the window allocation, together with (ii), (iii) and the
other derivation conditions. The minimum is still the derived-region cover's: ν = 9, +0.4827 (E732); ν = 10, +0.4864 (E730).
Every newly certified box is at least +0.68.

In words: **within Fauzan's bound package, with the allocation taken as far as his proof of Prop. 4.1 allows with his row
basis and weights, no choice of ν, α, β rescues ζ(7).** The row basis (4.5), the weights (4.6) and L₀ = 4M + 10 are his
choices, and a different weight scheme would be a different package. Not touched here: α ≥ 1/6, β below saturation, and (iii) failing. Each needs a different, so far
underived, formula. α = 0 is covered as in E730.

## Files

`extend.py`, `extend.json`, `extend.log`, `extend.stdout`; `check_window3.py`; `check_gap_points.py` →
`check-gap-points.json`; `local-review/` (the review and its scripts); this README. Lean: `E730.window3_empty` and
`E730.window3_empty_even` in `../E730-box-certify/lean/E730Lemmas.lean`.
