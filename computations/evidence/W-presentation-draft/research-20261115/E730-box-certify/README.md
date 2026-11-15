# E730: the ζ(7) floor A*(7) + LB is positive on the whole derived (α, β) region, for every even ν ∈ {2, …, 10}

Lane N, driver Claude Opus 5.5 on `[team machine]`, asked by [team member]: extend the one-cell interval certificate
(`scope_alpha_beta/certify_min.py`) to whole intervals of α and β, so that the floor is shown positive everywhere and not only
on a grid (E716 noted that +0.7573 is a grid minimum). EVENT WORK, Sun Nov 15 2026, 01:15 to 02:50 PT.
*Numbering:* this folder was `E717-box-certify` until 02:29. E717 had already been claimed on the board at 01:30, by the Codex
lane N thread for its height budget. That board claim stands, so this work is E730 (board CLAIM, Sun 02:29).

**Status.** COMPUTED (mpmath interval arithmetic at 113 bits plus exact rationals), given the PROOF-DRAFT reductions listed below.
19 elementary lemmas (14 reductions, 3 for the ν ≥ 24 cut-off added at 04:25, and E733's `window3_empty` and `window3_empty_even`) are checked in Lean 4.35.0 / Mathlib v4.35.0 (`lean/`). The team gate
`scripts/lean_check.py --final` gives **PASS** for all 19, using only propext, Classical.choice and Quot.sound (Sun 02:36, rerun 04:26, 06:20 and 07:05,
`lean/log/LEAN_CHECK.md`). The gate also asks a human to compare each printed statement with the claim, which has not been done
yet, so the lemmas are LEAN-CHECKED, not LEAN-VERIFIED. **Review.** E731's local review (`../E731-box-review/local-review/REVIEW.md`,
a fresh-context Claude Opus 5.5 subagent, so a SAME-family check) found no counterexample: checks 1 to 7 pass, and check 8
(the reading) is partial. Its points are fixed here. Lane N replayed all seven of its scripts, and the outputs are identical apart from timings
(`../E731-box-review/PARENT_REVIEW.md`). Lane W's spot-check (`../../../W-E730-spotcheck/`, also same-family, replayed) found
nothing either. The second-family review (Kimi K3.1 Pro,
`chat-d888090ac8`, same brief; all 100 calls served by kimi-k3.1-pro) **passes with one qualification**: `scan.cell` cannot
evaluate α = 0. It found no counterexample in 632 sampled points (smallest slack +0.082), and lane N replayed all its scripts.
These reviews predate the extension below (ν = 12 to 22, α = 0).

## Result

For each even ν ∈ {2, 4, 6, 8, 10}, the rectangle α ∈ [0, 1/6] × β ∈ [0, 2] contains the whole derived region (condition (iii),
2β + να − 1 < 3, forces β < 2 − να/2 ≤ 2). It is cut into 8 × 40 = 320 boxes of size 1/48 × 1/20. **Every box ends in one of two
ways, at the first level, with no splitting needed:**

- *invalid*: condition (iii) fails on the whole box, or the outer saturation z_β ≥ 0 fails at every point of it (on some y-cell
  the interval enclosure of z_β lies below 0);
- *certified*: a rigorous lower bound of A*(7) + LB that holds at every point of the box. It holds as a bound for the floor at
  the box's points in the region, and as a bound for the formula f below at the box's other points.

| ν | certified | invalid | unresolved | smallest certified lower bound | grid minimum (scan, admissible points) |
|---|---|---|---|---|---|
| 2 | 224 | 96 | 0 | +0.9337 | +1.0184 |
| 4 | 212 | 108 | 0 | +0.7845 | +0.8895 |
| 6 | 201 | 119 | 0 | +0.6580 | +0.7873 |
| 8 | 207 | 113 | 0 | +0.5372 | +0.7573 |
| 10 | 212 | 108 | 0 | +0.4864 | +0.8949 |

**So A*(7) + LB ≥ +0.486 > 0 at every point of the derived region with 0 < α < 1/6, for every even ν ∈ {2, …, 10}** (COMPUTED + PROOF-DRAFT). In words: no (α, β, ν) in the derived region rescues ζ(7) within this package.
By Theorem 3′ of `scope_alpha_beta/derivation_beta.md`, ζ(7) fails for every comparison measure and every such (ν, α, β), not
only at the grid points. This closes the "grid minimum" caveat of E716 for the package's formula. For β ∈ (1.125, 2] it is also the first computation of the package at all (see the next section).

- The cover ignores condition (i) (L_a ≥ 0), so it proves positivity on a superset of the region. The weakest boxes
  (ν = 10 at α ∈ [7/48, 1/6], β ∈ [3/20, 1/5]; ν = 8 at the same α, β ∈ [7/20, 2/5]) lie mostly below saturation: at α = 3/20
  the exact z_min there is −0.17 to −0.07 (`spot-check.json`). Those bounds come from the box bound's slack at the saturation edge,
  not from new minima. +0.7573 (ν = 8 at (11/80, 9/16)) remains the best point value on the grid. The cover's guaranteed bound
  is +0.486.
- At large β the floor grows. The scan stops at β = 1.125, and the cover reaches β = 2. Off-grid exact values at β ∈ [1.2, 1.9]
  are between +1.13 and +2.92.

## Checks (COMPUTED)

1. **Against the team's scan** (`crosscheck.py`, `crosscheck.json`): each of the 735 admissible scan points with α < 1/6 lies in
   a certified box. At all 1219 (point, containing box) pairs the box bound is below the point's exact floor7, with slack between 0.080
   and 0.651 (median 0.176).
2. **Off the scan grid** (`spot_check.py`, `spot-check.json`): exact package values (`scan.cell`) at 23 points. These are: 11 near
   the saturation edge at α = 3/20 (ν = 8, 10), and 12 at large β ∈ [1.2, 1.9] (ν = 2, 4, 6, 10), beyond the scan's range. All
   are consistent: no certified box bound exceeds an exact value.
3. **Pieces of the bound, checked in the prototype phase.** The interval T_out contains `pkg_ab`'s exact T_out at 1200 random
   points (`box.py`). `box2.PkgT.I_out` equals `pkg_ab`'s I_out at two cells (27071/16000 and 18881/46080). The closed-form
   arcsine potential matches quadrature (−2.1048000531, −0.457987145132). W_lo ≤ W_hi (2.09256 ≤ 2.09279). The F-part closed form
   matches `pkg_ab`'s A*(7) at three cells, to 5·10⁻⁶ (the error of the numerical Q integral).

## How the bound works (`box2.py`)

On a box B with centre m = (α_m, β_m), for (α, β) ∈ B in the region:

  floor7 ≥ f(α, β) := Ĩ(α, β) − 5/144 + S(α, β),

where

- Ĩ = ∫_{1/3}^{Y} T̃(y) dy, with Y = max(1, 2β₁) fixed on the box, is `pkg_ab`'s I_out with min(r, z) replaced by
  min(r, max(z, 0)). The two agree where z ≥ 0, that is on the region.
- −5/144 bounds ∫_3^∞ Q x⁻³ dx, using Q ≥ −5/8 and ∫_3^∞ x⁻³ dx = 1/18.
- S = 2βc₁ + 2νβα(γ + ln 3) + 3β² − 2β² ln 2β + t² I(σ_c) − t ∫V_{ν,α} dσ_c, with t = β/β_m and σ_c = `lb_opt(ν, α_m, β_m)`. This is the
  F-part of A*(7) plus LB at the trial measure tσ_c, which has mass β. In that sum the ±2β terms and the log α terms cancel exactly.

The bound is the centred (mean-value) form f(p) ≥ f(m) − (Δα/2)·max|∂_α f| − (Δβ/2)·max|∂_β f|. Here:

- f(m) is rigorous at the centre: I_out exactly in rationals, I(σ_c) by `ivlib.I_rho`, and ∫V dσ_c by `certify_min.lb_cert`'s quadrature.
- The partial derivatives are enclosed over the whole box. For Ĩ this uses forward mode through T̃'s min and max: hulls of the
  active pieces, summed over 600 y-cells per unit. For S it uses the formulas ∂_α S = 2νβ(γ + ln 3) + tν Σᵢ cᵢ Uᵢ(α), where Uᵢ is the
  closed-form log potential of the i-th arcsine component (increasing in α), and ∂_β S = 2c₁ + 2να(γ + ln 3) + 4β − 4β ln 2β + 2tI(σ_c)/β_m − W(α)/β_m.
- Ĩ is piecewise affine in (α, β) for each y, so along the segment from m to p it is Lipschitz. Its derivative there, almost everywhere,
  is that of an active piece, and the hull contains it. Then f(p) − f(m) = ∫₀¹ (d/ds) f(m + s(p − m)) ds gives the bound.

Cost: 2 to 5 s per box; the 1600 boxes took 602 s on 10 cores (`cover.log`).

## What is assumed, and with which label

| Step | Label | Where |
|---|---|---|
| Theorem 3′ (the criterion over (α, β)) and Fauzan's degree side conditions | PROOF-DRAFT (§5 of derivation_beta.md) | scope_alpha_beta |
| R = xF + Q (Prop. 1′) | PROOF-DRAFT, reviewed in E716 | derivation_beta.md |
| Q ≥ −1/4, hence ≥ −5/8, for the formula of Q in Prop. 1′ | LEAN-CHECKED `E730.Q_ge`, `E730.Q_ge_five_eighths` (with `bracket_ge`, `ell_sub_bound`, `cross_ge`) | `lean/E730Lemmas.lean` |
| ∫_3^∞ Q/x³ ≥ −5/144 from that pointwise bound; ∫_3^∞ x⁻³ = 1/18 | LEAN-CHECKED `E730.tail_ge`, `E730.integral_Ioi_three_inv_cube` (true for every q, integrable or not; it binds the real tail because Q/x³ is integrable, Q being a bounded step function, which is not stated in Lean) | same |
| F-part + C* collapse (±2β and log α cancel) | LEAN-CHECKED `E730.fpart_add_cstar` | same |
| T_out = T̃ where z ≥ 0 | LEAN-CHECKED `E730.min_max_zero` | same |
| ∂_β of 3β² − 2β² ln 2β; ∂_a ∫₀^a ln(t + u²) du = ln(t + a²) for t > 0 | LEAN-CHECKED `E730.hasDerivAt_beta_part`, `E730.hasDerivAt_J` (t > 0; the endpoint t = 0 of σ_c has measure zero) | same |
| g(α) = α(1 − γ − ln 3α) has g′ = −γ − ln 3α > 0 on (0, 1/6] (used only by the prototype `box.py`) | LEAN-CHECKED `E730.hasDerivAt_g`, `E730.g_deriv_pos` | same |
| ∫_3^∞ {x}/x² = 1 − γ − ln 3 + 5/6 and ∫_3^∞ {αx}/x² = α(1 − γ − ln 3α) (3α < 1) | PROOF-DRAFT; checked numerically (5·10⁻⁶) | README check 3 |
| LB(σ) is a valid lower bound for every σ of mass β (Lemma 2′) | PROOF-DRAFT | derivation_beta.md §4 |
| Log potential of the arcsine law on [c − h, c + h] at −a²: ln((c + a² + √((c + a²)² − h²))/2) | PROOF-DRAFT (the standard log potential of the arcsine law; re-derived in E731's local review, check 3(d)); COMPUTED by quadrature | check 3 |
| Differentiating ∫V_{ν,α} dσ_c under the integral sign; the segment (mean-value) argument above | PROOF-DRAFT | this README |
| The interval and quadrature code (`ivlib`, `certify_min.lb_cert`, reused read-only) | COMPUTED, shared with the one-cell certificate | certify/, scope_alpha_beta |

The Lean `Q` is a transcription of `pkg_ab.PkgAB.Q`'s formula, written with one integral over z ∈ [0, 1/2] instead of two (equal by
linearity, both integrands being bounded step functions). Lean checks the inequality, not that this formula is the Q of R = xF + Q.

## Extension, Sun 04:20 to 04:50: every even ν ≥ 2, and α = 0

**Why the scope said ν ≤ 10.** E13 (`criterion5/derivation.md`, Theorem 3) restricted itself to ν ≤ 10 after a skeptic's
review. The reason was that the allocation L_a ≥ 0 fails near x = 3 for ν > 10 on Fauzan's slice β = 1 − α (at α = 3/40).
derivation_beta.md inherited "even ν ≤ 10", but it already imposes L_a ≥ 0 as its own condition (i).
- Nothing else in its §1 to §4 depends on ν ≤ 10. Every formula carries ν as a symbol. Prop. 4.1 holds "for every H for which
  all L_a ≥ 0". E13's other ν hypothesis, (ν − 1)α < (s − 1)/6, was replaced there by the rank clamp, which derivation_beta also uses.
- So Theorem 3′ reads for every even ν ≥ 2 under (i) to (iii) (PROOF-DRAFT; the file's owner should confirm).
- With β free, L_a ≥ 0 holds at many points for ν > 10: on the grid α = k/240, β = m/40 it holds at 1141, 878, 644, 279 and
  131 points for ν = 12, 14, 16, 20, 22. It holds at none for ν = 24, 26, 30.

**ν ≥ 24: the derived region is empty.** This is a statement about the derived region, which is defined by the sufficient
test La_check ≥ 0 (condition (i)). It is not a statement about the package. E732's local review found that Fauzan's allocation
itself satisfies every condition at ν = 24, (α, β) = (1/240, 9/5), at p = 200003 (one point, COMPUTED), and its floor there is
not certified by anything here.
- L_a(3) = ⌊6β + 3να − 21/20⌋ + 1 − (ν/2)·lmax(3α), and lmax(3α) ≥ 1 for 0 < α < 1/6 (`E730.ell_half`).
- Under (iii), 6β + 3να < 12, so L_a(3) ≤ 11 − ν/2 < 0 once ν > 22 (`E730.la3_neg_of_le`, stated for every real ν > 22).
- Labels: LEAN-CHECKED for the inequality and for the value of ℓ. That this L_a(3) is condition (i) of the package is
  PROOF-DRAFT (`pkg_ab.La_check` includes x = 3).

**ν = 12, 14, …, 22: the same cover** (`cover.py 12 14 16 18 20 22 --la`, 460 s on 7 cores).
- `--la` also declares a box invalid when L_a(3) < 0 at its upper corner. By monotonicity (`E730.la3_box`) condition (i) then
  fails at every point of the box with α > 0. The test was checked against the exact `La_check` on 579 boxes, with no contradiction.
- Every box was certified or invalid at the first level:

| ν | certified | invalid (L_a / (iii) / saturation) | unresolved | smallest certified bound |
|---|---|---|---|---|
| 12 | 179 | 68 / 68 / 5 | 0 | +0.5326 |
| 14 | 161 | 78 / 77 / 4 | 0 | +0.6152 |
| 16 | 134 | 91 / 91 / 4 | 0 | +0.7118 |
| 18 | 112 | 102 / 102 / 4 | 0 | +0.7929 |
| 20 | 89 | 114 / 114 / 3 | 0 | +0.8777 |
| 22 | 66 | 126 / 125 / 3 | 0 | +0.9843 |

- Check (`spot_check_highnu.py`, `spot-check-highnu.json`): 48 random admissible points, 8 per ν. All lie in certified boxes,
  no bound is above the exact value, and the smallest slack is +0.318. The exact floors at these points grow with ν, from 1.16
  (ν = 12) to 3.18 (ν = 22). The team's scan never reached ν ≥ 12, so this is the only check there.

**α = 0.** With N = 0 there is no D_N, so the package does not depend on ν (every ν-term of the formulas carries a factor α).
The conditions reduce to L_a ≥ 0 ⇔ β ≥ 1/120 (lmax(0) = 0), saturation ⇔ β ≥ 2/3, and (iii) ⇔ β < 2. The certified function f
at α = 0 is a lower bound for that ν-free floor, whatever σ_c is. In every ν ≤ 10 cover, all 27 boxes of the column
α ∈ [0, 1/48] that meet β > 2/3 are certified. **So the floor at α = 0 is ≥ +1.045 on its whole range β ∈ [2/3, 2)**
(ν = 2 column). Labels: COMPUTED; that the formulas at α = 0 are the N = 0 package is PROOF-DRAFT. `lb_opt` refuses α = 0
(log α in its C*), so there is no exact point value to compare there.

**Together: A*(7) + LB ≥ +0.486 > 0 on the derived region for every even ν ≥ 2 and every 0 ≤ α < 1/6** (COMPUTED,
LEAN-CHECKED cut-off at ν ≥ 24, PROOF-DRAFT reductions). The minimum bound over all ν is still ν = 10's.

## What this does not show

- Odd ν is handled in E732 (`../E732-odd-nu/README.md`). There the inner allocation is re-derived (PROOF-DRAFT, no review), and this
  cover then gives ≥ +0.482 for ν = 1, 3, …, 21, with an empty region for ν ≥ 23. ν = 0 is not considered (E13 assumes ν ≥ 2).
- Larger ν is covered only as stated in the extension above: ν = 12 to 22 by the cover, and ν ≥ 24 because the derived region is
  empty. Parameters where the package is valid but La_check fails were found by E732's local review (check 5); E733
  (`../E733-window-region/README.md`; COMPUTED given PROOF-DRAFT steps, one same-family review) has since covered the whole
  window region for every ν ≥ 1 (≥ +0.482), and shown that for α > 0 it is empty for ν ≥ 25.
- Nothing about α ≥ 1/6, where the derivation's closed forms change.
- Nothing at α = 0 itself, where there are no cancelled poles and the regime is different. The boxes reach α = 0, so every 0 < α < 1/6 is covered, and there the log α terms cancel exactly (`E730.fpart_add_cstar`), so the bound has no 1/α or log α blow-up.
- Nothing beyond this package: other normalizations (G1) and other constructions are untouched.
- **β ∈ (1.125, 2] is new ground for the package itself, not only for the cover.** derivation_beta.md's own checks (C1 to C4, the
  E29 comparison) all stayed at β ≤ 1.125, and nothing checks Lemma 3′ or Theorem 3′ numerically at β > 1. E731's local review
  checked R = xF + Q exactly at β up to 2 (its check 3(b)). One wording slip there: derivation_beta §3, line 106, gives the
  y > 1 normaliser as (2β − y)₊ alone. The general formula, which is its own table row (line 51), its T_out formula (line 103)
  and the code, is Σ_{j≥1}(2β − jy)₊. That sum comes from v_p(∏_{i<H}(2i)!²) = Σ_j (2H − jp)₊ for primes p > K (PROOF-DRAFT),
  and the two agree when β ≤ 1.
- No second-family check. The interval library and the σ quadrature are the team's own, shared with `certify_min.py`, so an error
  there would affect both certificates alike.

## Files

- `box2.py`: the centred-form box bound (`floor_box`). It imports `scope_alpha_beta/pkg_ab.py`, `certify/{ivlib,run}.py` and `box.py`, all read-only.
- `box.py`: the prototype plain-interval bound, kept for its closed forms and its helpers.
- `cover.py`: the branch-and-bound driver. Writes `cover-nu{2,4,6,8,10}.json` and `cover.log`; the run's stdout is in `cover.stdout`.
- `crosscheck.py` → `crosscheck.json`; `spot_check.py` → `spot-check.json`.
- `lean/`: a v4.35.0 probe (`E730Lemmas.lean`, `lakefile.toml`, `lean-toolchain`), the gate's output in `gate.stdout` and
  `log/LEAN_CHECK.md`, and `lean-check.log` from the first compile, which had 5 errors, all fixed since.

Reproduce, from this folder: `python3 cover.py --workers 10` (about 10 min), then `python3 crosscheck.py` and `python3 spot_check.py`.
For Lean: `python3 scripts/lean_check.py --root <this folder>/lean --final --decl E730.Q_ge …` from the repository root.
