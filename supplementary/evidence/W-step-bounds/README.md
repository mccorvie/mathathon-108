# A two-sided bound on the s-step for every (α, β, ν) (lane W)

Claude Opus 5.5 (Claude Code, [team machine]), for [team member], Sun 15 Nov 06:52–07:15 PT; filed at [team member]'s request.
EVENT WORK, done in Phase 3 at [team member]'s explicit request. No human check, and no review by another model family. A same-family
(Claude) review passed the theorem; see "Review" below and `review/REVIEW.md`. This folder has no
evidence id (lane W's E700–E711 are used, and E712 onward belong to lane N), so cite it by folder name. Ledger: C108-W-STEP-BOUNDS.
It sharpens `../W-generic-step/` (C108-W-GENERIC-STEP) and adds an upper bound. It reads `../scope_alpha_beta/pkg_ab.py`
(E42) read-only and does not edit it.

**Question ([team member]).** What can be said about the size of Θ(s+2) − Θ(s) for *any* choice of α, β and ν? Is a lower
bound strong enough to show that ζ(7) can never close?

## Setting

This is the free-(α, β) package of `../scope_alpha_beta/derivation_beta.md` (E42; Prop. 1′ and Lemma 3′ passed the
second-family review E716), as implemented in `pkg_ab.py`. Notation:

- r_s = (s − 1)/2 and A = 2β − 1 + να, the rank intercept.
- r̂_s(y) = min(β, (A − r_s y)₊), the rank allowance.
- J_s = ∫_{1/3}^{1} r̂_s(y) dy.

**Domain.** 0 ≤ α < 1/6, β > 0, any integer ν ≥ 0, with:
- (iii) A < r_s;
- the outer saturation z ≥ 0 at both s and s + 2, so that the outer formula of derivation_beta §3 applies at both.

**What the domain does not include.**
- The inner allocation condition L_a ≥ 0, and even ν ≤ 10, are needed for Θ to be the package's margin (E42; odd ν and ν ≤ 22 rest on E732 and E733).
- The bound uses neither, so for other ν it is a statement about pkg_ab's formulas.
- Saturation at s + 2 implies saturation at s, because z is nonincreasing in s.

## Statement

**Theorem (PROOF-DRAFT; reported as CONJECTURE).** For every odd s ≥ 3 and every (α, β, ν) in the domain, and for every
M ≥ 3 and every U (the step is free of M by Prop. 1′ and the crude term, and of U because U does not depend on s,
derivation_beta §4):

    2β/3 + 4/9 − 2α + (2/3)α² − (J_s − J_{s+2})   ≤   Θ(s+2) − Θ(s)   ≤   2β/3 + 4/9.

**Corollary 1 (uniform).** J_s − J_{s+2} ≤ J_s ≤ (2/3)β, hence

    Θ(s+2) − Θ(s)  ≥  4/9 − 2α + (2/3)α²  >  7/54 ≈ 0.1296   for every (α, β, ν) in the domain and every odd s ≥ 3.

**Corollary 2 (ζ(7) and ζ(5)).** Wherever s = 5 and s = 7 are both in the domain, Θ(7) = Θ(5) + step₅→₇. So ζ(7) can close at
(α, β, ν) only if ζ(5)'s margin there is below minus the lower bound, which is at most −7/54.

### Values

| point (α, β, ν) | lower bound | true step | upper bound | `W-generic-step` bound |
|---|---|---|---|---|
| template (3/40, 37/40, 6) | 1991/2400 = 0.830 | 751/768 = 0.978 | 191/180 = 1.061 | 0.516 |
| (3/40, 37/40, 8) | 3817/4800 = 0.795 | 12817/14400 = 0.890 | 1.061 | 0.463 |
| (3/40, 37/40, 10) | 43609/57600 = 0.757 | 92111/115200 = 0.800 | 1.061 | 0.399 |
| (3/40, 37/40, 2) | 2129/2400 = 0.887 | 9929/9600 = 1.034 | 1.061 | 0.589 |

- **The upper bound matches E62 at the template.** At β = 37/40 it is 191/180, the value that E62 Proposition 2 gives for the step once s ≥ s*(ν) = max(ν + 1, 7 + 6(ν − 2)α) (`../sstep_all_s/proof.md`). E62 does not state it as an upper bound. The theorem shows that 2β/3 + 4/9 bounds the step at every s and every (α, β, ν) in the domain.
- **Neither bound can be improved uniformly.** Both are attained with equality at some in-domain points (`review/REVIEW.md`, Task 3).
- **The lower bound clears the Lean bound at the template.** For s ≥ 7 it is at least 691/800 = 0.864 (exact, s = 7..39, ν = 0..10), above the 167/300 of `sstep_ge`.
- **It is sharper than `W-generic-step`.** It keeps the outer per-pole price that `W-generic-step` drops.

## Proof

Fix y ∈ (1/3, 1], with k = ⌊1/y⌋, v = 1 − ky, u = (α + v − y)₊ and m = min(α, v).

**The outer function.** The class densities are d(2k) = α − m, d(2k+1) = m − u and d(2k+2) = u. Each is ≥ 0, because v < y and α < y, and their sum is α. By
derivation_beta §3 (`PkgAB.outer_parts`, `PkgAB.Tout`):

    T_out^s(y) = (s+2) P(y) + Σ_ℓ d(ℓ) c_s(ℓ) + min(r̂_s(y), z_s(y)) + (s-free normaliser terms),

where:
- P(y) = (1 − y) − Σ_ℓ d(ℓ)(ℓ − 2);
- c_s(ℓ) = Σ_{i=0}^{ℓ−3} (m_i)₊, with m_i = ℓ + s − 1 − ν − 2i;
- z_s(y) = y − 2α + Σ_ℓ d(ℓ)[1 + #{i : m_i ≤ 0}] + β − λ.

**The two ranges.** The inner range and the crude term contribute exactly 2β/3 to the step (Prop. 1′). On 1 < y ≤ 2β, T_out is s-free under (iii). So

    Θ(s+2) − Θ(s) = 2β/3 + ∫_{1/3}^{1} [T_out^{s+2} − T_out^{s}] dy.

**Per index i.** When s → s + 2, each m_i rises by 2. Put δ(m) = (m+2)₊ − (m)₊ and e(m) = 1[m ∈ {−1, 0}]. Then δ(m) = 2, 2, 1, 0
for m ≥ 1, m = 0, m = −1, m ≤ −2, so

    e(m) ≤ δ(m) ≤ 2.

**Summing over i.** Δc(ℓ) := c_{s+2}(ℓ) − c_s(ℓ) lies in [0, 2(ℓ − 2)]. Also z_s − z_{s+2} = Σ d(ℓ) Σ_i e(m_i) =: Δz, and Δz lies in [0, Σ d(ℓ)Δc(ℓ)].

**The rank term.** Both r̂ and z are nonincreasing in s. For a ≥ a′ and b ≥ b′,

    0 ≤ min(a, b) − min(a′, b′) ≤ (a − a′) + (b − b′).

**Pointwise bounds.** Hence:

    T^{s+2} − T^s = 2P + Σ d Δc + [min(r̂_{s+2}, z_{s+2}) − min(r̂_s, z_s)]
                 ≤ 2P + 2Σ d(ℓ)(ℓ − 2) + 0 = 2(1 − y),
    T^{s+2} − T^s ≥ 2P + Δz − (r̂_s − r̂_{s+2}) − Δz = 2P − (r̂_s − r̂_{s+2}).

**Integration.** Over (1/3, 1]:
- ∫ 2(1 − y) dy = 4/9;
- ∫ (r̂_s − r̂_{s+2}) dy = J_s − J_{s+2};
- ∫ P dy = 2/9 − α + α²/3, valid for 0 ≤ α ≤ 1/3.

The last integral is elementary. On (1/2, 1], Σ d(ℓ)(ℓ − 2) = m + u, which integrates to α/2 − α²/4. On (1/3, 1/2] it is 2α + m + u, which integrates to α/2 − α²/12. ∎

**Where the step comes from.**
- 2β/3 is the price of the inner and small primes.
- 2P is the outer per-pole price (the factor s + 2 grows by 2), at least 4/9 − 2α + (2/3)α² in total.
- Removed-pole classes and zero rows can only add to the step.
- The only possible loss is rank allowance, at most J_s − J_{s+2} ≤ (2/3)β.
- No analytic quantity enters: U is the same at s and s + 2.

## Checks (COMPUTED; all exact rationals unless stated)

| claim | command (from this folder) | expected output | time |
|---|---|---|---|
| the three pointwise inequalities on `PkgAB.outer_parts`, at 40 000 random (s ∈ 3..13, ν ∈ 0..30, α ∈ [0, 1/6), β ∈ (0, 2.5], y); closed form of ∫P against midpoint quadrature (float) | `python3 -B check_pointwise.py` | `out/check_pointwise.log`: failures [0, 0, 0]; five matching values | 1 min |
| both bounds at the team scan's exact steps (2β/3 + I_out7 − I_out5 from the four files `scan_coarse.json`, `scan_fine.json`, `scan_lowbeta.json` and `scan_fine2.json`): the 679 admissible cells (L_a ≥ 0, saturation) with α < 1/6 and A < 2 | `python3 -B check_scan.py` | `out/check_scan.log`: 0 lower and 0 upper violations; lower/true 0.612–0.996, median 0.843; `W-generic-step`'s 0.248–0.588. The review also checks the 754 cells of the domain, which ignores L_a: 0 violations (`review/rv_numbers.out`) | 2 s |
| both bounds at fresh `pkg_ab.I_out` values off the grid: 3 × 250 random points, steps 3→5 to 11→13, ν = 1..22 odd and even, β ∈ [0.1, 2] | `python3 -B check_random.py <seed> 250` for seeds 1, 2, 3 | `out/check_random_seed{1,2,3}.log`: 0 violations each | 10 s each |
| minimum of the explicit lower bound for 5→7 over the outer-valid superset (α = k/240 < 1/6, β = m/80 ≤ 2, ν = 0..24; saturation at 5 and 7, A < 2; L_a not imposed) | `python3 -B min_lower.py` | `out/min_lower.log`: ≥ 0.530 for ν ≤ 5, ≥ 0.279 for ν ≤ 10, global 0.2319 at (13/80, 21/80, 15) | 40 s (8 processes) |
| ζ(5) against the step on the scan grid | `python3 -B zeta5_side.py` | `out/zeta5_side.log`: see below | 2 s |

## The ζ(5) side, and what this does and does not prove about ζ(7)

**Grid result (COMPUTED, floating point; `out/zeta5_side.log`).** These figures cover the 679 admissible cells of the four scan files with α < 1/6 and A < 2. Here floor₅ = A*(5) + LB is the scan's float value, a lower bound for ζ(5)'s margin. The review finds the same minima on all 754 cells of the domain.
- floor₅ is never below **−0.0836**; the deepest point is (1/10, 39/40, 4).
- floor₅ is negative at 194 cells, all with ν ∈ {2, 4, 6}. There ζ(5) is not excluded; the scan's heuristic upper end is negative at 87 of them.
- At those 194 cells the lower bound on the step is ≥ **0.484**, and the true step is ≥ 0.789.
- So floor₇ ≥ floor₅ + lower bound ≥ +0.483 at those 194 cells. Over every cell the minimum is **+0.4827**, at (13/80, 49/80, 6), so ≥ +0.482 everywhere.
- Even the uniform 7/54 alone leaves +0.046.

**Not shown here.**
- A *continuous* bound m₅ ≥ −D on the derived region with D < 7/54 would complete a step-based proof that ζ(7) fails everywhere. A smaller D could be used with the sharper local bound. That would be E730's box method run at s = 5, which has not been done.
- The continuous statement for ζ(7) is E730 (`../W-presentation-draft/research-20261115/E730-box-certify/`, COMPUTED + PROOF-DRAFT). It certifies the floor at ≥ +0.486 directly. The theorem is consistent with that: a step costs at least 7/54 everywhere. On the scan grid it costs at least 0.484 wherever ζ(5)'s floor is negative, and that floor is never below −0.084 there (grid only, floating point).
- Nothing is in Lean for β ≠ 1 − α; the Lean identity is `thetaPkg_sstep` (D5).
- Nothing for α ≥ 1/6, below saturation, for other normalisers or for other constructions.
- Θ_pkg bounds the cost from above, so none of this shows that the actual determinants fail at ζ(7). That needs lower bounds on actual valuations, the H0 question.

## The actual step at finite K (COMPUTED; [team member]'s request, Sun 08:00 PT)

**Why this section exists.** The theorem above bounds the step of the bound package. Θ_pkg is an upper bound on the cost at
each s, so a bound on the difference of two upper bounds says nothing about the true difference.

**What is computed instead.** The true cost of this determinant at a given n is

    e_n(s) = log Q^prim_K(ζ(s)) / K²,   Q^prim_K = Δ_K / content(Δ_K).

By Gauss's lemma, every integer polynomial proportional to Δ_K is an integer multiple of Q^prim_K, so no integer normalisation does better.

`actual_step.py` reads the team's exact determinants at Fauzan's proportions (K = 40n, N = 3n, h = 37n) from `../witness/out`, `../obstacles/out` and `../boundary5/out` (E16, E19, E20, E25, E35). It checks that duplicate values agree and recomputes the package step exactly with pkg_ab. It does no new determinant computation.

| ν | K | e_n(5) | e_n(7) | actual step | package step |
|---|---|---|---|---|---|
| 2 | 40 | −0.0648 | +0.8828 | 0.9476 | 9929/9600 = 1.0343 |
| 2 | 80 | −0.0022 | +0.9704 | 0.9727 | 1.0343 |
| 2 | 120 | +0.0225 | +0.9920 | 0.9695 | 1.0343 |
| 2 | 160 | +0.0180 | +1.0061 | 0.9881 | 1.0343 |
| 6 | 40 | −0.1657 | +0.7669 | 0.9327 | 751/768 = 0.9779 |
| 6 | 80 | −0.1302 | +0.8460 | 0.9762 | 0.9779 |
| 6 | 120 | −0.1253 | +0.8548 | 0.9800 | 0.9779 |
| 8 | 40 | −0.0752 | +0.7965 | 0.8717 | 12817/14400 = 0.8901 |
| 8 | 80 | −0.0406 | +0.8712 | 0.9118 | 0.8901 |

**What the table shows.**
- At every computed K the actual step 5 → 7 lies between 0.87 and 0.99.
- At ν = 6 and K = 120 it is 0.980, within 0.003 of the package's 751/768.
- **Why the package step is so close.** The package's arithmetic bounds exceed the exact valuations by nearly the same amount at s = 5 and s = 7: 0.115 and 0.145 per K² at K = 40, 0.098 and 0.092 at K = 80, 0.084 and 0.077 at K = 120 (E25, over the primes p > √K at leading order, reproduced by two skeptics). So the overestimate largely cancels in the step.

**Not shown.**
- No limit in K, and no theorem about the actual step.
- Nothing at proportions other than Fauzan's.
- A theorem would need a lower bound on e(7), the open part of Claim 6's H0, together with the package's upper bound on e(5).

| claim | command (from this folder) | expected output |
|---|---|---|
| the table | `python3 -B actual_step.py` | `out/actual_step.log`: the nine rows above; package steps 9929/9600, 751/768, 12817/14400 exactly |

## Relation to earlier work

- The step identity 2β/3 + ΔI_out is E42's Prop. 1′ and Cor. 4. For β = 1 − α it is in Lean (`thetaPkg_sstep`).
- step ≥ 2β/3 − J_s + J_{s+2} is lane A's review of E63, Lemma B (`../A-e63-unsaturated-review/`, C108-A-E63-COST).
- `../W-generic-step/` drops J_{s+2} and bounds J_s by a triangle.
- **New here:**
  - the outer per-pole term 2∫P = 4/9 − 2α + (2/3)α² in the lower bound, and its closed form;
  - the upper bound 2β/3 + 4/9 for every (α, β, ν) and every s; at the template it equals the value 191/180 that E62 gives for s ≥ s*(ν);
  - the uniform constant 7/54;
  - the comparison with ζ(5)'s grid floor.
- No literature search has been done for this folder.

## Review

A same-family review was run on Sun 15 Nov, 07:19–07:42 PT, by a fresh-context Claude Opus 5.5 subagent that wrote its own code (`review/REVIEW.md`, `review/rv_*.py`, `review/*.out`). The parent replayed all four scripts unmodified, in isolation; the outputs are identical apart from runtimes.

**Verdict.** The theorem and both corollaries hold (PASS on tasks 1–3).
- Every proof step matches pkg_ab's actual formula.
- No counterexample was found: 0 violations at 50 in-domain edge points, 600 random in-domain points and 754 scan cells.
- pkg_ab's exact I_out agrees with the reviewer's own exact integral everywhere.
- Both bounds are attained with equality.
- Integrality of ν is genuinely used: the per-index step fails for non-integer ν, although the bounds still held at 426 such points.

**Tasks 4–5 were PARTIAL; all the findings are fixed above.**
- The scan check read two of the four scan files: 651 cells, now 679.
- Two minima were rounded up: 0.790 is now 0.789, and +0.483 "at every cell" is now +0.4827, so ≥ +0.482.
- "ζ(5) closes" was used where floor₅ < 0 was meant.
- E62 Proposition 2 was called a "ceiling".
- "Admissible" was used without a definition.
- The ν scope note covered only L_a.
- The source of U-freeness was given wrongly.

**Two notes on `pkg_ab.py`, which is not this folder's file.**
- `int_R_x3` cannot run at α = 0.
- `zmin` is a sampled test, accurate to about 5·10⁻⁸ at the saturation edge. Below saturation `I_out` still raises, so no wrong step value is produced.

**What the review does not change.** It is not a second-family review and not a human check, so the label stays CONJECTURE (PROOF-DRAFT; `\Written` in the report).

| claim | command (from `review/`) | expected output |
|---|---|---|
| all proof steps, edge points, 300 random points | `python3 -B rv_exact.py 300 20261115 > rv_exact.out` | `SUMMARY: 0 failed checks []` (about 20 s) |
| the Values table, 691/800, the scan counts and minima, `min_lower` | `python3 -B rv_numbers.py > rv_numbers.out` | §1 four `MATCH`; §2 691/800 at (7, 10); §3 754 cells, 0 violations; §4 the 651-cell minima; §5 0.2319 |
| `zmin` is sampled | `python3 -B rv_zmin_probe.py > rv_zmin_probe.out` | exact −1e−9 against PkgAB.zmin +5e−8; I_out raises |
| non-integer ν (outside the domain) | `python3 -B rv_real_nu.py 600 1 > rv_real_nu.out` | 426 points, 0 violations |

## Files

- `bounds.py`: the closed forms (`lower`, `upper`, `uniform`, `J`, `Pi`, and `laneW` for comparison).
- `check_pointwise.py`, `check_scan.py`, `check_random.py`, `min_lower.py`, `zeta5_side.py`: the checks above. Each imports `../scope_alpha_beta/pkg_ab.py` read-only.
- `out/`: their logs, and `min_lower.json`.
