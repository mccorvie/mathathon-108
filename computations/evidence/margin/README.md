# evidence/margin: one-package margin tool for #108 (`theta.py`)

**EVENT WORK** (Fri Nov 13 2026, 21:04-21:41 PT). Experimenter: Claude Opus 5.5. Owner of `theta.py`:
the experimenter. Other agents may import or run it, never edit it.

Python 3.14, standard library `fractions` for every arithmetic-side number; `mpmath` (50 digits) for the
energy; `numpy`/`scipy` only for the potential supremum and the comparison-measure optimiser (float64,
labelled HEURISTIC below). No randomness: every test point is a fixed fraction; seeds: none needed.

## The package (one set of bounds for every (s, ν))

- **Arithmetic side**: Lai, ai.vixra 2609.0080v1, Thm 9.3 (p. 13), eq. (78) without the E_M term:
  `A_M = I_out + c_cr·λ/M + ∫_3^M R(x)/x³ dx`, computed **exactly** (R and the outer integrand are
  piecewise affine; every piece is checked at 11 fixed interior fractions). R = −Γ − N is Lai (72)-(79)
  (p. 12-13), written as in mo271/Zeta5@7fe73676 `scripts/appendixB.py`; I_out is Lai (84) (p. 14) with the
  outer function of Zeta5 `appendixB.py` (ζ(5)) and [team handle]/zeta7-irrational@be55b3a4
  `ZetaSeven/OuterLimiting.lean` (ζ(7)).
- **Analytic side**: Lai Lemma 11.4 (p. 15): `U = λM_0 − I(ρ) + C*(ν)` for a comparison measure ρ of mass λ.
- **Margin** = A_M + U (the method closes only if < 0).
- ν = numerator power = exponent of D_N (Fauzan 6, Anand 8, Lai's ζ(7) claim 2).

## 1. Anchors (reproduced before any new value) — COMPUTED, exact

Command (3 s): `python3 theta.py anchors` → `out/anchors.log`
(sha256 `212719a17d5c387ee33749940746b718bb9822c75b8e7667ebce9a582dfe1767` after the 22:00 revision, which only adds the
REVISION CHECKS block; theta.py sha256 `2f1f90ade5ea082c73259fc16b9494692e8ad546197b08739b20e324e4e3b015`). Anchors 1-2 passed at Fri 21:26 PT, the exact
Zeta5 constant A_Z5 at 21:36 PT.

| Anchor | Source | Reproduced value | Match |
|---|---|---|---|
| I_out (ζ(5), ν = 6) | Lai (84), p. 14 | 127751/96000 | exact |
| ∫_3^20 R/x³ (ζ(5)) | Lai (103), p. 17 | 322437603634266857629/7535670527041937280000 | exact |
| A* with Lai's tail bound −2689/48000 | Lai (103) | 9928298118277006344769/7535670527041937280000 | exact |
| **A_200 by Lai (102)** | Lai (104) | 127125602969131786927559/94195881588024216000000 = **1.3495876977** | exact |
| I(ρ) for Fauzan's 16-component ρ (table from Zeta5 `Apery/Measure.lean` l. 28-44) | Lai p. 15 | −2.126593445147050403253601 | 25 digits |
| C*(6) | Lai p. 15 | 2.65303599034048866112925 | 24 digits |
| **λM_0 − I(ρ) + C\*** with M_0 = −1329/200 | Lai Lemma 11.4 | **−1.3669955645124609356** ≤ U = −2733991/2000000 | 20 digits |
| sup_t 2U^ρ − V_6 (grid, HEURISTIC) | Lai (93): −6.64989… | −6.64989388 (< M_0 = −6.645) | 6 digits |
| A_200 + U | Lai (108): −0.0174078 | −0.0174078023 | 1e-10 |
| I_out (ζ(7), ν = 8, Anand) | audit `ZetaSeven.outerIntegral_value` | 453803/288000 | exact |
| ∫_3^20 R/x³ (ζ(7), ν = 8) | audit `ZetaSeven.innerIntegral_value` | 120667538150827615739401/708353029541942104320000 | exact |
| **A_200 + 44/25 by Anand (89)** | audit `ZetaSeven.primeSumA_two_hundred_add_u` | 6626902387705935050696033/1362217364503734816000000 = **+4.8647907158** | exact |
| Zeta5 Lean outer integral (rank loss r, not min(r, z)) | Zeta5 `scripts/growth/outer_gen.py` | 127751/96000 + 9/640 = 129101/96000 (9/640 = Lai Lemma 10.1, p. 14) | exact |
| Zeta5 Lean growth route at M = 400: outer + (5.18) + ∫_20^400 (xF(x)+27/16)/x³ + 6λ/400 | Zeta5 `Apery/Growth/TailIntegral.lean` l. 26; README "≈ 1.345" | 1.34475217 ≤ A_eff = 136/100 | yes |
| A_eff + U | Zeta5 `Apery/Constants.lean` l. 13, 33, 36 (`Aeff_margin`) | −13991/2000000 | exact |
| **A_Z5**, the constant `growth_mN` proves: −6843153/128000000 + (5.18) + 129101/96000 + 22.2/1600 | Zeta5 `Apery/Growth.lean` l. 115-116; miner `evidence/zeta5_repo/INSIGHTS.md` item 1 | 2031621487545722214389669/1507134105408387456000000 = **1.3480031274** (outer, (5.18), 6λ/400 computed here; the tail bound is Lean's) | exact |
| Lean's tail bound vs the exact tail ∫_20^400 (xF+27/16)/x³ | Zeta5 `Growth.lean` l. 115 | exact −0.0567130866 ≤ −6843153/128000000 = −0.0534621328 | holds |
| A_Z5 − A_400(Lai (102) at M = 400 = 1.3336203696) | miner item 2 | 1840993/128000000 = 9/640 + 40993/128000000 | exact |
| A_Z5 + U (unrounded Zeta5 margin) | — | −0.0189923726 | — |

**Where the anchors disagree with each other (COMPUTED, exact):**
1. **The audit's +4.8648 is not the package value.** Anand's (89) puts A_0 = 9928298118277006344769/7535670527041937280000
   ≈ 1.3175 (which is Lai's ζ(5) A*, (103)) where ∫_20^∞ R/x³ (≈ −0.06) belongs. With the exact Thm 9.3
   right-hand side the ζ(7), ν = 8 package gives **A_200 = 1.7230965709, A_200 + 44/25 = +3.4830965709**:
   still positive, so the failure verdict of the prior audit stands, but +4.86 overstates it by 1.38.
2. **Lai (102) is an upper bound with slack**: the exact Thm 9.3 RHS at M = 200 for ζ(5) is
   **A_200 = 1.3455147648**, 0.0040729 below (102), so the package margin is A_200 + U = −0.0214808.
3. **Zeta5 Lean vs Lai, located exactly**: A_Z5 = A_400(Lai (102)) + 9/640 + 40993/128000000. The 9/640 is the
   rank loss r instead of min(r, z) (Lai Lemma 10.1, p. 14; Zeta5 outer 129101/96000). The 40993/128000000 is
   the gap between Lean's rational tail bound (R ≤ xF + 27/16 on [20, 400], then −6843153/128000000) and
   Fauzan's tail polynomial in (102). With the exact tail the same route gives 1.34475217; the exact package with
   Zeta5's outer gives 1.3436254. A_eff = 1.36 rounds A_Z5 up by 0.0119969, so the certificate margin −0.0069955
   is 37% of the unrounded −0.0189924. Lai's A_200 = 1.3495877 (M = 200) and A_Z5 = 1.3480031 (M = 400) are
   different packages. Both are below −U = 1.3669955.

## 2. How s and ν enter (read this before the numbers)

ν enters the package through H = 1 + (ν/2 − 1)α, b = (ν/2)ℓ(αx, z), the N(x) coefficient 2ν, the outer
t-coefficients ν and ν − 1 and the term 2να, the rank intercept 1 + (ν − 2)α, and on the analytic side
V_ν = 2π√t + J_1 − νJ_α and C*(ν). Lai's own programs use exactly these (laichunwing/Zeta7-is-Irrational@c42a984f,
Programs 01, 06-08). **Four constants are not determined by the anchors**, because both anchors have ν = s + 1:

| constant | where | (5, 6) | (7, 8) | reading **S** | reading **N** | Lai's ν = 2 programs |
|---|---|---|---|---|---|---|
| c_in | Γ: (T + b − ℓ − c_in), s(2T − q − c_in) | 5 | 7 | s | ν − 1 | ν − 1 = 1 |
| c_out | outer leading term c_out(1 − y) | 7 | 9 | s + 2 | ν + 1 | 9 |
| ρ_r | outer rank r = 1 + (ν−2)α − ρ_r y | 2 (Zeta5, Lai) | 3 (Anand) | (s − 1)/2 | (ν − 2)/2 | 2 |
| c_cr | range-2 crude term c_cr·λ/M | 6 | 8 | s + 1 | ν | 8 (Anand's 9λ/M) |

Which reading is right is **not** computed here. Evidence for S on the decisive constant c_in (HEURISTIC, my
reading of the formal proof): in mo271/Zeta5 (checked out read-only at d38a2888) the offset 4 of the weights
w(a, i) = i + (b_a − 4)/2 (`Apery/Arith/InnerWeights.lean`, header) is the loss in
`Apery/Arith/DirectBound.lean` (header: v_p(τ_X(g)) ≥ min_c(e_c − ℓ_c) − 4), which `Apery/Arith/TauBound.lean`
(header) traces to the functional τ(P) = L(P''')/24, i.e. to ζ(5) (three derivatives, (s−1)! = 24). The
numerator power enters only through the zero counts e_c. For ζ(7), τ involves (s − 2) = 5 derivatives
whatever ν is, so c_in = 7 = s. Reading N would make A independent of s (ζ(49) as cheap as ζ(5)), even though the
denominators of H_j^(s) grow like lcm(1..j)^s (HEURISTIC).

## 3. Lai's ν = 2 claim (s = 7) — COMPUTED (exact rationals), verdict below

Command (part of `python3 theta.py all`, or `python3 theta.py lai`) → `out/all.log`, section "LAI nu=2".
Inputs: laichunwing/Zeta7-is-Irrational@c42a984f Programs 01-11 (blob SHAs checked against the git tree; cached
read-only in `~/mathathon-cache/108/lai_zeta7_c42a984f/`).

| quantity | Lai (09_final_constants.txt) | this tool, exact, with Lai's own formulas |
|---|---|---|
| I_inner = ∫_3^20 R/x³, "old coeff" (Program 06: N(x) uses νλx⌊αx⌋) | −0.2252285088 | **−0.2252285088** (10 digits) |
| same with the 2ν coefficient (Program 08 "CORRECTED", and the ζ(7)-ζ(49) repo) | robustness check −0.18 | −0.1789785088 |
| I_out (Program 07 formula; Lai: K = 4·10⁷, Simpson) | 2.0093485686 | 2.0092465278 (K → ∞) |
| A_0 = ∫_20^∞ R/x³ (corrected formulas) | −0.0512225151 | −0.0512341755 |
| A_200 with his inputs and Anand's polynomial 9λ/M − 11549/(720M²) + 44/M³ | — | 1.7741270378; + U_upper = **−0.5319858** (reproduces his ≈ −0.53) |
| U (Lemma 11.4 form; float sup) | −2.3061128852 (3 arcsine pieces, M_0 = −6.0) | −2.468652 (25 pieces, grid sup M_0 = −6.124578) |

The "old coeff" is the N(x) coefficient ν instead of 2ν. Lai's own Program 08 marks it CORRECTED, and it moves
I_inner by exactly 2λ∫_{40/3}^{20} dx/x² = λ/20 = 0.04625. So 09 mixes an uncorrected I_inner with a corrected A_0.

Package margin A_200 + U at (s, ν) = (7, 2), exact A_200 (Thm 9.3 RHS) with the stated constants:

| variant | A_200 | + U_Lai = −2.3061 | + U_ours = −2.4687 |
|---|---|---|---|
| Lai's formulas, 2ν fixed | 1.820558 | −0.485555 | −0.648094 |
| Lai's formulas, 2ν fixed, **only c_in = 7** | 3.642808 | **+1.336695** | **+1.174156** |
| Lai's formulas, 2ν fixed, only ρ_r = 3 | 1.792780 | −0.513333 | −0.675872 |
| reading N (all ν-attributed) | 0.840985 | −1.465128 | −1.627667 |
| reading S (all s-attributed; revised outer, E13) | 3.602999 | +1.296886 | +1.134346 |

**Verdict (scoped to this package):** with Lai's own formulas the claim survives his flagged coefficient (exact
margin −0.486 with his U, −0.648 with a better comparison measure; the analytic side is not the problem). It
**fails at one located term**: the inner-weight offset c_in. Lai's Program 06 uses (T + b − ℓ − (ν − 1)), which
at ν = 2 means (T + b − ℓ − 1). Anand's ζ(7) template has (T + b − ℓ − 7), and in Zeta5's proof this offset is
a loss of the functional τ, which depends on s, not ν. With c_in = 7 alone, ∫_3^200 R/x³ rises by 1.822 and
the margin becomes +1.17 to +1.34. The numbers are COMPUTED; that c_in = s is right is HEURISTIC (section 2).

## 4. Table: A_200, A_∞, U and margins for s = 5, 7, 9 and ν = 4..10

`python3 theta.py all` (75 s) → `out/results.json` (sha256 `6af6d3c8e665efaf0f85c06f4e250ee756a098dca591ae7088cc56696774bb9d`),
`out/all.log` (sha256 `ad435427008c3aeaee8333d1a233b33db62cfff4beb8d80fa8e41e1aa6d73bf5`), `out/U_cache.json` (the measures;
sha256 `e6e6272ae5aaa0456810c1ebf993212ffae3e0e80e7f587550f2b9f9b720ecb4`, identical on rerun). Range: s ∈ {5, 7, 9},
ν ∈ {4, …, 10} (plus ν = 2 for U), M = 200 and M → ∞, readings S and N. Odd ν (*) is the formulas'
continuation: b = (ν/2)ℓ is then a half-integer and the construction's integer allocation is undefined.

- **A_200** is the exact Thm 9.3 right-hand side (a rational, listed in results.json; COMPUTED).
- **A_∞** = I_out + ∫_3^∞ R/x³: exact on [3, 200], then R(x + 40k) = R(x) + 40k·F(x) (identity checked exactly
  for k = 1, 2, 3 at 7 points per piece) summed in float64 over 20000 periods plus F̄/X (COMPUTED to about 1e-9).
- **U(ν)** = λM_0 − I(ρ) + C*(ν), the best of Fauzan's ρ and an SLSQP-optimised family of 36 arcsine measures on
  [0, L_j]. I(ρ) and C* are exact closed forms (50 digits). **M_0 is a float64 grid supremum** (about 90000 points
  on [0, 60] plus endpoints, locally refined, rounded up to 1e-6), so U is HEURISTIC in the same way as Lai's
  own 4100-point check. At ν = 6 this gives −1.371522, below the certified U = −1.3669955 because Fauzan's
  M_0 = −6.645 is rounded up from the grid value −6.649893.

Reading S below uses the **revised outer function** (Revision, section 7). Column Δ is the change at s = 5 from the
pre-revision table (it equals the change in I_out; the inner part is unchanged).

| ν | U(ν) | S: s=5 A_200+U | Δ (s=5) | S: s=7 A_200+U | S: s=9 A_200+U | N: any s A_200+U | S: s=5 A_∞+U | S: s=7 A_∞+U |
|---|---|---|---|---|---|---|---|---|
| 2 | −2.468652 | — | — | +1.134 | — | −1.628 | — | — |
| 4 | −1.959093 | −0.02118 | −0.01672 | +0.99278 | +2.05014 | −0.86203 | −0.04410 | +0.96986 |
| 5* | −1.671180 | **−0.03473** | −0.01203 | +0.96438 | +2.01705 | −0.47823 | −0.06222 | +0.93689 |
| 6 | −1.371522 | −0.02601 | 0 | **+0.95186** | +1.99797 | −0.02601 | −0.05807 | **+0.91980** |
| 7* | −1.057168 | +0.01050 | +0.02234 | +0.95846 | +1.99563 | +0.46920 | −0.02613 | +0.92183 |
| 8 | −0.734103 | +0.09892 | +0.08344 | +0.98899 | +2.00679 | +0.98899 | +0.05772 | +0.94779 |
| 9* | −0.401503 | +0.21323 | +0.15692 | +1.03752 | +2.03305 | +1.52734 | +0.16746 | +0.99175 |
| 10 | −0.060015 | +0.34237 | +0.23432 | +1.14194 | +2.08247 | +2.08247 | +0.29203 | +1.09160 |

**What the table shows (COMPUTED numbers; interpretations HEURISTIC):**
- Under reading S, for ν ≤ s + 1, each extra unit of ν lowers A_200 by about 0.30 (more numerator zeros, more
  p-adic gain) and raises U by about 0.30 (a stronger external field), so the margin is nearly flat. Past ν = s + 1
  the outer savings are capped (a removed-pole class cannot gain below weight 0), so A stops falling as fast while U
  keeps rising, and the margin climbs. **s, not ν, sets the floor**: best about −0.035 at s = 5 (ν = 5, a formula
  continuation; −0.026 at even ν = 6, Fauzan's choice), +0.952 at s = 7 (ν = 6), +1.996 at s = 9. No ν in 4..10
  makes s = 7 negative (best at M → ∞: +0.920).
- Exact s-step, U-free: Θ(7, 6) − Θ(5, 6) = **751/768** = 2λ/3 (primes p ≤ K/3) + 1387/3840 (outer), for every M and
  every comparison measure; Θ(7, 8) − Θ(5, 8) = 12817/14400 (COMPUTED, both confirmed independently of criterion5).
- (7, 8) is an anchor point (S and N agree there): +0.989 with the optimised measure, against +3.48 with Anand's
  U = 44/25 (whose comparison measure is far from optimal). Our pre-event exact determinants for n ≤ 9 grow like
  about exp(0.9K²), just below this upper bound (consistent, not a proof).
- Under reading N the margin depends only on ν and falls below zero for ν ≤ 6 at every s. That is Lai's ζ(7)-ζ(49)
  claim, and it stands or falls with c_in = ν − 1.

## 5. Figure

`out/margin_vs_nu.svg` (checked with `rsvg-convert` → `out/margin_vs_nu.png`). It plots A_200 + U against ν for reading S
at s = 5 (blue), 7 (red) and 9 (green), and for reading N (grey dashed, the same for every s), with the zero line,
Lai's ζ(5) anchor (square at ν = 6, −0.0174) and, at ν = 2, Lai's claim (−0.53, triangle) beside our exact
values: Lai's formulas −0.65, the same with c_in = 7 +1.17, reading S +1.13. **What it shows:** under the
s-attribution the three curves are about 1 apart and flat up to ν = s + 1 (rising after it, where the outer savings are capped), so the zeta value (through the inner offset c_in and
the outer constants) sets the margin. Under the ν-attribution one line slopes steeply down to the left; that slope is
the whole of Lai's ν = 2 claim.

## 6. Caveats

- Every "fails" is scoped to this package: Lai's Thm 9.3 local bounds (E_M dropped, as in Lai §12), a
  comparison-measure U, and the constants' (s, ν)-attribution of section 2. None of it shows the template
  cannot work with sharper p-adic bounds or the equilibrium measure.
- The general-s formulas (reading S at s = 9, and every off-anchor point) are an **extrapolation**: nobody has
  written Fauzan's §4 estimates for general (s, ν). Only the two anchor points are checked against published
  derivations; the Zeta5 Lean supports c_in = s structurally (section 2), and ρ_r = (s−1)/2 is a fit to two points.
- U uses a grid supremum (HEURISTIC). The arithmetic side is exact.
- Prior work used: Lai's note and programs, mo271/Zeta5 (Firsching, Paul-Lez) scripts and Lean, our audit
  [team handle]/zeta7-irrational@be55b3a4 (prior work). Everything in this folder was computed during the event.

## 7. Revision (Fri 21:53-22:00 PT, at the orchestrator's request)

**What changed.** For reading S, theta.py's outer function is now the class sum of the criterion advocate's
derivation (`../criterion5/derivation.md` §3, dossier E13, PROOF-DRAFT): a class with ℓ poles j ≤ K and one removed
pole costs c¹(ℓ) = Σ_(i<ℓ−2) max(0, ℓ + s − 1 − ν − 2i) and has z¹(ℓ) zero weights (Fauzan (4.12) with 5 → s,
6 → ν); an unremoved class costs (s + 2)(ℓ − 2) and has two zero weights (`Pkg.outer_parts`). Before, the outer
function used the family coefficients ν, ν − 1, 2να and the zero counts y − α + u, y + u, extrapolated linearly in ν.

**Why.** The two forms agree exactly on ν = s + 1, which is all the anchors test. Checked here at s = 3..11, 400
exact points each (REVISION CHECKS in `out/anchors.log`). Off that family the linear form ignores the min(0, ·) in
the class weights. It counts numerator zeros beyond a class's poles as further savings, so it undercounts the cost
for ν > s + 1, and it slightly overcounts it for ν < s + 1. I_out changes by −0.0120 at most off-family points
with ν < s + 1, −0.0167 at (5, 4), and +0.0834 at (5, 8) and +0.2343 at (5, 10). At M → ∞ the margin at (5, 8)
moves from −0.026 to **+0.058**.

**Unchanged.** The inner function R, U(ν) (the same measures: `out/U_cache.json` hash identical), reading N, Lai's
own formulas ('LAI'), and all three anchors. All anchors still pass, since they sit on the family. The pre-revision
outer is kept as reading 'S0' for comparison. **Confirmed exactly** (theta.py, independent code): Θ(7,6) − Θ(5,6) =
751/768 at M = 40 and 200, I_out(7,6) − I_out(5,6) = 1387/3840, I_out(7,2) = 31511/16000 (= 1.9694375), and Fauzan's
removed-class costs 0, 1, 2, 4, 6 at (5, 6). Effect on the headline numbers: the ν = 2 verdict for Lai is unchanged
(reading S +1.134 instead of +1.146; Lai's-formula rows untouched), and s = 7 and s = 9 stay positive for every
ν in 4..10. The s = 5 picture sharpens: ζ(5) closes only for ν ≤ 6 (even ν), and ν = 8 does not close it.
