# nu8_rescue / derive_fauzan-residue: the outer estimate at K/3 < p ≤ 17K/40 for (s, ν) = (5, 8)

**EVENT WORK**, route A, Claude Opus 5.5, Sat Nov 14 2026. No human has checked this file.
Scope: (s, ν) = (5, 8), α = 3/40, λ = 1 − α, K ∈ 40Z, Fauzan's bound package as generalised in
`../../criterion5/derivation.md` §1-§3 (E13). Read-only inputs: `../../margin/theta.py`, `../../slack58/slack58.py`,
`../../obstacles/budget.py`, `../../certify/out/{A,LB,margins}.json`, the exact Δ_K files of E16/E35/E38.
Sources: Fauzan, Zenodo 22826419 v1. (4.9)-(4.14) and the proof of Prop. 4.1 were read on the page images,
pp. 10-13 (`pdftoppm -r 110 -f 11 -l 13`). Lemmas 3.1-3.2 (pp. 6-7) and (5.4)-(5.10) (pp. 14-15) were read in the
extracted text.

## 0. Bottom line

1. **Route A read literally cannot drop the cap (HEURISTIC).** In the outer basis (4.11), a cross-class entry is μ
   of a polynomial. Fauzan, p. 12, says only that such entries are integral (CITED). A positive removed-class weight
   (for example w = 3/2 for row i = 2 of an ℓ = 5 removed class) would need these entries to be divisible by p²,
   and nothing in (4.10)-(4.12) gives that. Lemma 4.2 (p. 12) needs nonpositive weights, and for its hypotheses its
   loss min(r, z) is attained. So inside the basis (4.11) the cap and the rank loss cannot be removed entry by entry.
2. **What works instead (PROOF-DRAFT, §2).** Change the basis in Fauzan's outer argument from (4.11) to the
   Chinese-remainder basis (4.5) with the allocation (4.4). Then for **K/3 < p ≤ (17/40)K** the proof of Prop. 4.1
   (pp. 10-11) goes through line by line at (5, 8), for K large. The removed-pole classes get **uncapped** weights
   i + 4 − (ℓ_K(a) + 4)/2, and there is **no rank correction**, because the polynomial moments are handled inside the
   distribution formula (Lemma 3.1, deg U_0 ≤ p + 1). So v_p(Δ_K) ≥ γ_p^in = pΓ_(5,8)(K/p) + O(1) holds there.
3. **Improved outer weight and its exact integral (COMPUTED, exact rationals).** On (1/3, 17/40], replace the
   package's outer integrand T_out(y) = g(y) + scal(y) by y·R_(5,8)(1/y). This is smaller on the whole interval, and
   it equals T_out at y = 17/40 = γ\*. The decrease of A\*(5, 8) is
   **∫_(1/3)^(17/40) (T_out(y) − y R(1/y)) dy = 1159/28800 = 0.0402431** per K². Equivalently, the inner range moves
   down from x = 3 to x = 40/17. I_out(5, 8) = 125021/96000 becomes 363473/288000. Restricted to (1/3, 0.37] the
   decrease is 18397/720000 = 0.025551. E39's target there (cap + rank) is 103/8000 + 11939/720000 = 0.029457. The
   new weight does not reach g − cap − rank pointwise: it sits 0.07-0.21 K above it on (1/3, 0.37]. It keeps gaining
   up to 17/40, though, so its total is larger.
4. **Margin (COMPUTED).** The certified bracket [A\* + LB, A\* + U_θ] for (5, 8) moves from [+0.016654, +0.057723]
   (E33) to **[−0.023589, +0.017480]**. The package is therefore no longer certified to fail at (5, 8). It would close
   with a comparison measure whose U(ρ) is within 0.023589 of the certified dual floor LB(8) ≥ −0.7751727.
   theta's opt36 is 0.041070 above that floor, so it still fails, by +0.017480.
5. **Check against exact valuations (COMPUTED).** Data: all five (5, 8) runs, K = 40..200, re-verified from the
   coefficient files. There are 14 pairs (K, p) with K/3 < p ≤ 17K/40. **None violates** the finite-K integer bound
   γ_p^in (§3). The slacks v_p(content Δ_K) − γ_p^in are +1, +12, +3, +10, +18, +3, +21, +10, +4, +12, +30, +30, +3, +3.
   Over all 86 outer pairs with K/3 < p ≤ K, γ_p^in has no violation wherever it is defined, and neither does the
   package's own finite-K outer bound. The package bound is exact (slack 0) at every outer prime with p > K/2.

## 1. Why the basis (4.11) charges the cap and the rank loss (HEURISTIC, with CITED steps)

At (5, 8), with y = p/K ∈ (1/3, 0.4), every class a ≤ (p−1)/2 has ℓ = ℓ_K(a) ∈ {5, 6}. The removed classes are
a ≤ N. The weights (4.12), generalised in E13 §3, are min(0, i + 4δ − (ℓ + 4)/2):
- removed, ℓ = 5: uncapped −1/2, +1/2, +3/2, plus one E-row of weight 0. Capped cost 1, uncapped −3, so the cap is 4.
- removed, ℓ = 6: uncapped −1, 0, 1, 2, plus one E-row. Capped cost 2, uncapped −4, so the cap is 6.

The class blocks satisfy the uncapped bounds (residue part, p. 12: i + j + 8δ − ℓ − 4). A positive weight also has to
bound every cross-class entry of its row. Those entries are μ of polynomials ("integral, since their quotients are
polynomials with integral coefficients", p. 12, CITED), and after the split (4.10) they are only known to be
p-integral. Lemma 4.2 assumes w ≤ 0 ("The restriction to nonpositive weights is essential", p. 12, CITED). Its loss
max_k (k + 2 Σ_(i≤k) w_(i)) = min(r, z) is the worst case over complementary minors of L, and the bound
rank L ≤ r_p = K + 6N − 2p + 2 (p. 12, with 4N → (ν−2)N) is far above z ≈ 0.45K here. Nothing in (4.10)-(4.12) gives
the minors of L on zero-weight rows extra valuation. Conclusion (HEURISTIC): route A must change the basis.

## 2. The outer range near K/3 with the inner basis (PROOF-DRAFT)

**Proposition A.** Let (s, ν) = (5, 8), α = 3/40, K ∈ 40Z with K large, N = αK, h = K − N, and let p be prime with
K/3 < p ≤ 17K/40. Take m = (p−1)/2, L_0 = 2, b_a = 4ℓ_N(a), mT + E = h − 2 + 4N (0 ≤ E < m), ε_a = 1 on the E
classes with the largest ℓ_K(a), L_a = T − b_a + ε_a, Z_a = T + ε_a, and
  w_(a,i) = i + b_a − (ℓ_K(a) + 4)/2 (a ≥ 1, i < L_a),   w_(0,i) = min(2i − 3/2, min_c (Z_c − (ℓ_K(c) + 4)/2)) (i < 2).
Then v_p^G(Δ_K) ≥ γ_p^in := 2 Σ w. Moreover γ_p^in = pΓ_(5,8)(K/p) + O(1) uniformly, with Γ_(5,8) as in
criterion5 §2.

*Proof.* This is Fauzan's proof of Prop. 4.1 (pp. 10-11) with 6 → ν = 8 and 3 → ν/2 = 4. Fauzan's s is 5, so
Lemmas 3.1-3.2 and the prefactor p^(−4) are used unchanged (CITED). Only the places where (4.1) ("K/M < p ≤ K/3") is
used need checking. Write y = p/K ∈ (1/3, 17/40] and x = 1/y ∈ [40/17, 3).
- **Counts.** N < p/2, since y > 2α = 0.15. So ℓ_N(a) = [a ≤ N] ∈ {0, 1}, m_N = 0 and b_a ∈ {0, 4}. Also 2p ≤ K < 3p,
  so m_K = 2. ℓ_K(a) = 5 − [a > v] + [a ≥ p − v] with v = K − 2p. One of the two brackets is constant on
  a ≤ (p−1)/2, so ℓ_K takes **two consecutive values** ({5, 6} for y < 0.4, {4, 5} for y > 0.4). This is the fact used
  in the proof's comparison step.
- **L_a ≥ 0.** (h − 2 + 4N)/m > 2(1.225K − 2)/p ≥ 2·1.225/0.425 − 4/p > 5 for p > 6, so T ≥ 5 > 4 ≥ b_a. Hence
  L_a ≥ 1. Fauzan's estimate "T − b_a > 2λx − 81/20" is not needed: it is crude, and at ν = 8 it would fail below
  x ≈ 2.73.
- **(4.2) at an ordinary source c ∈ {a, p − a}.** For x = c + pz the near poles are z = k with |k| ≤ 3, because
  j ≤ K < 3p. Distinct near poles differ by at most 5 < p, so by a unit. The harmonic indices are below p. Far factors
  are units times series in pz. The leading numerator has degree ≤ ν_i + ν_j + 8ℓ_N(c) ≤ 2Z_c ≤ 2(T + 1) ≤ 16 ≤ p + 1,
  since T ≤ ⌊2·1.225K/(p−1)⌋ ≤ 7 and p > 13.3n ≥ 15 for K ≥ 80. So Lemma 3.1 applies, which gives
  ν_i + ν_j + 8ℓ_N − ℓ_K − 4.
- **(4.3) at c = 0.** The near poles are z = ±1, ±2 (p, 2p ≤ K), distinct units. The degree is
  5 + 2ν_i(0) + 2ν_j(0) ≤ 5 + 4L_0 = 13 ≤ p + 1. The bound is 2ν_i(0) + 2ν_j(0) + 16m_N − 2m_K + 1 =
  2ν_i(0) + 2ν_j(0) − 3. Hence the zero-row half-weight 2i − 3/2 in w_(0,i).
- **Comparisons (p. 11).** Ordinary source c: Z_c − Z_a + 1 + (ℓ_K(a) − ℓ_K(c))/2 ≥ 0, by the two-values fact and the
  ordering of the extras, word for word as in Fauzan. Zero source: an ordinary row has half-weight
  2L_0 + 8m_N − m_K + 1/2 = 5/2 there, and every ordinary weight is ≤ Z_a − 1 − (ℓ_K(a) + 4)/2 ≤ 5/2 (T ≤ 7 with
  ℓ_K ≥ 5 for y ≤ 0.4; T ≤ 6 with ℓ_K ≥ 4 for y > 0.4). The zero rows satisfy (4.7) by definition. The basis (4.5) is
  Z_p-unimodular (p. 10, no range condition).
- **Leading order.** The argument for (5.7) (p. 14) uses O(1) intervals of constancy and O(1) dimensions. It is
  uniform in x ∈ [40/17, 3], and formula (5.4) needs no change. The finite-K allocation in `residue58.py` agrees with
  pΓ(K/p) to within 9-15 at K = 160, 200 (`out/check.txt`, last two columns).
- **No rank term.** The polynomial moments are never split off. They are inside the local functions, and Lemma 3.1
  covers them through deg U_0 ≤ p + 1 and the factor p^j for j ≥ 1. So min(r, z) does not appear. ∎

*Consequence.* For K/3 < p ≤ 17K/40, v_p(Δ_K) ≥ max(γ_p^out, γ_p^in). The S_K parts agree exactly:
scal(y) = −y N(1/y), checked at 999 exact points (COMPUTED). So on (1/3, 17/40] the improved integrand is
**T_new(y) = y R_(5,8)(1/y)**, in place of T_out(y) = g(y) + scal(y). In class terms:
- removed classes a ≤ N: L_a = T − 4 + ε_a rows, uncapped weights i + 2 − ℓ_K(a)/2;
- unremoved classes: L_a = T + ε_a rows, weights i − (ℓ_K(a) + 4)/2;
- zero block: 2 rows;
- no rank loss; T = ⌊2Hx⌋ + O(1/p), H = 49/40.
T_out − T_new is positive on (1/3, 17/40) (exact at 399 points; both functions are piecewise affine) and vanishes
at 17/40. The pointwise values are 0.866 K at y = 0.3334, 0.535 K at 0.37, 0.25 K at 0.40, and 0 at 0.425. Above
17/40 the package's outer bound is the better one, so γ = 17/40 is the largest γ for which the replacement gains.
That is also as far as it is claimed.

## 3. Numbers (`python3 residue58.py integral` → `out/integral.txt`; `check` → `out/check.txt`)

| quantity | value | label |
|---|---|---|
| cap + rank on (1/3, 0.37] (E39's Z) | 103/8000 + 11939/720000 = 0.029457 | COMPUTED (reproduces E39) |
| γ\* = first zero of T_out − y R(1/y) after 1/3 | 17/40 | COMPUTED, exact |
| decrease of A\*(5,8) = ∫_(1/3)^(17/40) (T_out − yR(1/y)) dy | **1159/28800 = 0.04024306** | COMPUTED, exact |
| same, used only on (1/3, 0.37] | 18397/720000 = 0.02555139 | COMPUTED, exact |
| A\*(5,8): certified [0.79182638, 0.79182639] → | [0.75158333, 0.75158334] | COMPUTED (interval minus exact rational) |
| bracket [A\* + LB_lo, A\* + U_θ] | [+0.016654, +0.057723] → **[−0.023589, +0.017480]** | COMPUTED |
| finite-K pairs K/3 < p ≤ 17K/40, K = 40..200 | 14, violations 0, min slack +1 (K = 40, p = 17) | COMPUTED |
| all outer pairs K/3 < p ≤ K | 86; γ^in violations 0 where defined; package-bound violations 0 | COMPUTED |

The finite-K bound is computed as follows. It uses Fauzan's (4.4)-(4.8) with the smallest zero block L_0 ≥ 0 for which
the comparison, zero-source and degree checks of §2 all hold (L_0 = 2 in the claim range, (T, E, L_0) printed per
prime). The exact side is v_p(content Δ_K) from the run JSONs, re-verified from the coefficient files by
`slack58.verify_one` (content and primitivity recomputed, SHA-256 against `boundary5/out/SHA256SUMS*`). Exact
integers throughout. Note one tension: at K ≤ 200 the hypotheses "K large" (§2) do not hold literally; the check
tests the bound's formula, not the asymptotic hypotheses.

## 4. What this does not show

- No human has checked Proposition A. It reuses Fauzan's Lemmas 3.1-3.2 (CITED, s = 5, unchanged) and E13's ν-reading
  of (4.2)-(4.8) (PROOF-DRAFT, others'). The O(1) in the leading order is not made explicit.
- The improvement does not close (5, 8) on its own. It needs a comparison measure within 0.023589 of the certified
  dual floor (theta's opt36 is 0.041070 above it); see `../measure/`.
- The exact valuations are still 0.07-0.21 K below the new bound at p/K ≤ 0.37, and E39's profile is above it on
  (0.37, 0.425]. So the new bound is not sharp there. Matching the exact profile (E39's HEURISTIC limit ≈ 0.051)
  would need a better allocation than Fauzan's (4.4) (CONJECTURE: an allocation tuned to the outer pole counts).
- Coincidence noted, no claim: A\*_new = 0.75158 and the exact a_200 = 0.7515 (E38).

Reproduce (from this folder; about 10 s, one process): `python3 residue58.py integral && python3 residue58.py check`.
