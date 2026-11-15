# The (s, ν) margin of Fauzan's bound package: derivation (PROOF-DRAFT)

EVENT WORK, Fri Nov 13 2026, advocate:criterion5 (Claude Opus 5.5). No human has checked this file.
Every computation it quotes is reproduced by the scripts in this folder (README.md). Labels follow AGENTS.md §2.

**Sources** (all opened for this derivation):
- Fauzan, *ζ(5) is irrational*, Zenodo 22826419 v1 (Sep 17 2026), cached at `~/mathathon-cache/108/fauzan_22826419.pdf` (sha256 a42c05cc…0da). Equation and page numbers below are Fauzan's unless stated.
- Lai, ai.vixra 2609.0080v1 (the problem's reference): eq. (7)-(9) p. 3, Def. 4.2 p. 4, §7 pp. 9-10, (72)-(79) pp. 12-13, (84) p. 14, (88)-(93) pp. 14-15, (101)-(108) p. 17.
- Xu, Anchen0823/zeta9-research-notes@eb264a73, `missions/zeta7/research/analytic-foundations.md` §1-§5 (24 Sep 2026): the functional w_s, the field V_(q,α), C*(q,α,β), the real bound (12), the criterion (13), the moment cutoff (14)-(15). **Xu already states that U does not depend on s, and that s changes only lower-order factors of the weight (§3).** Everything in §4 below is Xu's, restated.
- mo271/Zeta5@7fe73676 (Lean ζ(5)): `Apery/Arith/DirectPoly.lean` l. 264-284 (`tauX_direct`: loss 4 = 5 − 1), `DirectBound.lean` l. 84 (`VG_H5`: v_p(H⁽⁵⁾) ≥ −5) and l. 164 (`VG_res`: +1), `ClassCount.lean` l. 102 (`Bse` = 5[a=0] + 6S_N − S_K). The miner's `evidence/zeta5_repo/INSIGHTS.md` §4 lists the same lines with HEURISTIC general-s readings; this file proves those readings.
- keithadler/zeta42@afd4190f `zeta7/README.md` l. 40-48 (24 Sep 2026; cached as `~/mathathon-cache/108/lit/keithadler_zeta7_README_afd4190f.md`): the *measured* version of §6. At K ≤ 80 the real side is almost s-blind, the arithmetic side costs about 0.88 K² more at s = 7 (d_j^7 against d_j^5), and the numerator only trades one side against the other. Corollary 4 below is the package-level, exact counterpart (0.978 at ν = 6). The qualitative statement is known (librarian, `evidence/literature/MAP.md` §D(ii)).
- Our prior audit [team handle]/zeta7-irrational@be55b3a4 (PRIOR WORK): `ZetaSeven/InnerLimiting.lean` (Anand's Γ with "−7", b = 4ℓ, N with 16λx) and `OuterLimiting.lean` (Anand's g(y)).

## 0. Notation and the one hypothesis on parameters

s = 2r + 1 ≥ 3 odd. ν = the exponent of D_N in the Hankel entries μ_X(D_N(t)^ν t^(i+j)/D_K(t)): ν = 6 for Fauzan, 8 for Anand, 2 for Lai's ζ(7) claim; Xu writes ν = 2q. ν must be even, because Fauzan's integral row basis f_i = (D_N/(N!)²)^(ν/2) q_i ((3.11), p. 9) splits D_N^ν between the two sides of the Gram form. α = N/K and λ = h/K = 1 − α (h = K − N, as in Fauzan, Anand and Lai); the numbers use α = 3/40. H := λ + (ν/2)α, which is 23/20 for ν = 6 (Lai (8)) and 49/40 for ν = 8.

The **package** P(s, ν, α) is Fauzan's §3-§5 with s and ν carried as symbols: the τ-pullback and distribution formula (§3.1-3.2), the crude small-prime bound (3.12), the inner class basis (4.4)-(4.8), the outer rank decomposition (4.10)-(4.14), the Legendre valuation of S_K = 4^(h−1)(K!)^(2h)/((N!)^(2νh)∏(2i)!²), the PNT prime sum (5.11), and a comparison measure ρ for the real bound (Lemma 6.1 = Lai Lemma 11.4). The margin of the package is

  Θ(s, ν, α; M, ρ) = A_M(s, ν, α) + U(ν, α; ρ),

and the method proves ζ(s) irrational as soon as Θ < 0 for one M ≥ 40 and one admissible ρ (Lai Lemma 3.1 with d = λ·40, c = −1600Θ).

## 1. Where s enters, and where ν enters (the attribution)

s enters through the functional only.
- (s1) Pullback: μ_X(R(t)) = τ_X(x^s R(−x²)) with τ(P) = L(P^(s−2))/(s−1)!, L(x^k) = B_k, and τ_X(1/(x−r)) = H^(s)_(d(r)) − X. Proof: on t^e both sides are (−1)^e B_(2e+2)(2e+s)!/((s−1)!(2e+2)!) (Xu (1)); on 1/(t+j²) the partial fractions x^s/(j²−x²) = −x^(s−2) − … − j^(s−3)x − (j^(s−1)/2)(1/(x−j) + 1/(x+j)) give −1/(s−1) + j^(s−1)(X − H_j^(s)) + 1/(2j), which is Xu (4). For s = 5 this is Lai Lemma 7.3 (p. 9).
- (s2) **Distribution formula, prefactor p^(−(s−1)).** For a polynomial P, Σ_(a<p) L(P(a+px)) = p·L(P), by the multiplication theorem Σ_a B_k(a/p) = p^(1−k)B_k. Differentiating s − 2 times gives Σ_a τ(P(a+px)) = p^(s−2)·p·τ(P), so τ_X(g) = p^(−(s−1)) Σ_(a=0)^(p−1) τ_Y^ext(g(a+px)) with Y = p^s X + C_p. At s = 5 this is Fauzan Lemma 3.2 (p. 7): p^(−4) and Y = p⁵X + C_p. Equivalently (Zeta5's route): a residue gains 1 and H^(s) loses s (`VG_res`, `VG_H5`), so a class summand loses s − 1 (`tauX_direct`, loss 4 at s = 5).
- (s3) Harmonic values: v_p(H_m^(s)) ≥ −s⌊log_p m⌋, and ≥ −s for m < p². This replaces Fauzan's "−5" in Lemma 3.3 (p. 8) and in (4.12) ("a harmonic value loses at most 5", p. 12).
- (s4) Moments: v_p(μ(t^e)) ≥ −1, and μ(t^e) ∈ Z_p for e < r(p−1) − 1 (von Staudt–Clausen; a pole of B_(2e+2) at k(p−1) = 2e+2 is cancelled by the factor 2e+2+k = kp of (2e+3)…(2e+s) iff k ≤ s−2). Xu (14) at s = 7; Fauzan p. 11 ("e < 2p − 3") at s = 5.

ν enters through the numerator and the normaliser only: the zeros of D_N^ν at the removed poles (6ℓ_N → νℓ_N in (4.2); "W supplies 5δ" → (ν−1)δ in (4.12)), the allocation b_a = (ν/2)ℓ_N(a) and T = ⌊2Hx⌋ ((4.4)), the factor (N!)^(2νh) of S_K, the rank intercept K + (ν−2)N of (4.10), the field V_ν and C*(ν) (Xu (6), (11)).

**Consequence: the attribution of Fauzan's constants** (revised after skeptic, 22:17). The earlier slogan "every 5 is s, every 6 or 3 is ν or ν/2" was false as written, and this table replaces it. In the family ν = s + 1 several of these numbers coincide, so each is assigned by where it comes from, not by its value:

| Fauzan's constant (place) | Value at (5, 6) | General (s, ν) | Source of the constant |
|---|---|---|---|
| distribution prefactor p^−4 (Lemma 3.2, p. 7); inner loss "−4" in (4.2), (4.6) | 4 | s − 1 | (s−2)-fold derivative in τ plus the multiplication theorem (s2) |
| order of the derivative in τ(P) = L(P''')/24 (Lai (49)) | 3 | s − 2 | functional (s1) |
| denominator 24 in τ and in μ(t^e); v_p(24) in (3.10), (3.12) | 24 = 4! | (s − 1)! | functional (s1) |
| zeros x^5 of the pullback (Zeta5 `Bse` "5[a=0]") | 5 | s | functional (s1) |
| "a harmonic value loses at most 5" ((4.12), p. 12); −5⌊log_p K⌋ (Lemma 3.3) | 5 | s | H^(s), (s3) |
| crude factor 6 in (3.10), (3.12), (5.11): residues 1 + harmonic 5 | 6 | s + 1 | (s3) plus residues |
| moment cutoff e < 2p − 3 (p. 11) | 2p − 3 | (s−1)(p−1)/2 − 1 | von Staudt–Clausen (s4) |
| rank slope "−2p" in (4.10) | 2 | (s − 1)/2 | (s4) |
| outer per-pole cost 7 ((4.14), table p. 13) | 7 | s + 2 | harmonic s plus node derivative 2 |
| 6ℓ_N in (4.2); 12h in S_K, (5.3), (5.5); 12λ{αx} in (5.12) | 6, 12 | ν, 2ν | zeros of D_N^ν, (N!)^(2νh) |
| b_a = 3ℓ_N(a) (4.4); 3δ in (4.12); 9 = 3² and 3 in (5.13) | 3, 9 | ν/2, (ν/2)² | half of D_N^ν on each side of the Gram form |
| W = D_N^5 and "W supplies 5δ" ((4.10)-(4.12)) | 5 | ν − 1 | D_N^ν/D_N after cancelling the removed poles |
| 5N ≤ 2p − 2 in (4.9) | 5 | ν − 1 (with 2 = (s−1)/2) | needed for r_p ≤ h |
| rank intercept K + 4N in (4.10) | 4 | ν − 2 | degree of the polynomial quotient |
| H = 1 + 2α = λ + 3α (Lai (8)) | 3 | ν/2 | allocation (4.4) |

Fauzan and Anand both have ν = s + 1, so the two published templates cannot tell these apart. This is the ambiguity the experimenter's theta.py lists as readings 'S' and 'N', and the table decides it for reading 'S'.

## 2. Inner range K/M < p ≤ K/3

**(2.1) Weights.** By (s2) and the class count of (4.2), a class summand has valuation ≥ ν_i(a) + ν_j(a) + νℓ_N(a) − ℓ_K(a) − (s−1). Fauzan's allocation (4.4)-(4.6) with 3 → ν/2 and 4 → s − 1 gives the row weights w_(a,i) = i + (ν/2)ℓ_N(a) − (ℓ_K(a) + s − 1)/2, a > 0. The comparisons in the proof of Prop. 4.1 (p. 11) involve only differences of the "tops" Z_c − (ℓ_K(c)+s−1)/2, in which s cancels, and the zero-source bound, which s only relaxes. So Prop. 4.1 holds for all (s, ν) with γ_p^in = 2Σ w.

**(2.2) Limiting function.** Σ_(i<L) w_(a,i) = (L/2)(L + 2b_a − ℓ_K(a) − s) with L = L_a = T − b_a + ε_a. As in (5.4)-(5.6) (p. 14),

  Γ_(s,ν)(x) = ∫_0^(1/2) (T − b)(T + b − ℓ − s) dz + σ(2T − ⌊2x⌋ − s) + (σ − n₊)₊,  b = (ν/2)ℓ(αx, z),
  N_ν(x) = 2λx⌊x⌋ − 2νλx⌊αx⌋ − 2J(λx),  R_(s,ν) = −Γ_(s,ν) − N_ν,

with T = ⌊2Hx⌋, σ = Hx − T/2, n₊ = {2x}/2, ℓ, J as in Fauzan. At (5, 6) this is (5.4)-(5.6); at (7, 8) it is the audit's `innerGamma`/`innerN`/`innerR`.

**Proposition 1 (PROOF-DRAFT; COMPUTED check C1-C2 in general_sq.py).** For every x ≥ 3,
  R_(s,ν)(x) = x·F(x) + Q_ν(x),  F(x) = (s−1)λ + 2λ{x} − 2νλ{αx},
  Q_ν(x) = [τ(τ − σ') − (τ − σ')₊ + η(1 − η)]/2 + (ν/2)² ∫_0^(1/2) B² dz − (ν/2) ∫_0^(1/2) AB dz,
where τ = {2Hx}, σ' = {2x}, η = {2λx}, A(z) = ℓ(x,z) − 2x, B(z) = ℓ(αx,z) − 2αx (Fauzan (B.1), p. 26, for the two integrals). In particular **R_(s,ν)(x) − R_(s',ν)(x) = (s − s')λx exactly**, and the mean slope is F̄ = (s − 1)λ + λ − νλ = **(s − ν)λ**.

*Proof.* Write T = 2Hx − τ, ℓ = 2x + A, b = (ν/2)(2αx + B), with ∫_0^(1/2) A = ∫_0^(1/2) B = 0 (because ∫_c^(c+1)⌊w⌋dw = c), ∫ ℓ = x, ∫ ℓ(αx,·) = αx. Expanding the integrand (T−b)(T+b−ℓ−s) = T² − b² − (T − b)(ℓ + s) and the two boundary terms (σ = τ/2), the coefficient of x is −2Hτ + τ − sH + (ν/2)sα + (2H − 1)τ = −s(H − (ν/2)α) = −sλ, with no fractional part left; the x² terms 2λ(λ + να − 1) cancel against N_ν; N_ν contributes x(−2λ{x} + 2νλ{αx} + λ) and the constant −η(1−η)/2. Collecting gives F and Q. At (5, 6) this is (5.12)-(5.13), p. 16. ∎

**Corollary (inner s-cost).** For every M ≥ 40: ∫_3^M R_(s+2,ν)x^(−3) dx − ∫_3^M R_(s,ν)x^(−3) dx = 2λ(1/3 − 1/M). The crude range (3.12) costs (s+1)⌊log_p 5K⌋ + v_p((s−1)!) per row (Lemma 3.3: 1 from the residues, s from (s3)), so its PNT contribution (s+1)λ/M grows by 2λ/M. **Together, the primes p ≤ K/3 cost exactly 2λ/3 per step s → s + 2, for every M.** Each unit of s costs one power of p per Hankel row at every such prime: Σ_(p≤K/3) h log p ≈ λK²/3.

## 3. Outer range K/3 < p ≤ K (p > K contributes 0)

Fauzan (4.12) generalises (by (s3) and the ν-attribution of §1) to: in a class with ℓ poles j ≤ K, δ = 1 if it contains a removed pole (j ≤ N), rows i < ℓ − 2 have weight min(0, i + (ν/2)δ − (ℓ + s − 1)/2), rows i ≥ ℓ − 2 weight 0 (the divided-difference argument at the two poles a, p − a < p works for every odd s, since H^(s)_(p−a) ≡ H^(s)_(a−1) mod p; Xu §5). Lemma 4.2 (p. 12) is unchanged; the rank bound (4.10) becomes r_p = max(0, K + (ν−2)N − r(p−1)) by (s4) (Xu (15) at s = 7; at s = 9, ν = 8 it is Xu's note v0.1 §7 "K + 6N − 4p + 4").

Class costs (−2Σw) and zero counts:
- no removed pole: c⁰(ℓ) = (s+2)(ℓ−2) (for ℓ < s + 5, always the case here), two zero weights;
- one removed pole: c¹(ℓ) = Σ_(i=0)^(ℓ−3) max(0, ℓ + s − 1 − ν − 2i), z¹(ℓ) = 1 + #{i ≤ ℓ−3 : ℓ + s − 1 − ν − 2i ≤ 0}.

At (5, 6) these are Fauzan's table on p. 13 (costs 0, 1, 2, 4, 6 and zeros 1, 1, 2, 2, 3 for ℓ = 2..6; unremoved 7(ℓ−2)) (COMPUTED, C3a). Summing over classes with y = p/K, k = ⌊1/y⌋, v = 1 − ky, u = (α + v − y)₊, m_v = min(α, v), the removed classes have densities α − m_v, m_v − u, u at ℓ = 2k, 2k+1, 2k+2, and

  g_(s,ν)(y) = (s+2)[(1 − y) − Σ_ℓ dens(ℓ)(ℓ−2)] + Σ_ℓ dens(ℓ)c¹(ℓ) + min(r̂, ẑ),
  ẑ = y − 2α + Σ_ℓ dens(ℓ)z¹(ℓ),  r̂ = min(λ, (1 + (ν−2)α − ry)₊),

  I_out(s, ν) = ∫_(1/3)^(2λ) [g_(s,ν)(y) − 2λ⌊1/y⌋ + Σ_(j≥1)(2λ − jy)₊] dy.

At (5, 6), g = R_0 − d of (5.8)-(5.9) (p. 15) and I_out = 127751/96000 (5.10); at (7, 8), g is the audit's `outerG` and I_out = 453803/288000 (COMPUTED, C3b, at 200 points and exactly). **The outer per-pole cost s + 2 is the outer counterpart of §2: a pole j > p of an unremoved class costs s (harmonic) + 2 (node derivative), Fauzan's "7".** Off the family ν = s + 1 the removed-class terms are not theta.py's family coefficients ν, ν − 1, 2να, and the zero count changes; the difference in I_out is −0.012 for most (s, ν) and **+0.083 at (5, 8)**, where ν > s + 1 caps the savings at zero (COMPUTED, C5).

**Source note to (5.9), added Sat Nov 14 01:30 PT** (EVENT WORK, advocate:sourcenotes5, Claude Opus 5.5; wording only, the text above is unchanged; it checks a source note of skeptic 5, Kimi K3.1 Pro, `../skeptic5-kimi/REPORT.md` §3). Skeptic 5 reports that Fauzan's printed (5.9) omits the outer positive part of d(y). **The page image does not bear this out.** Fauzan, Zenodo 22826419 v1 (sha256 a42c05cc…0da), p. 15, rendered with `pdftoppm -r 200 -f 15 -l 15`, prints d(y) = (1 + 4α − 3y − (1 + α − 3y)₊)₊ · 1_(1/3,1/2)(y), with the outer clamp (CITED). Lai prints the same in (85), Lemma 10.1, ai.vixra 2609.0080v1 PDF p. 14 (CITED). `pdftotext -layout` puts the big parentheses on the line above and the outer "+" on the line below, so the extracted text reads as unclamped. That is the likely origin of the report (HEURISTIC). The report's numbers are right (COMPUTED, exact, `../sourcenotes5/check_d59.py`): at α = 3/40, ∫_(1/3)^(1/2) d(y) dy = 9/640 with the clamp, which is Fauzan's stated value (p. 15), and 71/9600 without it. The difference is 1/150, the negative part on (13/30, 1/2). Dropping the clamp would make I_out(5, 6) equal 42797/32000 instead of (5.10)'s 127751/96000. Our code clamps: theta.py l. 549-551 integrates max(·, 0), and C3b above reproduces 127751/96000 exactly. **No correction to Fauzan's (5.9) is needed. Only the extracted text loses the clamp.**

## 4. The analytic side (Xu §3, restated; CITED)

Under y = K√t the weight is w_s(K√t) = e^(−2πK√t)·(polynomial of degree s in K√t), so s changes log Δ_K(ζ(s)) by O(K log K) only (Xu §3: "the zeta index s changes only lower-order factors of the weight and does not change this field"). The field V_ν = 2π√t + ∫_0^1 log(t+u²)du − ν∫_0^α log(t+u²)du and C*(ν) = −2λ + 2ναλ(1 − log α) + 3λ² − 2λ² log(2λ) (Xu (6), (11) with 2q = ν) give, for every comparison measure ρ of mass λ with 2U^ρ − V_ν ≤ M_0,
  log[S_K Δ_K(ζ(s))] ≤ U(ν; ρ)K² + O(K log K),  U(ν; ρ) = λM_0 − I(ρ) + C*(ν)   (Xu (12); Lai Prop. 11.7).

**Lemma 2 (dual bound; PROOF-DRAFT, standard).** Let E*(ν) = sup_σ [I(σ) − ∫V_ν dσ] over positive σ of mass λ with finite energy. For every admissible ρ and every σ, I(σ) − ∫V_ν dσ ≤ λM_0 − I(ρ); hence U(ν; ρ) ≥ LB(ν; σ) := I(σ) − ∫V_ν dσ + C*(ν).
*Proof.* I(σ) − ∫V dσ = I(σ − ρ) − I(ρ) + ∫(2U^ρ − V)dσ ≤ −I(ρ) + λM_0, since σ − ρ has mass 0 (Lai Lemma 11.5). ∎
So no comparison measure can beat LB. `dual_bound.py` evaluates LB at the measures theta.py found (monotone cells, 40 digits, outward-widened; COMPUTED): LB(2), LB(4), …, LB(10) = −2.5123, −1.9681, −1.3874 (ν = 6, Fauzan's ρ), −0.7755, −0.1305; the gap to theta.py's U(ν) is 0.009 to 0.07.

**Source note to Lemma 2: the admissibility hypotheses, added Sat Nov 14 01:30 PT** (EVENT WORK, advocate:sourcenotes5, Claude Opus 5.5; wording only, the text above is unchanged; raised by skeptic 5, Kimi K3.1 Pro, `../skeptic5-kimi/REPORT.md` §3-§4). In Lemma 2 and Theorem 3, "admissible" means the hypotheses of Xu's real bound, not only "mass λ and finite energy". The source is Xu, Anchen0823/zeta9-research-notes@eb264a73, `missions/zeta7/research/analytic-foundations.md` §3, the paragraph containing (7)-(8) (CITED):
- (A1) ρ is a positive measure of mass λ, supported in a fixed compact subset of (0, ∞);
- (A2) ρ has finite logarithmic energy I(ρ);
- (A3) 2U^ρ(t) − V_ν(t) ≤ M_0 for all t ≥ 0 (Xu (7));
- (A4) circle regularisation: a local mass estimate making the circle-regularisation error O(√ε) uniformly in the centre (ε = K^(−2)). Xu notes that any fixed finite positive sum of arcsine measures on nondegenerate intervals has this property.

The zero-mass step in the proof applies Lai Lemma 11.5 (ai.vixra 2609.0080v1, p. 16) to ν = σ − ρ (CITED). Lai's hypotheses are: ν is a finite real signed measure with compact support, ν(C) = 0, and finite logarithmic energy. Fauzan Lemma 6.2 (Zenodo 22826419, p. 18) states the same lemma with the energy hypothesis in absolute form, ∬|log|z − w|| d|ν|(z) d|ν|(w) < ∞, chosen, Fauzan says, to cover circle and arcsine measures (CITED). So the trial measure σ of Lemma 2 also needs compact support, and σ − ρ needs finite absolute logarithmic energy. The text above only says "finite energy". Nothing is re-proved here.

*Observation (COMPUTED, exact, `../sourcenotes5/endpoints.py`).* The ν = 6 measure in `../margin/out/U_cache.json` is Fauzan's Table 1 measure. Its smallest left endpoint is 7174131/10^11 > 0, so (A1) holds literally. The opt36 measures for ν ∈ {2, 4, 5, 7, 8, 9, 10} have components on [0, b], so their support contains t = 0, the excluded endpoint of Xu's (0, ∞). This leaves Lemma 2 and the s = 7 negative untouched: they use these measures only as trial σ, which needs compact support in C, not (A1). It does matter for every upper bracket A* + U_theta at ν ≠ 6, which uses such a ρ in the real bound (12). One example is "ν = 4 also closes" at s = 5 (§6). Whether Xu's (8) extends to support touching t = 0 is not checked here (open).

## 5. The margin as an explicit function, and the criterion

Combining §2-§4 (Fauzan (5.11), (5.20)-(5.21) with s and ν separated):

  **Θ(s, ν, α; M, ρ) = U(ν, α; ρ) + I_out(s, ν, α) + (s+1)λ/M + ∫_3^M x^(−2)[(s−1)λ + 2λ{x} − 2νλ{αx}] dx + ∫_3^M Q_ν(x)x^(−3) dx.**

s appears in exactly three places: (s+1)λ/M, the slope (s−1)λ of the inner integrand, and I_out through (s+2) and r = (s−1)/2. U never depends on s.

**Theorem 3 (the criterion; PROOF-DRAFT given §1-§4).** Fix odd s ≥ 3, even ν ≥ 2 and α ∈ (0, 1/3) with λ = 1 − α, and the degree side conditions of Prop. 4.1 (true for K large). *Revised after skeptic, 22:17:* the allocation must satisfy L_a ≥ 0 at every inner prime, which holds near x = 3 only for ν ≤ 10 at α = 3/40 (skeptic2), so the theorem is stated for even ν ≤ 10. The earlier hypothesis (ν−1)α < (s−1)/6 (Fauzan's (4.9), read as (ν−1)N ≤ r(p−1)) only guarantees r_p ≤ h. All computed rows use the clamped rank r̂ = min(λ, ·), which is valid without it (rank ≤ h always). The rows (5, 10) and (3, ν ≥ 6) violate the old hypothesis and rely on the clamp. Let Θ*(s, ν, α) := A*(s, ν, α) + U*(ν, α) with A* = I_out + ∫_3^∞ R_(s,ν)x^(−3)dx, and **define** U*(ν, α) := inf over admissible comparison measures ρ of U(ν, α; ρ), which is ≥ E* + C* by Lemma 2.
- (i) If Θ*(s, ν, α) < 0, the package proves ζ(s) irrational: there are an M and an admissible ρ with Θ(s, ν, α; M, ρ) < 0, because A_M → A* as M → ∞ and, by the definition of U* as an infimum, some ρ has U(ρ) < U* + ε. *Revised after skeptic, 22:17:* with this definition the "iff" is a tautology about the package and needs no potential theory. That U* equals E* + C* (arcsine sums approach the equilibrium energy) is HEURISTIC, standard potential theory, not proved here. It matters only for evaluating U*, not for the iff.
- (ii) If A*(s, ν, α) + LB(ν; σ) > 0 for one trial σ, then Θ(s, ν, α; M, ρ) > 0 for every admissible ρ and every M with A_M ≥ A* (here A_M − A* = (ν+1)λ/M + O(M^(−2)), positive for every M in the computed rows). In words: **"works iff A*(s,ν,α) + U*(ν,α) < 0", where only the denominator exponent A* depends on s.**
"Fails" in (ii) is scoped to this package: the local valuation bounds are not sharp, and a different normaliser (for instance the primitive content) is outside it.

**Corollary 4 (the s-step; PROOF-DRAFT, exact values COMPUTED).** For fixed (ν, α) and every M ≥ 40 and ρ,
  Θ(s+2, ν; M, ρ) − Θ(s, ν; M, ρ) = 2λ/3 + I_out(s+2, ν) − I_out(s, ν),
independent of M and of ρ. At α = 3/40 (sstep_exact.out): ν = 6, s = 5 → 7: **751/768 ≈ 0.9779**; ν = 8, 5 → 7: 12817/14400 ≈ 0.8901; ν = 2: 9929/9600 ≈ 1.0343; ν = 4: 4867/4800 ≈ 1.0140. *Revised after skeptic, 22:17:* the range is 7 → 9: 0.9405 (ν = 10) to 1.0611 (ν = 2); 3 → 5: 0.663 to 0.906 (0.737, 0.663, 0.668 at ν = 6, 8, 10); and 0.663 to 1.061 over all 15 computed steps. The step depends on α: 5 → 7 runs from 1.07 (α = 1/40, ν = 2) down to 0.69 (α = 6/40, ν = 8), exact, and to 0.54 at α = 3/20, ν = 10 (float) (skeptic2, `../skeptic2-criterion5/alpha_scan.out`, `alpha_sstep.out`).

## 6. What changes sign between s = 5 and s = 7

- **At fixed ν (U cancels):** the inner prime-sum term ∫_3^∞ R_(s,ν)x^(−3)dx is −0.0173 at (5, 6) and +0.5994 at (7, 6) (theta.py's exact-to-200 integrator; COMPUTED). Its sign follows the mean slope F̄ = (s − ν)λ: −λ at (5, 6), +λ at (7, 6). The reason is (s2)-(s3): the pole values j^(s−1)(X − H_j^(s)) carry p^(−s), Fauzan's "−4" is 1 − s, and every step s → s+2 costs p^(2h) at every inner prime. The outer term grows too (ΔI_out = +0.3612 at ν = 6: (s+2) per pole above p, partly offset by the moment rank r = (s−1)/2).
- **Along the published templates (5, 6) → (7, 8):** Θ goes from [−0.074, −0.058] to [+0.906, +0.948] (M → ∞; brackets [A* + LB, A* + U_theta]). Split: the s-step at ν = 8 is +0.8901 (U-free, exact); the ν-step at s = 5 is A*(5,8) − A*(5,6) + U(8) − U(6) ≈ −0.522 + 0.637 = +0.116. **So about 88% of the change from Fauzan's to Anand's template is the s-dependence of the denominators, not the numerator power.**
- **Over ν (α = 3/40, even ν ≤ 10):** the best margin is ≤ −0.058 at s = 5 (ν = 6; ν = 4 also closes, [−0.053, −0.044]), ≥ +0.904 at s = 7, ≥ +1.92 at s = 9, and ≤ −0.80 at s = 3 (COMPUTED, sstep_exact.out). **What is special about 5: it is the largest odd s at which the package closes, and it closes with about 6% of one s-step (0.058 of 0.98) to spare.**

## 7. What this does not show (HEURISTIC or open)

- **Scope** (revised after skeptic, 22:17). Every margin statement, including "only s = 5 closes", is for α = 3/40, λ = 1 − α, even ν ≤ 10 and Fauzan's bound package. Odd ν is not admissible. Beyond ν = 10, L_a ≥ 0 fails near x = 3, so ν > 10 needs a new allocation. U(ν, α) has not been computed off α = 3/40: the U-free s-step has been scanned in α by skeptic2 (0.54-1.07), the margin has not.
- Theorem 3(i)'s approximation of E* by arcsine sums is not proved here; (ii) needs only one trial σ and is what the s = 7 claim uses.
- The A* values use theta.py's float64 periodic tail beyond x = 200 (exact pieces, error about 1e−9); LB uses 40-digit function values with 1e−30 widening (not mpmath.iv: `iv.atan` is missing).
- The derivation generalises Fauzan's proofs line by line; it has not been formalised, and no human has checked it.

## 8. Correction, Sat Nov 14 12:04 PT: two hypotheses that §0, §3 and Theorem 3 omit

*EVENT WORK, integrator (Claude Fable 5.2, Claude Code on `[team machine]`, for [team member]). The text above is unchanged. Source of the correction: lane A's audit E100 (Codex, GPT family, for [team member]), `../A-foundation-audit/PROOF_AUDIT.md` §4-§5, a PROOF-DRAFT that no human has checked. The integrator re-ran a copy of its checker `check_foundation.py` (standard library only, no producer code): the output is identical to the stored `out/foundation_checks.json`.*

**What stands.** For odd s ≥ 5 at α = 3/40 and even ν ≤ 10, both hypotheses below hold, so §1-§6 are unchanged there: no number at s = 5, 7, 9 changes (PROOF-DRAFT, E100 §1: a scoped pass).

**(H1) The outer class model needs α < 1/6** (PROOF-DRAFT, E100 §4). Fauzan's (4.9) (p. 11) assumes 2N < p, and (4.11)-(4.12) use at most one removed pole per ordinary class. For every prime p > K/3 this requires α = N/K < 1/6. Theorem 3 says α ∈ (0, 1/3), which is too wide. α = 3/40 satisfies it.

**(H2) "p > K contributes 0" needs a rank condition** (PROOF-DRAFT, E100 §5). For p > K the pole-part basis is integral, but the polynomial (moment) correction has rank at most ρ_p = max(0, K + (ν−2)N − r(p−1)), with r = (s−1)/2. The argument of §3 gives an integral determinant only when ρ_p = 0 for every p > K. A sufficient condition is

  a := 1 + (ν−2)α ≤ r.

At α = 3/40 and even ν ≤ 10, a ≤ 8/5, so every odd s ≥ 5 (r ≥ 2) is covered. **At s = 3 (r = 1) and ν ≥ 4, a = 23/20, 13/10, 29/20, 8/5 > 1, and §3 as written does not cover the primes K < p < aK.** Fauzan's Proposition 4.3 (p. 13) makes the same correction vanish in his case by K + 4N + 1 < 2p.

**A witness that the unrestricted statement is false** (COMPUTED, E100; re-run by the integrator). At K = 40, N = 3, p = 41, X = 0: v_41(Δ_K(0)) = −6, −12, −18, −24 for s = 3 and ν = 4, 6, 8, 10, and 0 for (s, ν) = (5, 10) and (7, 6). These K are below Fauzan's K ≥ 200M², so they are not asymptotic counterexamples; they show that the local statement "p > K gives an integral determinant" is false without (H2).

**A sufficient repair at s = 3** (PROOF-DRAFT, E100 §5; not shown sharp). Keep the correction: all pole-part weights are 0, so Lemma 4.2 bounds the cost by min(h, ρ_p), and the extra leading cost is ∫_1^(2λ) min(λ, (a − ry)₊) dy, which is (a − 1)²/2 at r = 1 on this slice: 0, 9/800, 9/200, 81/800, 9/50 for ν = 2, 4, 6, 8, 10. Adding it to the upper ends of the s = 3 rows of `../criterion_map/TABLE.md` gives −0.8576467, −0.8814511, −0.7642658, −0.5317068, −0.2361026 (COMPUTED by the integrator: decimal addition to the certified upper ends). All stay negative, so "the package closes at s = 3 for every even ν ≤ 10" survives, relative to this repair.

**What changes in our claims.**
- Theorem 3 is to be read with (H1) and (H2) added to its hypotheses.
- The s = 3 values of I_out at ν ≥ 4, and with them the 3 → 5 steps of Corollary 4 at ν ≥ 4 (the lower end 0.663 of its range), are not established by §3. With the repair, each such step is smaller by (a − 1)²/2.
- §6's "≤ −0.80 at s = 3" becomes "≤ −0.88 at s = 3 (ν = 4, with the repair)"; the ν = 2 value −0.8576 needs no repair.
- Nothing changes in "what is special about 5", in the 5 → 7 step, or in any ζ(7) or ζ(9) statement.
