# Proposition 1 (E44): the lower half of the log-gas asymptotics for the single-value template (PROOF-DRAFT)

EVENT WORK, Sat Nov 14 2026, 08:53-09:25 ET (05:53-06:25 PT), `e26_proof/prop1` (Claude Opus 5.5, subagent of the #108 workflow).
No human has checked this file. Labels follow AGENTS.md §2; each claim carries exactly one. Computations: `check.py`
(one process, about 5 s), output `check.out`, checks C1-C8. The file starts from the flsz-analytic proposer's sketch
(`../../zeta7_levers/panel_verdicts.json`, slug flsz-analytic, field "mechanism" (b)) and from its two verdicts.

## 0. Result

- **Proposition 1 (PROOF-DRAFT, §2-§4).** Let σ be a positive measure of mass λ with compact support in **[0, ∞)** (a
  hard edge at t = 0 is allowed) and a Hölder-1/2 local mass bound; every finite positive sum of arcsine measures
  qualifies. Then, for every K ∈ 40Z>0, every odd s ≥ 3 and every integer ν ≥ 1,
  `log[S_K Δ_K(ζ(s))] ≥ LB(ν; σ) K² − E_σ(K)`. The error E_σ(K) is explicit, (2.2), and E_σ(K) = (ν+5)λ K log K + O_σ(K).
  Hence `liminf K^-2 log[S_K Δ_K(ζ(s))] ≥ LB(ν; σ) = I(σ) − ∫V_ν dσ + C*(ν)`.
- **Success test, met (§5).** The only K²-order inequality in the proof is the quantile energy bound, Lemma Q (§3).
  Every other step is an identity, or a two-sided per-point estimate with O(log K) slack per point, or Stirling with
  O(log K) slack in total. The K² constant is LB(ν; σ), and its C*(ν) is exactly Xu's (11) with 2q = ν (Fauzan (6.3) at
  ν = 6).
- **Hard edge (§4).** The proof never uses min supp σ > 0, so it covers the ν = 2 trial measure opt36, whose 25
  components all start at t = 0 (C3, exact). This closes the scope gap that both verdicts found.
- **Corollary 2 (PROOF-DRAFT, numbers from E33(b), COMPUTED, certified).** No analytic estimate of any kind can push the
  real exponent of F_K(ζ(7)) below LB(6) ≥ −1.3871640488. The room over the package's U_θ(6) is therefore at most
  **0.015642459** per K² (exact, C6). The 7-decimal figure "0.0156424" rounds the wrong way: the certified ceiling is
  ≤ 0.0156425. At ν = 2 the ceiling is ≤ 0.0434920.
- **Corollary 3 (PROOF-DRAFT): the analytic half of E26.** e_K ≥ a_K + LB(ν; σ) − E_σ(K)/K² for every K. So at (7, 6),
  **liminf a_K > 1.3871641 implies that the template cannot certify ζ(7), with any arithmetic and any analytic
  estimate.** That hypothesis on a_K stays CONJECTURE (a_K = 1.931, 2.104, 2.149 at K = 40, 80, 120, E25).
- **Remark 3 (PROOF-DRAFT; COMPUTED check).** A second, shorter proof uses Jensen's inequality with the product trial
  measure. It gives a better error, (ν + 1 − s)λ K log K + O(K), which is 0·K log K at (7, 6). It is consistent with
  every exact u_K in the pod (C7).

## 1. Objects (exact definitions)

s ≥ 3 odd. ν ≥ 1 an integer (the template uses even ν; positivity below needs no parity). K ∈ 40Z>0, N = 3K/40,
h = K − N = 37K/40, α = N/K = 3/40, λ = h/K = 37/40. D_m(t) = ∏_{j=1}^m (t + j²). For y > 0,
`w_s(y) = [2(2π)^(s−1)/(s−1)!] y^s Σ_{ℓ≥1} ℓ^(s−1) e^(−2πℓy)`.
G_K(X)_ij = μ_X(D_N(t)^ν t^(i+j)/D_K(t)) for 0 ≤ i, j < h, Δ_K = det G_K ∈ Q[X],
S_K = (K!)^(2h) 4^(h−1) / ((N!)^(2νh) ∏_{i=1}^{h−1} ((2i)!)²), F_K = S_K Δ_K. These are the pod's definitions
(`../../witness/README.md` "Objects", `../../witness/hankel.py`); at ν = 6 S_K is Fauzan (2.5) and G_K, Δ_K are
Fauzan (2.4) (Zenodo 22826419, p. 4, page image checked) [CITED].

For τ ≥ 0 and 0 < a ≤ 1: J_a(τ) = ∫_0^a log(τ + u²) du, so J_a(0) = 2a log a − 2a and
J_a(τ) = a log(τ + a²) − 2a + 2√τ arctan(a/√τ) for τ > 0 (Xu l. 111).
- V_ν(τ) = 2π√τ + J_1(τ) − ν J_α(τ). This is Xu (6) (l. 104-108) with 2q = ν, and Fauzan (6.1), p. 17, at ν = 6 [CITED].
- C*(ν) = −2λ + 2ναλ(1 − log α) + 3λ² − 2λ² log(2λ). This is Xu (11) (l. 156-158) with 2q = ν, and Fauzan (6.3), p. 17
  (page image checked), at ν = 6 [CITED]. Values: C*(6) = 2.65303599034049, C*(2) = 0.660437713518 (C1) [COMPUTED].
- I(σ) = ∬ log|t − u| dσ(t) dσ(u). LB(ν; σ) = I(σ) − ∫V_ν dσ + C*(ν): `../../criterion5/derivation.md` Lemma 2 and
  E33(b) (`../../certify/README.md` §3.4). κ_s = log((2π)^(s−1)/(s−1)!). c_V = π·max(3, ν − 2).
- u_K = K^-2 log F_K(ζ(s)), a_K = −K^-2 log content(F_K), e_K = a_K + u_K = K^-2 log Q^prim_K(ζ(s)).

**Hypothesis (H) on σ.** σ is a positive Borel measure on R with σ(R) = λ and supp σ ⊂ [b_−, b_+] ⊂ [0, ∞), where
b_± are its extreme support points and L_σ = b_+ − b_−. There is C_σ < ∞ with σ(I) ≤ C_σ |I|^(1/2) for every
interval I. (H) forbids atoms. U^σ is bounded on supp σ (layer-cake as in Lemma Q(a)(iv)), so I(σ) is finite.

**Lemma 0 (arcsine sums satisfy (H)) [PROOF-DRAFT].** Let ω_[a,b] be the arcsine probability measure on
[a, b], with density 1/(π√((t−a)(b−t))). Then ω_[a,b](I) ≤ (4/π)(|I|/(b−a))^(1/2) for every interval I. Hence
σ = Σ_k c_k ω_[a_k,b_k] with c_k > 0, Σc_k = λ and 0 ≤ a_k < b_k satisfies (H) with C_σ = (4/π) Σ_k c_k (b_k − a_k)^(−1/2).
*Proof*: on [a, m], with m the midpoint, b − t ≥ L/2, so the density is at most
(1/π)(2/L)^(1/2)(t − a)^(−1/2), and symmetrically on [m, b]. A decreasing integrand integrates to at most 2√ℓ over a
set of length ℓ. So ω(I) ≤ (2/π)(2/L)^(1/2)(√ℓ_1 + √ℓ_2) ≤ (4/π)(|I|/L)^(1/2), since √ℓ_1 + √ℓ_2 ≤ (2(ℓ_1+ℓ_2))^(1/2). ∎ The same bound is Fauzan's "at most 4√(2r)/(π√L)" for an
interval of radius r (Zenodo 22826419, p. 19, first line, page image checked) [CITED].

[COMPUTED, C3, exact fractions] Both stored trial measures satisfy (H). The ν = 6 measure fauzan16 has 16
components, c_k > 0, Σc_k = 37/40, a_min = 7.174·10^-5, b_+ = 0.746637, C_σ = 3.332118, L_σ = 0.746566. The ν = 2
measure opt36 has 25 components, c_k > 0, Σc_k = 37/40, **every a_k = 0**, b_+ = 0.577080, C_σ = 5.616569,
L_σ = 0.577080.

## 2. Statement

**Proposition 1 (PROOF-DRAFT).** Let s ≥ 3 be odd, ν ≥ 1, K ∈ 40Z>0, and let σ satisfy (H). Then F_K(ζ(s)) > 0 and

    log[S_K Δ_K(ζ(s))] ≥ LB(ν; σ) K² − E_σ(K),                                                   (2.1)

    E_σ(K) = −R_S(K) + 2 log(h!) + 2h log K + (2h − 1) log⁺ L_σ + (h − 1)(2 log(K C_σ) + 2 + log 2)
             + c_V (K(√b_+ − √b_−) + √2 h) + h (log(2πK) + 1/(6K) − κ_s),                          (2.2)

    R_S(K) = h log(2πK) − νh log(2πN) − νh/(6N) − (h−1) log π − log((h−1)!) + 2h log(2h) − 2h
             − (1 + log(h−1))/12 − 1 − (1/2) log h.                                                (2.3)

E_σ(K) = (ν+5)λ K log K + O_σ(K): −R_S contributes (ν−2)h log K, 2 log h! contributes 2h log K, the explicit term
2h log K, the self-energies 2(h−1) log K, and the last term h log K. So liminf_K K^-2 log[S_K Δ_K(ζ(s))] ≥ LB(ν; σ).
s enters (2.2) only through −hκ_s, an O(K) term.

[COMPUTED, C5] At (7, 6) with fauzan16: E(40) = 2403.9, E(80) = 5364.8, E(120) = 8538.9 (14.9 K log K at K = 120).
E(K)/K² ≤ 0.0156424 from K ≈ 7240 on. The bound (2.1) lies below every exact u_K in the pod: (7,6), (5,6), (7,2), (5,2),
K = 40 to 160. It is far from sharp at those K (Remark 3 is much sharper).

## 3. Proof

**Step A (identities).**
- (A1) [CITED] At X = ζ(s), μ_ζ(s)(R) = ∫_0^∞ R(y²) w_s(y) dy for every rational R with only simple poles at −j²
  (Xu §1, (1)-(4) and l. 48; for s = 5 Fauzan Prop. 2.2, (2.10), p. 5, page image checked). G_K(ζ(s)) is then
  positive definite and Δ_K(ζ(s)) > 0 (Xu §2, l. 59-66). Substituting t = y² gives
  G_K(ζ(s))_ij = ∫_0^∞ t^(i+j) ω(t) dt, with ω(t) = [D_N(t)^ν/D_K(t)] w_s(√t)/(2√t) > 0 [PROOF-DRAFT].
- (A2) [CITED] Andréief/Heine: Δ_K(ζ(s)) = (1/h!) ∫_(0,∞)^h ∏_{i<j}(t_j − t_i)² ∏_i ω(t_i) dt_i. Sources:
  Forrester, arXiv:1806.10411, (1.7), p. 2; Lai, ai.vixra 2609.0080v1, Lemma 11.6, (97)-(98), p. 16 (page image
  checked); Fauzan (6.10), p. 19 (page image checked).
- (A3) [PROOF-DRAFT] Put t = K²τ. D_N(K²τ) = K^(2N) ∏_{j≤N}(τ + (j/K)²) and D_K(K²τ) = K^(2K) ∏_{j≤K}(τ + (j/K)²).
  The Vandermonde gives K^(2h(h−1)) and the Jacobian K^(2h). Hence

      log Δ_K(ζ(s)) = 2h(h + νN − K) log K − log h! + log Z_K,
      Z_K = ∫_(0,∞)^h ∏_{i<j}(τ_j − τ_i)² ∏_i ω̃_K(τ_i) dτ_i,                                           (3.1)
      ω̃_K(τ) = [∏_{j≤N}(τ + (j/K)²)^ν / ∏_{j≤K}(τ + (j/K)²)] · w_s(K√τ)/(2K√τ).

  Here 2h(h + νN − K) = 2λ(λ + να − 1)K² exactly, which is Xu's K² log K coefficient (l. 140, 144) with 2q = ν.

**Step B (restriction to an ordered box at the quantiles of σ; part of the quantile bound).** [PROOF-DRAFT]
F_σ(t) = σ((−∞, t]) is continuous. Put b_0 = b_− and, for 1 ≤ k ≤ h, b_k = min{t : F_σ(t) = k/K}. Then b_h = b_+,
b_0 < b_1 < ... < b_h (F_σ(b_k) = k/K and F_σ(b_0) = 0), and each cell A_k = [b_{k−1}, b_k] has σ(A_k) = 1/K. Put x_i = b_i for 0 ≤ i ≤ h−1 and
δ = K^-2, and let

    R = {τ = x + u : δ ≤ u_0 ≤ u_1 ≤ ... ≤ u_{h−1} ≤ 2δ},   vol(R) = δ^h/h!.

On R, for i < j, τ_j − τ_i = (x_j − x_i) + (u_j − u_i) ≥ x_j − x_i > 0, and τ_i ≥ δ = K^-2. The integrand of Z_K is
≥ 0 on (0, ∞)^h and R ⊂ (0, ∞)^h. Hence

    log Z_K ≥ h log δ − log h! + 2 Σ_{i<j} log(x_j − x_i) + inf_{τ∈R} Σ_i log ω̃_K(τ_i).            (3.2)

The ordered perturbation replaces the gap condition ("gaps ≥ cK^-2") of the proposer's independent boxes. No lower
bound on the spacing of the quantiles is needed.

**Step C (per-point bounds, two-sided to O(log K) per point).** For every τ ≥ K^-2:

    log ω̃_K(τ) ≥ −K V_ν(τ) − log(2πK) − 1/(6K) + κ_s.                                            (3.3)

- (C1) [PROOF-DRAFT] Σ_{j≤N} log(τ + (j/K)²) ≥ K J_α(τ). The sum is a right-endpoint Riemann sum of the
  nondecreasing u ↦ log(τ + u²).
- (C2) [PROOF-DRAFT] Σ_{j≤K} log(τ + (j/K)²) ≤ K J_1(τ) + log(2πK) + 1/(6K). The difference d(τ) is continuous on
  [0, ∞). Its derivative Σ_j (τ + (j/K)²)^-1 − K∫_0^1 (τ + u²)^-1 du is ≤ 0 (a right-endpoint sum of a nonincreasing
  function; Xu l. 136, Fauzan p. 20). So d(τ) ≤ d(0) = 2(log K! − K log K + K) ≤ log(2πK) + 1/(6K), by Stirling,
  log m! ≤ m log m − m + (1/2) log(2πm) + 1/(12m) (DLMF 5.6.1, not re-opened here) [CITED]. This is Xu (9) (l. 129-133)
  and Fauzan (6.12) (p. 20, page image checked), whose constants are 2 log K + O(1) and 2 log K + 2. The upper half
  is used for D_K and the lower half for D_N^ν. Xu's upper bound uses them the other way round (both verdicts).
  [COMPUTED, C2: 0 ≤ d ≤ log(2πK) + 1/(6K) on a grid of τ, m and K = 40, 80, 120; equality at τ = 0, m = K.]
- (C3) [PROOF-DRAFT] Every term of w_s is positive. Keeping ℓ = 1 (Fauzan's device in (C.2), p. 29, page image
  checked) gives w_s(y)/(2y) ≥ [(2π)^(s−1)/(s−1)!] y^(s−1) e^(−2πy). For y = K√τ ≥ 1 this is ≥ e^(κ_s − 2πK√τ).
  The dropped factors y^(s−1) ≥ 1 and Σ_{ℓ≥2} lose O(log K) per point.

Adding ν·(C1), −(C2) and (C3) gives (3.3), because K[νJ_α − J_1] − 2πK√τ = −K V_ν(τ).

**Step D (Lemma Q, the quantile energy bound: the only K²-order inequality).** Let σ satisfy (H), with b_k, x_i, A_k
as in Step B.
- (a) 2 Σ_{0≤i<j≤h−1} log(x_j − x_i) ≥ K² I(σ) − (2h−1) log⁺ L_σ − (h−1)(2 log(K C_σ) + 2 + log 2).
- (b) For any τ_i ∈ [x_i + δ, x_i + 2δ]: K Σ_i V_ν(τ_i) ≤ K² ∫V_ν dσ + c_V K(√b_+ − √b_− + h√(2δ)).

*Proof of (a)* [PROOF-DRAFT]. Write E_kj = K² ∫_{A_k}∫_{A_j} log|t − u| dσ dσ. The integrand is integrable by (H), so
K² I(σ) = Σ_{k,j=1}^h E_kj.
- (i) Fix i < j. For t ∈ A_{i+1} and u ∈ A_j (note i + 1 ≤ j), both t and u lie in [b_i, b_j]. So
  |t − u| ≤ b_j − b_i = x_j − x_i, and since K² σ(A_{i+1}) σ(A_j) = 1, log(x_j − x_i) ≥ E_{i+1, j}.
- (ii) Summing over 0 ≤ i < j ≤ h−1 (k = i+1 runs over 1 ≤ k ≤ j ≤ h−1):
  2 Σ_{i<j} log(x_j − x_i) ≥ Σ_{k,j ≤ h−1} E_kj + Σ_{k ≤ h−1} E_kk.
- (iii) Σ_{k,j≤h−1} E_kj = K² I(σ) − 2Σ_{k<h} E_kh − E_hh ≥ K² I(σ) − (2h − 1) log⁺ L_σ, since log|t − u| ≤ log L_σ on
  the support and K² σ(A_k) σ(A_h) = 1.
- (iv) Self-energies. ρ_k = K σ|_{A_k} is a probability measure. For t ∈ A_k, ρ_k({u : |u − t| < r}) ≤
  min(1, β√r) with β = √2 K C_σ, and every u ∈ A_k has |u − t| ≤ ℓ_k = |A_k|. The layer-cake formula gives
  ∫ log|u − t| dρ_k(u) = log ℓ_k − ∫_0^{ℓ_k} ρ_k(|u − t| < r) dr/r. Since ρ_k(A_k) = 1 ≤ β√ℓ_k, we have
  ℓ_k ≥ r_0 = β^-2, and ∫_0^{ℓ_k} min(1, β√r) dr/r = 2 + log(ℓ_k/r_0). So ∫ log|u − t| dρ_k(u) ≥ −2 log β − 2, and
  E_kk = ∬ log|t − u| dρ_k dρ_k ≥ −2 log(K C_σ) − log 2 − 2.

Combining (ii)-(iv) gives (a). ∎

*Proof of (b)* [PROOF-DRAFT]. **Lemma V.** For τ, τ' ≥ 0, |V_ν(τ) − V_ν(τ')| ≤ c_V |√τ − √τ'|. Proof: V_ν is
continuous on [0, ∞). For τ > 0, V_ν' = π/√τ + J_1' − νJ_α', with 0 ≤ J_a'(τ) = arctan(a/√τ)/√τ ≤ π/(2√τ). So
(2 − ν)π/(2√τ) ≤ V_ν' ≤ 3π/(2√τ), hence |V_ν'| ≤ c_V/(2√τ); integrate. ∎ Now V_ν(τ_i) and the average
K∫_{A_{i+1}} V_ν dσ are both values, or averages of values, of V_ν on [b_i, max(b_{i+1}, b_i + 2δ)]. By Lemma V they
differ by at most c_V(√b_{i+1} − √b_i + √(2δ)). Summing over i telescopes to c_V(√b_+ − √b_− + h√(2δ)), and
Σ_i K∫_{A_{i+1}} V_ν dσ = K ∫V_ν dσ. ∎

[COMPUTED, C4, float64] At K = 40, 120, 400, 1200 and 4000, for both stored measures: (a) holds with large room. The
actual D_K = 2Σ log(x_j − x_i) − K²I(σ) is ≈ +1.0·K log K, while the bound is ≈ −3.0 (K = 40) to −2.4 (K = 4000)
times K log K. (b) holds; the actual field excess is negative.

**Step E (S_K by Stirling: the constant C*).** [PROOF-DRAFT; the Stirling inequality is CITED, DLMF 5.6.1, not
re-opened here] Use log m! = m log m − m + (1/2) log(2πm) + θ_m/(12m) with 0 < θ_m < 1 in 2h log K! (θ ≥ 0),
−2νh log N! (θ ≤ 1) and −2Σ_{i<h} log((2i)!) (θ ≤ 1). For φ(x) = 2x log(2x) − 2x (convex, φ(0) = 0, φ'' = 2/x),
the trapezoid errors are e_0 = φ(1)/2 − ∫_0^1 φ = 1/2 and, for i ≥ 1, e_i ≤ (1/8)(φ'(i+1) − φ'(i)) (Peano kernel
(x−i)(i+1−x)/2 ≤ 1/8). So Σ_{i=1}^{h−1} φ(i) ≤ ∫_0^h φ + 1/2 + (1/4) log h − φ(h)/2, with 2∫_0^h φ = 2h² log(2h) − 3h².
With N = αK and h = λK, the main parts combine exactly:

    2h(K log K − K) − 2νh(N log N − N) − (2h² log(2h) − 3h²) = −2h(h + νN − K) log K + C*(ν) K²,

and every remainder is collected in R_S(K), (2.3). Thus

    log S_K ≥ −2h(h + νN − K) log K + C*(ν) K² + R_S(K).                                           (3.4)

The K² constant is exactly Xu's C*(q, α) of (11) with 2q = ν. At ν = 6 Fauzan's (6.15), p. 20 (page image checked),
is the upper-bound version with the same C*. [COMPUTED, C1, mpmath at 60 digits] log S_K − main ≥ R_S(K) holds at
K = 40 to 4000 for ν = 6 and 2, with slack 0.8 to 1.6. (log S_K − main)/(K log K) moves toward (2 − ν)λ (−3.085 at
K = 4000 for ν = 6, against −3.7 in the limit, because of the O(K) term).

**Step F (assembly).** [PROOF-DRAFT] By (3.1), (3.2), (3.3) on R, Lemma Q and (3.4), with δ = K^-2:
log[S_K Δ_K(ζ(s))] ≥ [−2h(h+νN−K) log K + C*K² + R_S] + 2h(h+νN−K) log K − log h! − 2h log K − log h!
+ K²I(σ) − (2h−1) log⁺ L_σ − (h−1)(2 log(KC_σ) + 2 + log 2) − K²∫V_ν dσ − c_V(K(√b_+ − √b_−) + √2 h)
− h(log(2πK) + 1/(6K) − κ_s) = LB(ν; σ)K² − E_σ(K). The K² log K terms cancel identically. ∎

## 4. The hard edge at t = 0 (ν = 2)

[PROOF-DRAFT] Only four places in §3 could depend on where supp σ starts, and none needs b_− > 0:
- Step B: τ_i ≥ x_i + δ ≥ K^-2 > 0 for every b_− ≥ 0, so R ⊂ (0, ∞)^h.
- Step C: (C1)-(C2) hold uniformly on τ ≥ 0, and τ = 0 is the worst case of (C2). (C3) needs y = K√τ ≥ 1, which R
  guarantees. Under the literal "(0, ∞)" sketch the ℓ = 1 bound would cost ((s−1)/2) log τ_i, which is unbounded at a
  hard edge. On R it costs nothing.
- Lemma Q(a) uses only (H). Arcsine components on [0, b] satisfy (H) with the same constant (Lemma 0 is
  translation-invariant).
- Lemma Q(b) uses Lemma V, which holds down to τ = 0 (V_ν(0) = J_1(0) − νJ_α(0) is finite, with a √τ modulus).

So Proposition 1 holds as stated for supp σ ∋ 0. It applies to opt36 at ν = 2 (C3: all 25 a_k = 0).
[COMPUTED, C8, float64] For the weakly nested opt36, I(σ) recomputed from the closed-form arcsine potentials, without
the nested-energy formula (Lai (91)), is −2.5361445499 (M = 20000). This agrees with the stored −2.5361445586 to
9·10^-9 (fauzan16: 8·10^-10). The E36 caveat (Lai Lemma 11.3 is stated for strict nesting) therefore does not affect
the value numerically. E33's certified LB(2) still rests on E33's own interval computation.

## 5. Success test

| Step | content | type | slack against the quantity it bounds |
|---|---|---|---|
| A1-A3 | Gram representation, Andréief, scaling | identities | 0; gives the K² log K term exactly |
| C1, C2 | Riemann sums for D_N^ν (lower half) and D_K (upper half) | per point, two-sided | ≤ ν(log 2πN + 1/6) and ≤ log 2πK + 1/6 per point: O(K log K) |
| C3 | weight, ℓ = 1 term, y^(s−1) ≥ 1 on R | per point | O(log K) per point |
| E | Stirling for S_K | global, two-sided | O(log K) in total (C1: 0.8 to 1.6); gives C*(ν) exactly |
| **B + D** | **restriction to the box at σ's quantiles; Lemma Q (energy and field)** | **the only K²-order inequality** | its K² constant is I(σ) − ∫V_ν dσ; against the true value it loses K²[E*(ν) − I(σ) + ∫V_ν dσ] (HEURISTIC) |

[PROOF-DRAFT] So the K²-coefficient of the lower bound is [I(σ) − ∫V_ν dσ] from Lemma Q plus C*(ν) from Step E,
and C*(ν) is Xu's (11). [COMPUTED, C1] C*(6) = 2.65303599034049, equal to Xu's printed ≈ 2.65303599034049 (l. 170) and to
E33's 2.6530359903404888.

## 6. Check against Xu (6)-(12) and the proposer's sketch

[CITED, Xu, Anchen0823/zeta9-research-notes@eb264a73, `missions/zeta7/research/analytic-foundations.md`, cached, read
l. 1-220] Xu's upper bound (10)-(12) and Proposition 1 are mirror images:
- Andréief: used in both.
- Weight: Xu bounds it above (Fauzan (6.11)); we bound it below (ℓ = 1).
- (9): Xu uses the upper half for D_N^(2q) and the lower half for D_K; we use the lower half for D_N^ν and the upper
  half for D_K.
- The K²-order step: Xu's (8) needs a comparison measure ρ, the bound M of (7) and circle regularisation with
  ε = K^-2. Ours is Lemma Q, which needs a trial measure σ and an ordered box of side K^-2.
- (11): the same C* in both.
- Result: Xu gets ≤ [λM − I(ρ) + C*]K² + O(K log K); we get ≥ [I(σ) − ∫V dσ + C*]K² − O(K log K).

[PROOF-DRAFT] With derivation.md Lemma 2 (LB(ν; σ) ≤ U(ν; ρ)) the two bounds form a consistent sandwich.

Corrections to the sketch (panel_verdicts.json, flsz-analytic, "mechanism" (b)):
- (1) Step 6's reason for "C* is Xu's" is inaccurate, as both verdicts say: Xu uses both halves of (9). C* is the
  same because it comes from S_K alone, which Step E evaluates to O(K log K).
- (2) The independent K^-4 boxes need a gap bound. The ordered box removes that need, and it also keeps τ ≥ K^-2,
  which the hard edge requires.
- (3) The field Riemann sum over the quantiles was not in the sketch. It is Lemma Q(b).
- (4) "Compact support in (0, ∞)" is relaxed to [0, ∞) (§4).
- (5) The room 0.0156424 should read ≤ 0.0156425 (C6).

**Standard lower bound.** Lemma Q plus Step B is the quantile/box half of the free-energy asymptotics for β = 2
log-gases, and Remark 3 is its averaging (Gibbs) form. The unweighted averaging step appears in Saff, *Logarithmic
potential theory with applications to approximation theory*, Surveys in Approximation Theory 5 (2010) 165-200
(arXiv:1010.3760, cached text): proof of Theorem 1.9, the display before (1.16), p. 172. There, the expectation of the
discrete energy under the product of equilibrium measures bounds its extremum. Theorem 6.1, p. 197, gives the weighted
Fekete version [CITED]. The β-ensemble large-deviation lower bound is commonly attributed to Ben Arous-Guionnet (PTRF
108, 1997), Johansson (Duke Math. J. 91, 1998), Anderson-Guionnet-Zeitouni (*An Introduction to Random Matrices*,
2010, §2.6) and Saff-Totik (*Logarithmic Potentials with External Fields*, 1997, Ch. III). None was opened here, and no
theorem numbers are claimed [HEURISTIC pointer]. The proof above is self-contained and does not depend on them.

## 7. Consequences

**Corollary 2 (the analytic ceiling; PROOF-DRAFT given E33(b)).** Let B_K be any sequence with F_K(ζ(7)) ≤ B_K for all
large K ∈ 40Z>0, from any analytic method (comparison measures, FLSZ-type products, saddle points, or anything else).
Then liminf K^-2 log B_K ≥ liminf u_K ≥ LB(6; fauzan16) ≥ −1.3871640488. The last inequality is E33(b), COMPUTED
with mpmath.iv and certified. So every bound log F_K(ζ(7)) ≤ U'K² + o(K²) has U' ≥ −1.3871640488. Its gain over
U_θ(6) ≤ −1.3715215895 (E33(a)) is at most 0.015642459335 per K² ([COMPUTED, C6, exact Fractions on the E33
endpoints]; rounded up, 0.0156425). At ν = 2 (opt36, hard edge, §4) the bound is LB(2) ≥ −2.5121443774 and the gain is
at most 0.043491999 (U_θ(2) uses opt36 as comparison measure, admissible by E36, PROOF-DRAFT). Romik's
U_true(6) = −1.3855098 (E32) is not used.

**Corollary 3 (the analytic half of E26; PROOF-DRAFT).** Let m_K > 0 be rational with m_K F_K ∈ Z[X]. Then
m_K·content(F_K) is a positive integer (Gauss), so log m_K ≥ K² a_K. By (2.1),

    K^-2 log(m_K F_K(ζ(s))) ≥ e_K ≥ a_K + LB(ν; σ) − E_σ(K)/K².

At (s, ν) = (7, 6): if liminf a_K > 1.3871641 (≥ −LB(6; fauzan16)), then liminf_K K^-2 log Q_K(ζ(7)) > 0 for every
nonzero integer polynomial Q_K proportional to Δ_K. So 0 < |Q_K(ζ(7))| < e^(−cK²) (Lai Lemma 3.1, (5), p. 3, page image checked; Xu §4, l. 183-196) fails
for all large K, whatever the arithmetic estimate and whatever the analytic estimate. **E26 becomes a PROOF-DRAFT once
liminf a_K > 1.3871641 is proved.** That statement is CONJECTURE: a_K = 1.931, 2.104, 2.149 at K = 40, 80, 120 (E25,
COMPUTED), and 1.3871641/2.149 = 0.645, so a bound capturing 65% of the computed a_K suffices. Prop 1 adds nothing on
the arithmetic side.

**Remark 3 (second proof by Jensen's inequality; PROOF-DRAFT).** Suppose in addition that σ has a density f_σ with
∫ f_σ |log f_σ| < ∞ and ∫ |log τ| dσ < ∞ (true for arcsine sums, including [0, b] components). Apply Jensen to
Z_K = E_P[F/∏_i f̂(τ_i)] with P = (σ/λ)^(⊗h) and f̂ = f_σ/λ. Since E_P[2Σ_{i<j} log|τ_j − τ_i|] = (1 − 1/h)K² I(σ),
and the per-point bounds (C1), (C2) and the full ℓ = 1 bound log[w_s(y)/(2y)] ≥ κ_s + (s−1) log y − 2πy hold for all
τ > 0, we get

    log Z_K ≥ (1 − 1/h)K² I(σ) − K² ∫V_ν dσ + h[(s−1) log K − log(2πK) − 1/(6K) + κ_s]
              + K[((s−1)/2) ∫ log τ dσ − ∫ log(f_σ/λ) dσ],

so log F_K(ζ(s)) ≥ LB(ν; σ)K² + (s − ν − 1)λ K log K − O_σ(K). It uses the same C*, no box and no quantiles, and its
only inequality is Jensen's, applied to the whole integral. The quantile proof stays the main one because the success
test asks for the quantile bound. Remark 3 also shows where s enters: only through the weight factor y^(s−1), at
K log K order. That matches the slope 2λ per step s → s + 2 measured in `../../zeta7_levers/flsz-analytic/room.out` (C)
(HEURISTIC fit there). [COMPUTED, C7, float64, not certified] With ∫ log τ dσ in closed form (−2.738566 for fauzan16,
−3.524151 for opt36) and ∫ log f_σ dσ by quadrature (1.01300 and 1.58874), the Jensen bound/K² is −1.3591, −1.3707 and
−1.3757 at (7, 6), K = 40, 80, 120. These lie below the exact −1.1641, −1.2584, −1.2944, and the same holds at every
stored K for (5, 6), (7, 2) and (5, 2).

## 8. What this does not show

- Nothing about a_K. The arithmetic half of E26 is open (CONJECTURE).
- [HEURISTIC] The value of lim u_K. Prop 1 and Xu (12) bracket every limit point between LB(ν; σ) and U(ν; ρ). That the
  limit exists and equals E*(ν) + C*(ν) is strong duality plus the matching upper bound at the equilibrium measure,
  which is not proved here.
- E_σ(K) is explicit but crude: E/K² = 0.59 at K = 120 for (7, 6), and it falls below the 0.0156 room only from K ≈ 7240
  on (C5). So Proposition 1 is an asymptotic statement and says nothing new at the computed K. Remark 3's bound is
  sharper but rests on float quadrature (C7).
- Rigour of the checks: C1 uses mpmath at 60 digits. C3 and C6 use exact fractions. C2 checks a finite grid. C4, C7 and
  C8 are float64. The certified numbers −1.3871640488, −2.5121443774, −1.3715215895 and −2.4686523779 are E33's
  (mpmath.iv, 113 bits). Here they are read, not recomputed.

## 9. Files

- `prop1.md` (this file).
- `check.py`: checks C1-C8. It reads `../../margin/out/U_cache.json`, `../../certify/out/{LB,margins}.json`,
  `../../witness/out/*.json` and `../../obstacles/out/*.json` (read-only).
- `check.out`: the output of `python3 check.py` (about 5 s; it ends with "All checks passed (C8 included).").

Run: `cd problems/108-zeta-odd-autopsy/evidence/e26_proof/prop1 && python3 check.py`.
