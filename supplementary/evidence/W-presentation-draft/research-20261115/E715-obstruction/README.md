# E715: the obstruction, made precise, for the thin single-pole class

Lane N, driver Claude Opus 5.5 on `[team machine]` (for [team member]), who asked what exactly the obstruction is. EVENT WORK, Sun Nov 15 2026, 00:07 to 00:25 PT. It sharpens E713's reading ("a route to ζ(7) would have to change the mechanism"), which was an inference from searched data, into four statements with proofs and one explicit hypothesis. No frozen claim changes; no Open Math OS run.

## The answer in one paragraph

In this class, the ζ(s) tail charges every prime p ∈ (K/2, K] exactly s + ⌊2K/p⌋ − τ_p powers in the denominator of the approximation, whenever τ_p < s (Theorem 2). The construction has four general ways to raise τ_p, each proved here (Theorem 3), and every one is paid for in polynomial degree:
- vanishing of order ν at the shifted poles (at most s + 1 powers), on two ranges of p fixed by N;
- a reflection that cancels one power on p ≤ 2K/3;
- root coverage: two powers on the primes p ≡ 1 (mod 4) that a complete block of roots reaches.

The decay, by contrast, is bounded by e^{−3.53K}, **whatever s is**, by a Jensen inequality against Prévost's weight (Theorem 1). Assume that no other systematic cancellation occurs (hypothesis H). Then the large primes alone make the approximations diverge for **every s ≥ 7 and for no s ≤ 5**: the best balance over all parameters is −2.21, −0.75, +0.245, +1.26 and +2.27 per pole for s = 3, 5, 7, 9, 11 (Theorem 4). **So for this class the obstruction sits exactly between ζ(5) and ζ(7).** Its source is the large primes of the ζ(s) tail, against an analytic ceiling that does not grow with s.

*Reviewed* (E714, Kimi K3.1 Pro, all 47 calls; replayed here): Theorems 2 and 4 pass, and Theorems 1 and 3 pass with corrections that are made below. The reviewer confirmed D(0,0) = 3.52549434807829 and the original table to 9 digits, independently. The sharper Theorem 2′ and root coverage came after the review; they have not been reviewed by a second family yet.

## The class

Odd s ≥ 3. For K ≥ 1 take f(t) = A(t)/D_K(t) with D_K(t) = ∏_{k≤K}(t + k²) and A = D_N(t)^ν B(t), where A is a monic integer polynomial of degree K − (s+1)/2 and B ≥ 0 on t ≥ 0 (for example B = p² with integer roots: E708, E709, E713). The approximation r is the root of the linear form Σ_j Res_{t=−j²} f · μ_X(1/(t+j²)), with μ_X(1/(t+j²)) = j^{s−1}(X − H_j^{(s)}) + 1/(2j) − 1/(s−1). Its X coefficient is ±1, q is its reduced denominator, and e = |r − ζ(s)|. Closing means q e → 0. At X = ζ(s) the functional is μ(R) = ∫_0^∞ R(y²) w_s(y) dy with w_s(y) = (2(2π)^{s−1}/(s−1)!) y^s Σ_ℓ ℓ^{s−1} e^{−2πℓy} (report, CITED: Xu; Prévost). So e = ∫_0^∞ f(y²) w_s(y) dy > 0. (COMPUTED check of this representation, by mpmath quadrature at s = 7: ∫ w_7(y)/(y² + j²) dy agrees with j^6(ζ(7) − H_j) + 1/(2j) − 1/6 to 27 to 31 digits at j = 1, 2, 5.)

## Theorem 1 (decay ceiling; PROOF-DRAFT)

For every family in the class with N = βK, and every probability measure ν on [0, ∞) of finite entropy,

  −ln(e)/K ≤ ∫ V_{ν,β} dν − (1 − νβ) · inf_{x∈ℝ} ∫ ln|x − u| dν(u) + O(ln K / K),
  V_{ν,β}(x) = 2π√x + ∫_0^1 ln(x+u²) du − ν ∫_0^β ln(x+u²) du.

*Proof.* Put t = y² = K²x and let g be the density of y when x ~ ν. Jensen gives ln ∫ F ≥ ∫ g ln(F/g) for F = f(y²) w_s(y) ≥ 0. Each root ρ of B contributes ∫ ln|K²x − ρ| dν ≥ 2 ln K + inf_{x∈ℝ} U_ν(x), since |x − ρ| ≥ |x − Re ρ|. The factor D_N^ν contributes ν Σ_{k≤N} ∫ ln(K²x + k²) dν ≥ 2νN ln K + νK ∫∫_0^β ln(x+u²) du dν, a right Riemann sum of an increasing function. Next, since u ↦ ln(x+u²) is increasing, Σ_{k≤K} ln(x + (k/K)²) ≤ K∫_0^1 ln(x+u²) du + ln(1 + 4/x), so ln D_K(K²x) ≤ 2K ln K + K∫_0^1 ln(x+u²) du + ln(1 + 4/x). The last term has a finite integral against the arcsine measure on [0, b], so it is O(1). (The first version printed + ln(x+4), which fails as x → 0; corrected after E714.) Also ln w_s(y) ≥ c_s + s ln y − 2πy (the ℓ = 1 term). The entropy term is ln K + O(1). The ln K terms cancel up to (s+1) ln K. ∎

With ν the arcsine measure of [a, b], the infimum is ln((b−a)/4). Minimizing over (a, b) gives **D(0, 0) = 3.5255 on [0, 0.125]**, a bound for every family whatever s, ν, N and B are (`ceiling.py`, `criterion.py`; any (a, b) gives a valid bound). The searches of E713 reach 3.29 at K = 40 and 3.35 at K = 80, so the ceiling is within about 5% of what is achieved. The field V_{ν,β} is the report's V_ν with α = β: as the report says, it does not depend on s.

## Theorem 2 (the large primes; PROOF-DRAFT, whole class)

Let p be prime with K/2 < p ≤ K, p > s and p² > 2K. Put T_p = Σ_{j=p}^{K} (−1)^j C(2K, K+j) j^{s+1} A(−j²) ∈ ℤ and τ_p = v_p(T_p). If s + ⌊2K/p⌋ − τ_p ≥ 4, then v_p(q) = s + ⌊2K/p⌋ − τ_p; otherwise v_p(q) ≤ 3.

*Proof.* Res_{t=−j²} f = (2/(2K)!) (−1)^{j−1} C(2K, K+j) j² A(−j²), because ∏_{k≠j}(k² − j²) = (−1)^{j−1}(K−j)!(K+j)!/(2j²). With A_j the residue times j^{s−1} times the sign of the X coefficient, Σ A_j = 1, and

  r = Σ_{i≤K} S_i i^{−s} + Σ_j B_j,  S_i = Σ_{j≥i} A_j,  B_j = −A_j j^{1−s}(1/(2j) − 1/(s−1)).

Then S_p = ±(2/(2K)!) T_p and v_p((2K)!) = ⌊2K/p⌋ ≤ 3. Every other piece has valuation ≥ −3: S_i ∈ (2/(2K)!)ℤ with p ∤ i for i ≠ p (since 2p > K); B_j for j ≠ p; and B_p, whose j^{s+1} gives v_p(B_p) ≥ −2. So S_p p^{−s} is the strict minimum when its valuation is ≤ −4. ∎ This is E712's Lemma 2 for the whole class.

**Theorem 2′ (sharper; PROOF-DRAFT, after E714).** Under the same conditions, with F = ⌊2K/p⌋: if τ_p ≤ s − 1, then v_p(q) = s + F − τ_p exactly; otherwise v_p(q) ≤ F. *Proof.* Every piece other than S_p p^{−s} lies in (2/(2K)!)·ℤ_(p) with p-free extra factors, so its valuation is ≥ −F (and B_p's is ≥ −F + 1). S_p p^{−s} has valuation τ_p − F − s, which is strictly below −F exactly when τ_p < s. ∎ For p > 2K/3 (F = 2) this certifies the costs 3 that Theorem 2 could only bound.

## Theorem 3 (the general divisibility mechanisms; PROOF-DRAFT, whole class)

For K/2 < p ≤ K:
- (a) *Direct vanishing:* if p ≥ K − N, then τ_p ≥ min(ν, s+1). (For j = p + t with 1 ≤ t ≤ N, the factor (t² − j²)^ν = (−p(p+2t))^ν appears; for j = p, j^{s+1}.)
- (b) *Mirror vanishing:* if p ≤ 2N + 1, then τ_p ≥ min(ν, s+1). (Every j ∈ [p, K] has j − p ≤ N or 2p − j ≤ N, and k = 2p − j gives k + j = 2p.)
- (c) *Reflection:* if p ≤ 2K/3, then τ_p ≥ 1. (Lucas modulo p, as in E712's Lemma 4a; it needs only that j^{s+1}A(−j²) is even in j. E714's reviewer checked the involution, j ↦ 3p − j.)
- (d) *Root coverage* (found after E714): if p ≡ 1 (mod 4) and B contains the double roots a² for every a ≤ (p−1)/2, then τ_p ≥ 2. (−1 is a square mod p, so for each j with p ∤ j some a ≤ (p−1)/2 has a ≡ ±√−1·j mod p, and (j² + a²)² supplies p²; the term j = p has p^{s+1}.) The analytically best root sets of E713 are exactly such blocks {1..A} with A ≈ 0.28K, so this mechanism is not a curiosity.
- (e) *Endpoint root* (found by E714's reviewer): if K = p is prime and a = p is a root, the single term j = p gains more; this affects one prime and weight O(ln K).

**Hypothesis H (restated after E714).** Counting root coverage only through complete blocks as in (d), the excess Σ_{K/2<p≤K} (τ_p − τ_p^{mech}) ln p over mechanisms (a) to (d) is o(K). (Partial blocks would have to hit the needed residues ±√−1·j mod p for many primes at once; nothing in the computations does.) The reviewer's 19 families and 268 large primes found no positive-weight exception.

*COMPUTED support for H* (`check_general.py`, `general-check.json`, and E712): Theorems 2 and 3 hold at every large prime of the 7 families checked (s = 3, 5, 7; K = 40 to 160; 73 primes) and of E709's family for n ≤ 20 (351 primes in the Lemma 3 range). The excess per K is 0, 0, 0, 0.037 and 0.039 for the families at K = 40 to 160, plus single primes of 0.18 and 0.215 at K = 40 and 80 (they look like coincidences of a free root a ≡ ±√−1·j mod p). E709's family has 2 exceptions among 351 primes up to n = 20.

## Theorem 4 (the obstruction; conditional on H)

Count, by the prime number theorem, the large-prime part of ln q: LP_s = ∫_{1/2}^{1} c(y) dy with y = p/K and c = s + ⌊2/y⌋ − τ^{mech}, counted as 0 when τ^{mech} ≥ s (Theorem 2′ then gives only an upper bound). If a family closes ζ(s), then LP_s ≤ D + o(1), where D is Theorem 1's bound for its parameters. Two cases cover the class (generous to it: gains of different mechanisms are added, capped at s + 1):
- **no covering block:** parameters (ν, β); grid νβ of step 1/200 for ν = 0..12 (`criterion2.py`, `criterion2.json`);
- **a covering block {1..αK}, α ∈ (1/4, 1/2]:** two more powers on the primes ≡ 1 (mod 4) up to 2αK, and D with the block's roots fixed in Theorem 1 (free mass 1 − νβ − 2α); grid of 13 α by up to 12 β by ν = 0..12 (`criterion3.py`, `criterion3.json`). A block with α ≤ 1/4 covers no prime above K/2.

| s | min (LP_s − D), no covering block | with a covering block | overall | verdict |
|---|---|---|---|---|
| 3 | −2.21 (ν = 3, νβ ≈ 0.99) | −1.60 | **−2.21** | not excluded by the large primes |
| 5 | −0.75 (ν = 5, νβ ≈ 0.86) | −0.55 | **−0.75** | not excluded by the large primes |
| 7 | +0.245 (ν = 7, νβ ≈ 0.89) | +0.48 | **+0.245** | **excluded: q e grows at least like e^{0.245K}** |
| 9 | +1.26 (ν = 9, νβ ≈ 0.90) | +1.50 | **+1.26** | excluded |
| 11 | +2.27 (ν = 11, νβ ≈ 0.90) | +2.52 | **+2.27** | excluded |

The critical configuration is ν = s, the smallest vanishing order that clears a prime's cost to zero in Theorem 2′. It spends about 89% of the degree on D_N^ν and pays with a lower decay (D = 3.11 instead of 3.53). Covering blocks never help the class: the degree they take costs more decay than the two powers they save. The first table (Theorem 2's cruder threshold "≥ 4") gave +0.095 at s = 7. E714's reviewer recomputed that one independently, to 9 digits (`criterion.json`, `refine.json`).

## What to say in the report (labels as above)

- **Precise form (Theorems 1 to 4, PROOF-DRAFT with hypothesis H):** In the thin single-pole class, the analytic decay is at most e^{−3.53K} for every s. The ζ(s) tail charges each prime in (K/2, K] exactly s + ⌊2K/p⌋ − τ_p powers. The class raises τ_p only through vanishing (at most s + 1 powers), reflection (one power) and root coverage (two powers on primes ≡ 1 mod 4), each bought with degree. Under H, no family in the class closes ζ(s) for s ≥ 7, and the large primes do not exclude s = 3 or 5.
- **Strength:** the ζ(7) margin is +0.245 per pole, and it is conservative. It improves with any better trial measure in Theorem 1, and it ignores all primes ≤ K/2, which in the computed families cost a further 2 to 4 per pole. The mechanisms' gains were added together and capped generously.
- **Not shown:** H itself; the primes ≤ K/2; anything about other classes (higher-order poles, the Hankel determinant method of the ζ(5) proof, whose ζ(7) failure is E62/E63). The class requires a nonnegative integrand, since Theorem 1 uses Jensen. No irrationality or novelty claim.
- **Review status:** Theorems 1 to 4 in their first form had a second-family review (E714, Kimi K3.1 Pro): passes with two corrections, both made here. Theorem 2′, mechanism (d) and the second table came after it and are this session's only. No human has read any of it.

## Files

`ceiling.py` (Theorem 1 at ν = 0), `criterion.py` → `criterion.json` (the first table, Theorem 2's threshold), `refine.py` → `refine.json` (its fine grid at s = 7), `criterion2.py` → `criterion2.json` (Theorem 2′, no covering block), `criterion3.py` → `criterion3.json` (with root coverage), `check_general.py` → `general-check.json` (Theorems 2 and 3, and H, on families of E713). Needs Python 3 with scipy (and the E713 folder for `family.py`). The review is in `../E714-review/` (`PARENT_REVIEW.md`, `worker/`).
