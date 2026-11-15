# The step in the true exponent of the package's own polynomial (lane W, #108)

Claude Opus 5.5 (Claude Code, [team machine]), for [team member], Sun 15 Nov 2026, about 06:15 PT. EVENT WORK (Phase 3, at [team member]'s explicit request: "is there a way we could establish an actual result about how much the true cost rises by?"). **No human has read this proof.** Labels per AGENTS.md section 2: the lemma and the theorem are PROOF-DRAFT (report: CONJECTURE, written proof in this file); the two Lean inputs are those of the ledger; the numbers in section 5 are COMPUTED from stored exact values.

## 1. What is proved, in one paragraph

Fix Fauzan's template K = 40n, N = 3n, h = 37n (α = 3/40, λ = 1 − α = 37/40), an even ν with 2 ≤ ν ≤ 10 and a natural cutoff M ≥ 40. For odd s ≥ 5 let m_n(s) be the package's own multiplier (`normalizerSharp s ν (40n) (3n) M (explicitAllocation …)`), F_n(s) = S_n det G_n(X) and Q_n(s) = m_n(s) F_n(s), the package's integer polynomial. Define its **true exponent**

  E(s) := limsup_(n→∞) (1/K²) log Q_n(s)(ζ(s))   (a value in [−∞, ∞)).

**Theorem.** E(s+2) = E(s) + 2λ/3 + I_out(s+2, ν, α) − I_out(s, ν, α), and E(s) = −∞ exactly when E(s+2) = −∞. At ν = 6, from 5 to 7, the step is 751/768 (Lean, `sstep_value_nu6`). From 5 to 7 it lies in [0.800, 1.034] over even ν ≤ 10 (E14, COMPUTED; Lean at ν = 6 and 8). For every odd s ≥ 7 and ν ≤ 10 it is at least 167/300 (Lean, `sstep_ge`).

So the package's actual polynomial value, not a bound on it, pays exactly the arithmetic step. The energy constant U plays no role: the analytic parts at s and s + 2 cancel in the limit.

## 2. The three inputs

1. **Arithmetic limit (Lean, E432; ledger C108-I2, update Sat 19:03).** `explicit_normalizer_limit_statement`: for odd s ≥ 5, even 2 ≤ ν ≤ 10, natural M ≥ 40, log m_n(s)/(40n)² → A_M(s) := `thetaPkg s ν (3/40) M 0` (evidence/B-bridge-final-gate/Project/Final.lean, ExplicitTargets.lean).
2. **The scalar step (Lean, `thetaPkg_sstep`, Mathathon/P108/SStep.lean; ledger C108-I3).** With U = 0: A_M(s+2) − A_M(s) = 2λ/3 + I_out(s+2) − I_out(s), for all real s, ν, α and M ≥ 3. The values 751/768 (`sstep_value_nu6`) and ≥ 167/300 (`sstep_ge`, real s ≥ 7, ν ≤ 10) are also Lean.
3. **Lemma W (new, section 3).** log F_n(s+2)(ζ(s+2)) − log F_n(s)(ζ(s)) = O(K log K).

*Proof of the theorem from 1-3.* Write E(s) = lim a_n(s) + limsup b_n(s) with a_n = log m_n/K² (a convergent sequence, by 1) and b_n = log F_n(ζ(s))/K². By Lemma W, b_n(s+2) − b_n(s) → 0, so the two limsups are equal (both finite or both −∞). Hence E(s+2) = E(s) + (A_M(s+2) − A_M(s)), with (−∞) + δ = −∞ when both are −∞, and A_M(s+2) − A_M(s) is input 2. ∎ (Wording fixed after the Kimi review, section 7.)

Lemma W was stated without proof in criterion5/derivation.md section 4, citing Xu ("the zeta index s changes only lower-order factors of the weight", Anchen0823/zeta9-research-notes@eb264a73, analytic-foundations.md section 3). The proof below is ours.

## 3. Lemma W and its proof

**Lemma W.** Let s ≥ 3 be an odd integer, ν ≥ 0 an integer, and N < K, h ≤ K. Write Δ(s) := det G(ζ(s)) for the h × h Hankel determinant of the construction. Then Δ(s) > 0, and for all K ≥ K₀(s, ν, N/K):

  h·log c_s ≤ log Δ(s+2) − log Δ(s) ≤ h·log((s−1)!·8π²·(K⁴ + 2)),   c_s := 1/(s(s+1)(s−1)!).

Since S_n does not depend on s, the same bounds hold for log F_n(ζ(s+2)) − log F_n(ζ(s)); both sides are O(K log K).

**Step 0: the integral representation (CITED).** At X = ζ(s) the functional integrates against Prévost's weight (Prévost, Results Math. 74 (2019), Theorem 1; Calegari's blog of 24 Sep 2026; deck page 5; in Lean for symbolic s at ν = 6 by E414/E431):

  G(ζ(s))_(ij) = ∫_0^∞ y^(2(i+j)) ρ_s(y) dy,   ρ_s(y) = φ(y) w_s(y),   φ(y) = D_N(y²)^ν / D_K(y²),
  w_s(y) = c'_s y^s Σ_(ℓ≥1) ℓ^(s−1) e^(−2πℓy),   c'_s = 2(2π)^(s−1)/(s−1)!.

Only w_s depends on s; φ and S_n do not. With t = y², G(ζ(s)) is the Hankel matrix of the positive measure μ_s(dt) = f_s(t) dt, f_s(t) = ρ_s(√t)/(2√t), on (0, ∞). By Heine's formula (Szegő, *Orthogonal Polynomials*, Ch. II, CITED),

  Δ(s) = (1/h!) ∫_((0,∞)^h) ∏_(i<j) (t_i − t_j)² ∏_i μ_s(dt_i) > 0.

**Step 1: the two weights are comparable, explicitly.** Put q = e^(−2πy) and P_m(q) = Σ_(ℓ≥1) ℓ^m q^ℓ = q A_m(q)/(1 − q)^(m+1), where A_m is the Eulerian polynomial: nonnegative integer coefficients, constant term 1, A_m(1) = m!, so 1 ≤ A_m(q) ≤ m! on [0, 1] (Comtet, *Advanced Combinatorics*, §6.5, CITED). Then

  r(y) := w_(s+2)(y)/w_s(y) = ((2π)²/(s(s+1))) · (y/(1 − q))² · A_(s+1)(q)/A_(s−1)(q).

Using 2πy/(1 + 2πy) ≤ 1 − e^(−2πy) ≤ 2πy:

  c_s = 1/(s(s+1)(s−1)!) ≤ r(y) ≤ (s−1)!·(1 + 2πy)²   for every y > 0.

**Step 2: lower bound.** Pointwise ρ_(s+2) ≥ c_s ρ_s, and the integrand of Step 0 is nonnegative, so Δ(s+2) ≥ c_s^h Δ(s).

**Step 3: upper bound, by Christoffel's formula.** Pointwise ρ_(s+2)(y) ≤ (s−1)!(1 + 2πy)² ρ_s(y) ≤ (s−1)!·8π²·(t + c)·ρ_s(y), with t = y² and c = 1/(4π²), because (1 + 2πy)² ≤ 2 + 8π²y². Therefore

  Δ(s+2) ≤ ((s−1)!·8π²)^h · Δ[(t + c)μ_s] = ((s−1)!·8π²)^h · Δ(s) · ∏_(k=1)^h (x_k + c),

where Δ[(t + c)μ_s] is the Hankel determinant of the measure (t + c)μ_s, and x_1 < … < x_h are the zeros of the monic orthogonal polynomial P_h of μ_s. The equality is Christoffel's theorem (Szegő, Theorem 2.5, CITED), or directly from Heine's formula: E[∏(t_i + c)] = (−1)^h P_h(−c) = ∏(x_k + c). All x_k lie in (0, ∞). So it remains to show x_h ≤ K⁴ + 1.

**Step 4: the zeros are at most K⁴ + 1.** The largest zero is the largest eigenvalue of the truncated Jacobi matrix, x_h = max over polynomials p ≠ 0 of degree < h of ∫ t p² dμ_s / ∫ p² dμ_s (Szegő, Ch. III, CITED). Fix such a p, of degree d < h ≤ K, and put T = K⁴.
- *Density on (0, 1].* For t ≤ 1: φ ≥ (N!)^(2ν)/∏_(j≤K)(1 + j²) ≥ 1/(2^K (K!)²); w_s(y) ≥ c'_s q/(2π)^s ≥ e^(−2π)/(π(s−1)!) (Step 1's bounds); and 1/(2√t) ≥ 1/2. So f_s ≥ e^(−C K log K) on (0, 1], and ∫_0^1 p² dt ≤ e^(C K log K) ∫ p² dμ_s.
- *Size of p beyond 1.* By the Legendre expansion on [0, 1], ‖p‖²_(∞,[0,1]) ≤ (d + 1)² ∫_0^1 p² dt. By Chebyshev's extremal property, |p(t)| ≤ ‖p‖_(∞,[0,1]) T_d(2t − 1) ≤ ‖p‖_(∞,[0,1]) (4t)^d for t ≥ 1 (CITED, standard).
- *Density beyond 1.* For t ≥ 1: φ ≤ (1 + N²)^(νN) t^(νN), and w_s(y) ≤ c'_s (s−1)! y^s e^(−2πy)/(1 − e^(−2π))^s. So f_s(t) ≤ e^(C K log K) t^(νN + s/2) e^(−2π√t).
- *Tail.* Hence ∫_(t>T) t p² dμ_s ≤ e^(C K log K) [∫_(t>T) t^(1 + 2d + νN + s/2) e^(−2π√t) dt] ∫ p² dμ_s. With t = u², the bracket is ∫_(u>K²) 2u^(a) e^(−2πu) du with a = O(K); for K ≥ K₀, u^a ≤ e^(πu) on u > K², so the bracket is at most e^(−πK²). So ∫_(t>T) t p² dμ_s ≤ e^(C K log K − πK²) ∫ p² dμ_s ≤ ∫ p² dμ_s.
- Together with ∫_(t≤T) t p² dμ_s ≤ T ∫ p² dμ_s: the Rayleigh quotient is at most T + 1, so x_h ≤ K⁴ + 1.

Then ∏(x_k + c) ≤ (K⁴ + 2)^h, and Step 3 gives the upper bound of the lemma. ∎

(The constants C depend only on s, ν and N/K. Nothing in the proof uses that s is odd beyond Step 0's representation; Step 1 needs s ≥ 2.)

## 4. Scope and limits

- **The package's own polynomial.** E(s) is the exponent of m_n F_n for the package's explicit multiplier, the one E432 controls. The smallest integer multiplier (the primitive content) may be smaller. Whether *its* exponent also steps by 751/768 is the open E26/H0 question.
- **Differences only.** The theorem gives E(s+2) − E(s), not E(s). Pinning E(5) or E(7) themselves needs a lower bound on the true decay rate, (1/K²) log F_n(ζ(s)) ≥ U* − o(1). That is standard potential theory (n-th-root asymptotics of Hankel determinants with varying weights) but is not proved in this repository. The team's LB (criterion5/derivation.md, Lemma 2) bounds certificates only; "U* = E* + C*" is HEURISTIC there. Known one-sided facts: E(5) ≤ Θ_pkg(5, 6; 10⁶, u) < 0 (Claim 8), so E(7) = E(5) + 751/768 < 751/768.
- **limsup.** E(s) need not be a limit. The theorem holds for limsups because the arithmetic part converges.
- **Not Lean.** Lemma W and the deduction are written proofs; inputs 1 and 2 are Lean (gates pass; statements compared by a second AI model family, not a human).

## 5. Numerical check (COMPUTED, `check.py`)

Rounded values (4 decimals; 3 for ζ(7) at n = 1, 3) of stored exact computations at ν = 6 of u_K = log F_K(ζ(s))/K², with their rounding carried as intervals: ζ(5) from evidence/boundary5/README.md (table B1), ζ(7) from evidence/obstacles/README.md (E25). Compare D := log F(ζ(7)) − log F(ζ(5)) = K²(u_K(7) − u_K(5)) with Lemma W's two bounds:

| n | K | u_K(5) | u_K(7) | D = K^2 (u_K(7) - u_K(5)) | D / (K log K) | lower bound h log c_5 | upper bound | inside |
|---|---|---|---|---|---|---|---|---|
| 1 | 40 | -1.2757 | -1.164 | 178.7 ± 0.9 | 1.211 | -243.4 | 825.2 | True |
| 2 | 80 | -1.3294 | -1.258370207 | 454.6 ± 0.3 | 1.297 | -486.9 | 1855.6 | True |
| 3 | 120 | -1.3478 | -1.294 | 774.7 ± 7.9 | 1.349 | -730.3 | 2963.4 | True |
all inside Lemma W's bounds: True

The difference D is positive and grows like 1.2-1.35 · K log K, inside both bounds at every n. Per K² it shrinks: 0.112, 0.071, 0.054. HEURISTIC reading: the pointwise factor y² ≈ K²t per variable gives about 2h log K = 2λ K log K ≈ 1.85 K log K at leading order, less a t-dependent O(K) term.

## 6. Sources

Prévost (Results Math. 74, 2019, Thm 1) for the weight; Xu (zeta9-research-notes, analytic-foundations §3) for the claim that s changes only lower-order terms; Szegő, *Orthogonal Polynomials*, Ch. II-III and Thm 2.5 (Heine's formula, Jacobi matrices, Christoffel); Comtet, *Advanced Combinatorics*, §6.5 (Eulerian polynomials); the team's Lean E432 and `thetaPkg_sstep` (lanes B and L; Firsching's mo271/Zeta5 architecture underneath).

## 7. Cross-family review (Kimi K3.1 Pro, Open Math OS, Sun 15 Nov 08:00-08:03 PT)

Brief: VM `N-W-lemmaW-review/BRIEF.md` (written by this lane, launched at [team member]'s request); worker chat `chat-2467227dd9`, effort high, 14 model calls; transcript `log/transcripts/omos/p-a217855738464a2684aabaf655cafe60-chat-2467227dd9-seq0.jsonl.gz`. Report copied to `review-kimi/REVIEW.md` (with its rerun outputs).

- **Verdict: pass with qualification.** W1 Steps 0-4 pass, each checked line by line (constants of Step 1, the Christoffel sign, the Rayleigh, Nikolskii, Chebyshev and tail estimates of Step 4, and K₀'s dependence on s, ν and N/K only). W2 passes. W3 is partial: `check.py` reruns byte for byte, but its inputs are rounded values, not an exact replay.
- **Its two findings were both minor wording issues, both fixed here at 08:04 PT:** the line that wrote E(s+2) − E(s) without the −∞ case (section 2), and "stored exact values" for the rounded inputs (section 5 and `check.py`).
- **Not checked by the reviewer:** the cited sources (Prévost, Szegő, Comtet) and the two Lean inputs, which the brief allowed it to take as given. It found Xu's s-independence remark at the level of the external field, but not Lemma W's explicit two-sided bounds; it makes no novelty claim.
- **Label:** still PROOF-DRAFT; no human has read it. In the deck's language it is now a written proof with a passing review by another model family.
