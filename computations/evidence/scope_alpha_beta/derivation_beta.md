# Fauzan's bound package with a free Hankel size β = H/K: derivation (PROOF-DRAFT)

EVENT WORK, Sat Nov 14 2026 (04:17-05:08 PT), advocate:scope-alpha-beta (Claude Opus 5.5). No human has checked this file.
It extends `../criterion5/derivation.md` (E13, PROOF-DRAFT, event work of advocate:criterion5) from the slice h = K − N to an
independent Hankel size H. Every formula below is evaluated by `pkg_ab.py`; the checks are in `check_e13.py` (README §2).
Labels follow AGENTS.md §2.

**Sources** (all opened for this file):
- Fauzan, *ζ(5) is irrational*, Zenodo 22826419 v1, cached `~/mathathon-cache/108/fauzan_22826419.pdf` (text `fauzan.txt`):
  (3.11)-(3.12) p. 9; §4.1 (4.1)-(4.8) p. 10 and Prop. 4.1 with proof p. 11; §4.2 (4.9)-(4.10) p. 11, (4.11)-(4.13) and
  Lemma 4.2 p. 12, (4.14), the class table and Prop. 4.3 p. 13; §5 (5.1)-(5.3) p. 13, (5.4)-(5.6) p. 14, (5.12)-(5.13) p. 16.
- Xu, Anchen0823/zeta9-research-notes@eb264a73, `missions/zeta7/research/analytic-foundations.md` §2 (positivity, exact degree,
  and the block basis 1, …, t^(r−1), D_tail, …, t^(H−r−1) D_tail for H > r) and §3 (the paragraph "The same scaling calculation
  works if the Hankel dimension is independent": mass β, S_(K,N,q,H), C*(q, α, β)). **The free-β analytic side is Xu's**;
  he leaves open whether β improves the combined exponent. Everything new here is the arithmetic side for H ≠ K − N.
- `../criterion5/derivation.md` §1-§5 (the (s, ν) attribution, Prop. 1, the outer class sums, Lemma 2, Theorem 3).

## 0. Setting

s odd, ν even (exponent of D_N), α = N/K, **r = K − N** (the number of poles of D_tail = D_K/D_N, i.e. of X-dependent poles),
λ := r/K = 1 − α, and **H = βK** the Hankel size:

  G_H(X) = [μ_X(D_N(t)^ν t^(i+j)/D_K(t))]_(0≤i,j<H),  Δ_H = det G_H ∈ Q[X].

Fauzan, Anand and Lai use H = r (β = λ). Xu §2 proves Δ_H(ζ(s)) > 0 for every H and deg_X Δ_H = r for H ≥ r (CITED). For H < r this derivation uses only
**deg_X Δ_H ≤ H**, which holds because every entry of G_H is affine in X; that is all that clearing the denominator of a rational
ζ(s) = a/b needs (multiply by b^H). *Correction of Sun 06:53 PT (integrator, after the Kimi review E716, check 2):* an earlier version
said here that E29 found deg_X Δ_H = H for the computed H < r. That is false in general (in the reviewer's table 11 of 120
small cases have lower degree; lane N's remark: an entry μ_X(t^m D_N^ν/D_K) contains X only when νN + m ≥ K − (s+1)/2, so
deg_X Δ_H ≤ max(0, 2H − K + (s+1)/2 + νN), PROOF-DRAFT). Nothing in §1 to §5 used the equality. Below, "the package" is Fauzan's §3-§5 with s, ν (E13) **and H** carried as
symbols, and Θ(s, ν, α, β; M, ρ) = A_M + U is its margin; the method proves ζ(s) irrational iff Θ < 0 for one M ≥ 40 and one
admissible ρ (Lai Lemma 3.1, as in E13).

**The normaliser is bookkeeping.** With Fauzan's (5.1)-(5.2) (p. 13), m_(K,M) = ∏_p p^(−L_p), L_p = v_p(S) + γ_p, both signs
kept ("a positive bound allows division by a power of p"), so log(m S Δ_H(ζ(s))) = log Δ_H(ζ(s)) − Σ_p γ_p log p, whatever S is.
S only books the K² log K cancellation. We use Xu's S_(K,N,q,H) = 4^(H−1)(K!)^(2H)/((N!)^(2νH) ∏_(i<H)(2i)!²) (Fauzan's S_K with
h → H), whose Legendre valuation is (5.3) with h → H. (PROOF-DRAFT; immediate from (5.1)-(5.2).)

## 1. Which constants change with β, and why

| Fauzan's constant (place, page) | at (5, 6, λ) | general (s, ν, α, β) | why |
|---|---|---|---|
| total dimension "h" in (4.4) mT + E = h − L₀ + 3(N − m_N), p. 10 | h = λK | **H = βK** | the rows are Poly_(<H) |
| Lai's H = λ + 3α in T = ⌊2Hx⌋, s = Hx − T/2 ((5.4) p. 14; Lai (8)) | 23/20 | **H_L = β + (ν/2)α** | (4.4): mT ≈ H + (ν/2)N, m = (p−1)/2 |
| 2λ in "T − b_a > 2λx − 81/20 ≥ 3/2" (L_a ≥ 0, p. 10) | 2λ | **2β** (and ν/2 for 3) | T − b_a > 2βx − 21/20 − ν/2 |
| 2h, 12h, 2Σ_(i<h) in v_p(S_K) (5.3) p. 13 | 2λ, 12λ, J(λx) | **2β, 2νβ, J(βx)** | S with h → H |
| N(x) = 2λx⌊x⌋ − 12λx⌊αx⌋ − 2J(λx) (5.5) p. 14 | | **2βx⌊x⌋ − 2νβx⌊αx⌋ − 2J(βx)** | (5.3) at p > √K |
| F = 4λ + 2λ{x} − 12λ{αx} (5.12) p. 16 | | **(s−1)β + 2β{x} − 2νβ{αx}**, mean (s−ν)β | Prop. 1′ below |
| crude range (3.12) "−6h⌊log_p 5K⌋ − h v_p(24)", p. 9 | 6λ/M | (s+1)β/M | one crude loss per row (irrelevant as M → ∞) |
| "only the primes p ≤ 2h enter" (5.2), p. 13; outer upper limit 2λ | 2λ | **max(1, 2β)** | (2i)! with i < H |
| rank intercept K + 4N in (4.10), p. 11 | 1 + 4α | **2β − 1 + να** | L_ij = 0 for i + j < K − νN + r_s(p−1) − 1, i, j < H |
| rank clamp min(h, ·) | λ | **β** | rank ≤ matrix size |
| zero-weight rows z in Lemma 4.2, (4.13) p. 12 | ẑ_λ(y) | **ẑ_λ(y) + (β − λ)** | §3 below |
| outer class costs 7(ℓ−2), c¹(ℓ) and their zero counts (table p. 13) | | **unchanged** | properties of the r-row basis (4.11) |
| −2λ⌊1/y⌋ + Σ_j(2λ − jy)₊ (outer part of (5.3)) | | **−2β⌊1/y⌋ + Σ_j(2β − jy)₊** | (5.3) at p > K/3 |
| V_ν (Xu (6)) | | unchanged | per-point field: D_N^ν/D_K and w_s do not see H |
| mass of the comparison measure (Lai Lemma 11.4, Xu (7)-(8)) | λ | **β** | H points in the Andréief integral |
| C*(ν) = −2λ + 2ναλ(1 − log α) + 3λ² − 2λ² log 2λ (Xu (11)) | 2.6530 | **C*(ν, α, β): λ → β** | Stirling for S_(K,N,q,H) (Xu §3, CITED) |

Unchanged: everything E13 attributes to s (s−1 inner loss, s+2 outer per-pole cost, r_s = (s−1)/2 rank slope, s+1 crude factor)
and to ν (ν/2 allocation, ν−1 removed-class factor), and α (class densities). **α enters only through class counts and the
field; β only through the row count.** At β = λ every row reduces to E13 (exact identity, check C1).

## 2. Inner range K/M < p ≤ K/3 (Fauzan §4.1, Prop. 4.1, pp. 10-11)

Fauzan's proof of Prop. 4.1 uses h only through Σ_a L_a + L₀ = h in (4.4) and the degree bounds "≤ p + 1" (true for K large at
fixed M). The basis (4.5) E_(a,i) = ∏_(c≠a)(t + c²)^(L_c)(t + a²)^i is a Z_p-unimodular basis of Poly_(<Σ L) for **any** nonnegative
L_a (Chinese remainder theorem, distinct residues −c² mod p). So with h → H in (4.4), Prop. 4.1 holds verbatim for every H for
which all L_a ≥ 0 (PROOF-DRAFT). From (4.4): 2H_L x − 21/20 < T < 2H_L x, b_a ≤ (ν/2)ℓ_max(αx), hence L_a ≥ 0 whenever
⌊2H_L x − 21/20⌋ + 1 − (ν/2)ℓ_max(αx) ≥ 0 for all x ≥ 3 (`pkg_ab.La_check`, the exact step-function test of E22 with λ → β in
H_L). Fauzan's own linear form gives the sufficient condition 6β − 21/20 − ν/2 > −1, i.e. **β > ν/12 + 1/120** (ν = 10: β > 0.842).

The limiting functions are (5.4)-(5.6) with H_L = β + (ν/2)α in T, s = H_L x − T/2, and N as in the table:

  Γ = ∫_0^(1/2)(T − b)(T + b − ℓ − s)dz + σ(2T − ⌊2x⌋ − s) + (σ − n₊)₊,  N = 2βx⌊x⌋ − 2νβx⌊αx⌋ − 2J(βx),  R = −Γ − N.

**Proposition 1′ (PROOF-DRAFT; exact check C3 at 1800 points).** R_(s,ν,α,β)(x) = x F_β(x) + Q_(ν,α,β)(x) with
F_β = (s−1)β + 2β{x} − 2νβ{αx} and Q = [τ(τ−σ′) − (τ−σ′)₊ + η(1−η)]/2 + (ν/2)²∫B² − (ν/2)∫AB, τ = {2H_L x}, σ′ = {2x}, η = {2βx}.
*Proof.* E13's proof with λ → β where it comes from the row count: the x-coefficient of Γ is −2H_Lτ − sβ + τ + (2H_L − 1)τ
= −s(H_L − (ν/2)α) = −sβ; the x² terms 2β(β + να − 1) cancel against N (this is Xu's raw/factorial K² log K cancellation, which
holds for every β); −J(βx) = −β²x² + βx/2 − η(1−η)/4 gives the rest. ∎ So the inner s-step is 2β/3 for every M, the mean slope is
(s − ν)β, and Corollary 4 becomes **Θ(s+2) − Θ(s) = 2β/3 + I_out(s+2) − I_out(s)** (U-free, M-free; check C4).

## 3. Outer range K/3 < p ≤ K (Fauzan §4.2, pp. 11-13)

Fauzan's basis (4.11), P_a q_(a,i), is a unimodular basis of Poly_(<r): one row per pole of D_tail. It needs H = r. Write w for its
r weights (4.12) (nonpositive half-integers), n for the number of negative ones and z_r = r − n for the zero ones (the zero
counts of the table, p. 13: 2 per unremoved class, z¹(ℓ) per removed class; per K this is ẑ_λ(y) = y − 2α + Σ dens·z¹).

**Lemma 3′ (PROOF-DRAFT).** Under (4.9) except 5N ≤ 2p − 2 (replaced by the clamp), with ρ_H := max(0, 2H + νN − K − r_s(p−1))
(r_s = (s−1)/2):
- (H ≤ r) if H ≥ n, then v_p(Δ_H) ≥ 2Σ_(w<0) w − min(ρ_H, H − n);
- (H ≥ r) v_p(Δ_H) ≥ 2Σ_(w<0) w − min(ρ_H, z_r + H − r).

*Proof.* Moment correction exactly as (4.10): G_H = A_H + p^(−1)L_H, L_H integral; in the monomial basis L_ij = 0 for
i + j < K − νN + r_s(p−1) − 1, so its first H − ρ_H rows vanish and rank L_H ≤ ρ_H (Fauzan's argument with h → H).
(H ≤ r) Poly_(<H) ⊂ Poly_(<r), so A_H = Pᵀ A_r P with P the integral r × H matrix of the inclusion in the basis (4.11), and
v(A_r,ij) ≥ w_i + w_j by (4.12). Expand det(A_H + p^(−1)L_H) by complementary minors (as in Lemma 4.2's proof): a term with a
k × k minor of p^(−1)L_H has valuation ≥ −k + v(det A_H[I^c, J^c]); by Cauchy–Binet, det A_H[I^c, J^c] = Σ_(S,S′) det P[S, I^c]
det A_r[S, S′] det P[S′, J^c] over (H−k)-subsets S, S′ of the r rows, each term of valuation ≥ Σ_S w + Σ_(S′) w, which is at least
twice the sum of the H − k most negative weights. If H − k ≥ n that sum is Σ_(w<0) w; each further dropped weight is ≤ −1/2 and
repays the −1 of its k. The minimum over k ≤ ρ_H is −min(ρ_H, H − n). (H ≥ r) Xu's block basis (§2): rows (4.11) for Poly_(<r),
then D_tail t^k (k < H − r), unimodular for Poly_(<H) (D_tail is monic of degree r). Every entry involving a second-block row is
μ′ of a polynomial, integral after the correction; give those rows weight 0. Lemma 4.2 (p. 12) applies verbatim with z = z_r + H − r.
∎ Both cases read: **zero count z_r + (H − r)**, the same formula on both sides of β = λ. Outer function, per K, y = p/K:

  T_out(y) = (s+2)[(1 − y) − Σ dens(ℓ)(ℓ−2)] + Σ dens(ℓ)c¹(ℓ) + min(r̂_β, ẑ_λ + β − λ) − 2β⌊1/y⌋ + Σ_(j≥1)(2β − jy)₊,
  r̂_β = min(β, (2β − 1 + να − r_s y)₊),  I_out(s, ν, α, β) = ∫_(1/3)^(max(1, 2β)) T_out dy,

with the class terms only for y ≤ 1 (for 1 < y ≤ 2β only the normaliser term (2β − y)₊ remains: Prop. 4.3's p > K case, whose
polynomial correction vanishes iff 2β + να − 1 < r_s; this holds for s = 7 on the whole grid and is imposed for s = 5).
**Saturation condition:** H ≥ n at every outer prime, i.e. z_β(y) := ẑ_λ(y) + β − λ ≥ 0 on (1/3, 1] (`PkgAB.zmin`). Below it the
cost is twice the sum of the βK most negative weights, a different formula not implemented here.

**Where it breaks in α.** Fauzan's (4.9) needs 2N < p (at most one removed pole per outer class, which the class densities
α − m_v, m_v − u, u assume). For p > K/3 this is **α < 1/6**. For α ∈ {7/40, 8/40} the outer formula is not derived (two removed
poles share a class for K/3 < p ≤ 2N); those rows are printed as the formula's continuation only.

## 4. Analytic side (Xu §3, CITED; Lemma 2 with mass β, PROOF-DRAFT)

V_(ν,α)(t) = 2π√t + ∫_0^1 log(t+u²)du − ν∫_0^α log(t+u²)du (unchanged); C*(ν, α, β) = −2β + 2ναβ(1 − log α) + 3β² − 2β² log(2β);
U(ν, α, β; ρ) = βM₀ − I(ρ) + C* for ρ of mass β with 2U^ρ − V ≤ M₀ (Xu (12) with λ → β). **Lemma 2′**: for every σ of mass β with
compact support and finite energy, U(ρ) ≥ LB(σ) := I(σ) − ∫V dσ + C*(ν, α, β) (E13's proof: σ − ρ has mass 0, Lai Lemma 11.5). The
scan maximises LB over nested arcsine families of mass β (`pkg_ab.lb_opt`); any σ gives a valid bound.

## 5. Theorem 3′ (the criterion over (α, β); PROOF-DRAFT given §1-§4)

Fix odd s, even ν ≤ 10, α < 1/6 and β with (i) L_a ≥ 0 (La_check), (ii) z_β ≥ 0 on (1/3, 1], (iii) 2β + να − 1 < r_s, plus Fauzan's
degree side conditions (true for K large). With A*(s, ν, α, β) = I_out + ∫_3^∞ R x^(−3)dx and U* the infimum over admissible ρ:
the package closes iff A* + U* < 0 (definitional, as in E13), and **if A* + LB(σ) > 0 for one σ, ζ(s) fails for every comparison
measure and every M with A_M ≥ A***. At β = λ this is E13/E15 exactly.

## 6. What this does not show

- The package's local bounds are not sharp; a different normaliser (primitive content) is outside it (E25, E35).
- β below the saturation bound, α ≥ 1/6, ν > 10, odd ν: not covered.
- The A_M ≥ A* step at finite M is certified only where `certify_min.py` says so; the scan is at M → ∞.
- U* = E* + C* (arcsine sums approach the equilibrium energy) is not needed for the failure direction and is not proved.

## 7. Checks of this derivation (COMPUTED; commands in README §2)

- **C1 (β = λ reproduces E13 exactly).** `check_e13.py`: R(x) at 240 rational points in [3, 240], T_out(y) at 240 points in
  (1/3, 2λ], I_out and ∫_3^20 R/x³ equal theta.py reading 'S' as exact rationals for α = k/40 (k = 1..6), s ∈ {5, 7},
  ν ∈ {2, 4, 6, 8, 10}: 60/60 PASS. Anchors through pkg_ab: I_out(5,6) = 127751/96000 (Fauzan (5.10)), Lai (103), I_out(7,8) =
  453803/288000 (audit), A_40(7,6) − A_40(5,6) = 751/768 (E14).
- **C3/C4 (Prop. 1′ and the s-step at β ≠ λ).** R = xF_β + Q at 1800 points; R_(s+2) − R_s = 2βx; Θ_40(7) − Θ_40(5) =
  2β/3 + ΔI_out = 18277/19200, 751/768, 57667/57600 at β = 17/20, 37/40, 1 (α = 3/40, ν = 6).
- **Against E29 (exact finite K, α = 3/40, ν = 6; `compare_e29.py`).** The package floor A*(7) + LB lies above the exact
  e_H(7) = log Q^prim_H/K² at all 21 tabulated (K, H), by 0.126-0.156 (K = 40), 0.057-0.076 (K = 80), 0.050-0.062 (K = 120), as
  Gauss's lemma requires in the limit. The β-minimum is β ≈ 0.875 in the package against β ≈ 0.85 exactly (K = 80, 120); the
  ζ(7) slopes in β agree in sign on both sides of the minimum and to 0.1-0.2 per unit β. **The β-slope of the s-step does not
  match**: package 0.19-0.40, exact 0.34-0.94 per unit β (K ≤ 120; the exact step is not converged in K). The package's own
  free-β gain at ν = 6 is 0.006 against the exact 0.013-0.015 (E29).
- **Certified cells.** `certify_min.py` re-derives A*(7) and LB with 113-bit interval arithmetic (certify/ code by import) at
  11 cells: all floors > 0, minimum +0.757282 at (11/80, 9/16, 8); the template cell gives +0.904376 (E33: +0.904155 with
  Fauzan's ρ as σ).
