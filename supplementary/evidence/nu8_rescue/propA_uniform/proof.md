# Proposition A, uniform leading order: γ_p^in − pΓ_(5,8)(K/p) is one of five constants

**EVENT WORK**, problem #108, thread propA-uniform. Author: **advocate:Claude Opus 5.5**. Sat Nov 14 2026, work started
08:47 PT (`TZ=America/Los_Angeles date`). **No human has checked this file.**
Files: `uniform58.py` (all code), `out/{direct,closed,pnt,compare}.{txt,json}` and the `.log` run records.

## Summary (10 lines)

1. **Need (§1, PROOF-DRAFT reduction).** E50 lowers A\* (an upper bound for limsup log m_K/K²) by 1159/28800. This needs only the one-sided (★) Σ_{K/3<p≤17K/40} (−γ_p^in) log p ≤ K²∫_{1/3}^{17/40} c_in + o(K²), c_in(y) = −yΓ_(5,8)(1/y); i.e. γ_p^in ≥ pΓ(K/p) − C uniformly, plus the PNT.
2. **Theorem U (PROOF-DRAFT, §3).** For every n ≥ 1, K = 40n, prime K/3 < p ≤ 17K/40: R := γ_p^in − pΓ_(5,8)(K/p) is exactly 15, 27/2, 19/2, 10, 9 for p/K in (1/3, 7/20), (7/20, 43/120], (43/120, 2/5), (2/5, 49/120), (49/120, 17/40].
3. Hence 9 ≤ R ≤ 15 and γ_p^in ≥ pΓ(K/p) + 9: the needed one-sided bound holds with C = 0, and the two-sided |R| ≤ 15 as well (PROOF-DRAFT).
4. **Proof (§3).** γ_p^in = Σ_types c·φ_T + E(2T − q − 4) − min(E, n_+) − 2 over 4 class types (removed or not × ℓ_K ∈ {q, q+1}); each count c differs from p × Fauzan's measure by 0, ±1/2 or ±1; the tie order is irrelevant; the zero block is exactly −2; T = ⌊2HK/p⌋ unless 3p = 49n + 1 (then T is one larger, E = 0, R = 9).
5. **COMPUTED (§4).** Exact rationals at every pair: from the definitions for n ≤ 1000 (200,647 pairs; row-by-row Fraction version at n ≤ 40), closed form for n ≤ 20000 (60,535,920 pairs): min R = 9, max R = 15, R equals the predicted constant at every pair, 0 violations.
6. **COMPUTED cross-checks.** My γ_p^in = residue58.py's (1036 pairs, n ≤ 60) = Kimi's alloc.py (59 pairs, n ≤ 12); my Γ = theta.py's −(R + N) (1036 points); ∫_{1/3}^{17/40} yR(1/y) dy = 9091/36000 = residue58's value.
7. **Sum over p (§5, PROOF-DRAFT; Dusart 2010 Thm 5.2, CITED).** c_in is continuous, increasing, affine on 5 pieces, ∫ = 3709/14400; Σ_{K/3<p≤17K/40} (−γ_p^in) log p ≤ K²·3709/14400 + 10.2K²/ln²(K/3) − 9(θ(17K/40) − θ(K/3)).
8. **S_K part (Lemma S, PROOF-DRAFT).** scal(y) = −yN(1/y) and v_p(S_K) − pN(K/p) = ⌈⌊2h/p⌋/2⌉ ∈ {2, 3} on this range, so T_new = yR(1/y) = c_in + scal and the S_K part needs nothing new.
9. **Item 4 (§6).** The summed version needs only the PNT step for the one fixed function c_in; no further uniformity statement is needed. The gain 1159/28800 is C108-LC7 and is not redone here.
10. **Open.** This addresses the gap named in Kimi's REPORT §(d) and HUMAN_CHECK addendum item 2. Still open: Proposition A's valuation half v_p(Δ_K) ≥ γ_p^in (E48), the E13 package, and a human check of this file.

---

## 1. What E50 needs, stated precisely

**Notation.** K = 40n, N = 3n, h = 37n, α = 3/40, λ = 37/40, H = 1 + 3α = 49/40, θ(t) = Σ_{p≤t} log p.

**How the gain enters.**
- `combine58.py`, `cmd_margins`, forms A\*_new = A\* − gain, with gain = ∫_{1/3}^{17/40} (T_out − yR(1/y)) dy =
  1159/28800 (COMBINED.md §2). It then requires A\*_new + U < 0.
- Here A\* = I_out + ∫_3^∞ R(x)/x³ dx, and I_out = ∫_{1/3}^{2λ} T_out(y) dy, with T_out = g + scal (theta.py, Pkg 'S').
- A\* is the constant in the arithmetic bound limsup_K log m_{K,M}/K² ≤ A_M (Fauzan, Prop. 5.2, (5.11), p. 15,
  CITED; generalised by the E13 package).
- m_{K,M} = Π_{p≤2h} p^{−L_p} (Fauzan (5.2), p. 13, CITED). By (5.1), p. 13 (CITED), L_p = v_p(S_K) + γ_p^out for
  3p > K. L_p is a lower bound for the p-adic valuations, and log m_{K,M} = Σ_p (−L_p) log p.
- So a **larger** L_p gives a **smaller** A. The gain needs lower bounds on the exponent, never upper bounds.

**The step E50 takes (PROOF-DRAFT reduction).** For K/3 < p ≤ 17K/40, use L_p := v_p(S_K) + γ_p^in. This is legitimate because
v_p(Δ_K) ≥ γ_p^in (Proposition A, first half, PROOF-DRAFT E48; not treated here). What remains is the prime-sum
estimate

(★★)  Σ_{K/3<p≤17K/40} (−v_p(S_K) − γ_p^in) log p ≤ K² ∫_{1/3}^{17/40} yR(1/y) dy + o(K²).

By Lemma S(i) (§5), yR(1/y) = −yΓ(1/y) − yN(1/y) = c_in(y) + scal(y). So (★★) follows from two estimates:

- (★) Σ_{K/3<p≤17K/40} (−γ_p^in) log p ≤ K² ∫_{1/3}^{17/40} c_in(y) dy + o(K²). **This is the new part.**
- (S) Σ_{K/3<p≤17K/40} (−v_p(S_K)) log p ≤ K² ∫_{1/3}^{17/40} scal(y) dy + o(K²). This was already inside
  T_out = g + scal. Lemma S(ii) reproves it.

**Reduction of (★).** A one-sided uniform bound γ_p^in ≥ pΓ(K/p) − C, with C absolute, turns (★) into two pieces:
- an error of C·θ(17K/40) = O(K);
- the PNT passage K Σ_p c_in(p/K) log p = K²∫c_in + o(K²), using pΓ(K/p) = −K c_in(p/K).

Equality, that is a two-sided bound, is not needed. Theorem U gives both sides anyway.

## 2. Definitions (as in derivation.md §2 and residue58.py)

n ≥ 1, K = 40n, p prime with K/3 < p ≤ 17K/40 (equivalently 40n < 3p and p ≤ 17n), m = (p − 1)/2, classes a = 1, …, m.

**Allocation.**
- ℓ_A(a) := #{1 ≤ j ≤ A : j ≡ a or j ≡ −a (mod p)} for A ∈ {K, N}, and m_A := ⌊A/p⌋.
- b_a := 4ℓ_N(a).
- T, E by division with remainder: mT + E = h − 2 + 4(N − m_N), 0 ≤ E < m.
- ε_a ∈ {0, 1}. ε_a = 1 exactly for the first E classes in the list of a = 1..m sorted by decreasing ℓ_K(a), with ties
  broken by increasing a.
- L_a := T − b_a + ε_a and Z_a := T + ε_a.

**Weights.**
- w_{a,i} := i + b_a − (ℓ_K(a) + 4)/2 for 0 ≤ i < L_a.
- w_{0,i} := min(2i − 3/2, μ) for i = 0, 1, where μ := min_{1≤c≤m} (Z_c − (ℓ_K(c) + 4)/2).
- γ_p^in := 2 (Σ_a Σ_{i<L_a} w_{a,i} + w_{0,0} + w_{0,1}).

The −3/2 is residue58's (4i + 16m_N − 2m_K + 1)/2 at m_N = 0, m_K = 2, which hold by (0b) and (0c) below.

**Γ = Γ_(5,8)** (Fauzan (5.4), p. 14, CITED, with 3ℓ(αx, z) → 4ℓ(αx, z) and H = 1 + 2α → 1 + 3α; the constant 5 = s
is unchanged, reading 'S'). For x > 0 and 0 < z < 1/2:
- ℓ(u, z) := ⌊u − z⌋ + ⌊u + z⌋ + 1 and b(x, z) := 4ℓ(αx, z);
- T_0 := ⌊2Hx⌋, s := Hx − T_0/2, q := ⌊2x⌋, n_plus := (2x − q)/2;
- Γ(x) := ∫_0^{1/2} (T_0 − b)(T_0 + b − ℓ − 5) dz + s(2T_0 − q − 5) + (s − n_plus)^+.

This is theta.py's G in `Pkg(5,8,'S').R` (R = −G − N) and residue58's −c_in(y)/y. Both identities are COMPUTED in §4.

**Derived functions.**
- c_in(y) := −yΓ(1/y).
- N(x) := 2λx⌊x⌋ − 16λx⌊αx⌋ − 2J(λx), with J(u) := ⌊2u⌋u − ⌊2u⌋(⌊2u⌋ + 1)/4.
- R(x) := −Γ(x) − N(x).

These are Fauzan (5.5)-(5.6) with 12 → 2ν = 16.

## 3. Theorem U and its proof

**Theorem U (PROOF-DRAFT).** Take n ≥ 1, K = 40n, a prime p with K/3 < p ≤ 17K/40, and put y = p/K. Then

| y | R(K, p) := γ_p^in − pΓ_(5,8)(K/p) |
|---|---|
| 1/3 < y < 7/20 | 15 |
| 7/20 < y ≤ 43/120 | 27/2 |
| 43/120 < y < 2/5 | 19/2 |
| 2/5 < y < 49/120 | 10 |
| 49/120 < y ≤ 17/40 | 9 |

No prime p gives y ∈ {7/20, 2/5, 49/120}. In particular **9 ≤ R(K, p) ≤ 15** and **γ_p^in ≥ pΓ(K/p) + 9** for every
such pair.

Throughout, x := K/p ∈ [40/17, 3), and 3p ≥ 40n + 1 because 3p > 40n are integers.

### Step 0: ranges

- **(0a)** p ≥ 17. Indeed p > 40/3, and 14, 15 and 16 are not prime.
- **(0b)** N < p/2. Indeed p > 40n/3 > 6n = 2N. Hence N ≤ m, ⌊N/p⌋ = 0 and m_N = 0.
- **(0c)** 2p < K < 3p, since p ≤ 17n < 20n and 3p > 40n. Hence m_K = 2.
- **(0d)** p ∤ K. Otherwise p | 40n, so p | n (as p ≥ 17), so p ≤ n, which contradicts p > 13n. Hence 2x = 2K/p ∉ Z.
- **(0e) q and T_0.**
  - 2x ∈ [80/17, 6), so q = ⌊2x⌋ ∈ {4, 5}. q = 5 ⟺ 5p ≤ 2K ⟺ p < 16n (16n is even, so p ≠ 16n) ⟺ y < 2/5.
  - 2Hx = 2HK/p = 98n/p ∈ [98/17, 7.35), so T_0 ∈ {5, 6, 7}.
  - T_0 = 7 ⟺ p ≤ 14n ⟺ p < 14n (14n is even).
  - T_0 = 5 ⟺ 6p > 98n ⟺ p > 49n/3.
  - 49n/3 is never prime: it is an integer only if 3 | n, and then it equals 7·(7n/3) with 7n/3 ≥ 7.
  - So: T_0 = 7 ⟺ y < 7/20; T_0 = 6 ⟺ 7/20 < y < 49/120; T_0 = 5 ⟺ y > 49/120.
  - T_0 = 7 forces p < 16n, so q = 5. T_0 = 5 forces p > 16n, so q = 4.
  - Hence (T_0, q) ∈ {(5,4), (6,4), (6,5), (7,5)}, with T_0 − q = 1 for (5,4) and (6,5), and T_0 − q = 2 for (6,4)
    and (7,5).
- **(0f)** D := N + K − 3p = 43n − 3p, and D ≥ 0 ⟺ y ≤ 43/120. If T_0 = 7, then D ≥ 43n − 42n > 0.
- **(0g) T versus T_0.**
  - Put Q := h − 2 + 4N = 49n − 2 (using m_N = 0). Then T = ⌊Q/m⌋ = ⌊2(49n − 2)/(p − 1)⌋ and E = Q − mT.
  - Q/m − 98n/p = (98n − 4p)/(p(p − 1)). This is > 0, since 4p ≤ 68n. It is < 98n/((40n/3)·16) = 294/640 < 1,
    since p > 40n/3 and p − 1 ≥ 16. So T_0 ≤ 98n/p < Q/m < T_0 + 2, and **T ∈ {T_0, T_0 + 1}**.
  - **T ≤ 7.** p − 1 ≥ (40n − 2)/3, so Q/m ≤ 6(49n − 2)/(40n − 2) < 8, because 294n − 12 < 320n − 16 ⟺ 26n > 4.
  - **Case B := {T = T_0 + 1}.** Then T_0 ≤ 6.
    - If T_0 = 6, then p ≥ 14n + 1, and T = 7 ≤ Q/m means 7(p − 1) ≤ 98n − 4, i.e. p ≤ 14n + 3/7. Contradiction.
    - So T_0 = 5 and T = 6, i.e. 6p > 98n and 6(p − 1) ≤ 98n − 4. Together: 49n < 3p ≤ 49n + 1.
    - Conversely, if **3p = 49n + 1**, then p − 1 = (49n − 2)/3 and Q/m = 6, so T = 6 and E = 0. Also
      98n/p = 294n/(49n + 1) ∈ (5, 6), so T_0 = 5.
    - So **Case B ⟺ 3p = 49n + 1, and then (T, T_0, q, E) = (6, 5, 4, 0)**.
    - Case A := {T = T_0} is everything else.
  - In both cases T ≥ 5, and T ≥ 6 when q = 5, since then T_0 ∈ {6, 7}.

### Step 1: pole counts as values of ℓ(x, z) at z = a/p

**The general formula.** Let 1 ≤ a ≤ m and A ∈ {K, N}.
- The j ≡ a (mod p) in [1, A] are a + kp with k ≥ 0. There are ⌊(A − a)/p⌋ + 1 of them; this is 0 when a > A, since
  then −p < A − a < 0.
- The j ≡ −a are kp − a with k ≥ 1. There are ⌊(A + a)/p⌋ of them.
- The two sets are disjoint, since a ≢ −a for 1 ≤ a < p/2.
- Hence **ℓ_A(a) = ℓ(A/p, a/p)**. In particular ℓ_K(a) = ℓ(x, a/p), and ℓ_N(a) = ℓ(αx, a/p) because N/p = αx.
  So b_a = b(x, a/p).

**(1i) The b-values.** αx = N/p < 1/2 by (0b). For z ∈ (0, 1/2), ⌊αx + z⌋ = 0, while ⌊αx − z⌋ = 0 if z ≤ αx and −1
otherwise. So ℓ(αx, z) = [z ≤ N/p], b(x, z) = 4[z ≤ N/p], and **b_a = 4[a ≤ N]**. The N classes a ≤ N are the
*removed* ones.

**(1ii) The ℓ-values.** Let v := K − 2p > 0. For z ∈ (0, 1/2):
- x − z ∈ (1, 3), so ⌊x − z⌋ = 2 if z ≤ x − 2 = v/p, and 1 otherwise.
- x + z ∈ (2, 3.5), so ⌊x + z⌋ = 3 if z ≥ 3 − x = (3p − K)/p, and 2 otherwise.
- Hence ℓ(x, z) = 4 + [z ≤ v/p] + [z ≥ (3p − K)/p].

Split by q:
- **q = 5 (2v > p).** Here v/p > 1/2, so the first bracket is 1, and (3p − K)/p < 1/2. So ℓ ∈ {5, 6}.
  - The high set (ℓ = 6) is z ∈ [(3p − K)/p, 1/2).
  - The high classes are 3p − K ≤ a ≤ m. Here 1 ≤ 3p − K by (0c), and 3p − K ≤ m ⟺ 5p ≤ 2K − 1, which holds since
    5p < 2K.
  - **n_+ := #high classes = K − (5p − 1)/2.**
- **q = 4 (2v < p).** Here (3p − K)/p > 1/2, so the second bracket is 0. So ℓ ∈ {4, 5}.
  - The high set (ℓ = 5) is z ∈ (0, v/p], and the high classes are 1 ≤ a ≤ v (v ≤ m).
  - **n_+ = v.**

In both cases ℓ ∈ {q, q + 1} ("low", "high"). The p-measure of the high set is **P_+ := K − qp/2 = p·n_plus**
(q = 5: p(v/p − 1/2) = K − 5p/2; q = 4: v = K − 2p). So **n_+ − P_+ = (q − 4)/2**.

### Step 2: the four class types, counts against measures

A class has a type (b_a, ℓ_K(a)) ∈ {0, 4} × {q, q + 1}. Define:
- c(b, ℓ) := the number of classes of that type;
- P(b, ℓ) := p·|{z ∈ (0, 1/2) : (b(x, z), ℓ(x, z)) = (b, ℓ)}|, the measure in Fauzan's integral times p;
- Δ := c − P.

**q = 4.** Here N < v, since v ≥ 40n − 34n = 6n > 3n. So every removed class is high.

| type | c | P | Δ |
|---|---|---|---|
| (4,5) | N | N | 0 |
| (4,4) | 0 | 0 | 0 |
| (0,5) | v − N | v − N | 0 |
| (0,4) | m − v | p/2 − v | −1/2 |

**q = 5.** The high classes are a ≥ 3p − K and the removed classes are a ≤ N. Their overlap 3p − K ≤ a ≤ N has
max(0, D + 1) elements. Its z-interval [(3p − K)/p, N/p] has p-measure max(0, D).

| type | c | P | Δ (D ≥ 0) | Δ (D ≤ −1) |
|---|---|---|---|---|
| (4,6) | max(0, D + 1) | max(0, D) | 1 | 0 |
| (4,5) | N − c(4,6) | N − P(4,6) | −1 | 0 |
| (0,6) | n_+ − c(4,6) | P_+ − P(4,6) | 1/2 − 1 = −1/2 | 1/2 |
| (0,5) | m − N − c(0,6) | p/2 − N − P(0,6) | −1/2 − Δ(0,6) = 0 | −1 |

On each region every count is affine in (n, p), and |Δ| ≤ 1. Σ Δ = m − p/2 = −1/2 in all three cases.

### Step 3: γ_p^in in terms of the counts

Put **φ_t(b, ℓ) := (t − b)(t + b − ℓ − 5)**.

**(3a) One class.** L_a ≥ T − 4 ≥ 1. Then

Σ_{i<L_a} 2w_{a,i} = Σ_{i=0}^{L_a−1} (2i + 2b_a − ℓ_a − 4) = L_a(L_a + 2b_a − ℓ_a − 5).

- If ε_a = 0, then L_a = T − b_a and the sum is φ_T(b_a, ℓ_a).
- If ε_a = 1, the sum is (T − b_a + 1)(T + b_a − ℓ_a − 4) = φ_T(b_a, ℓ_a) + (2T − ℓ_a − 4).

So **Σ_{i<L_a} 2w_{a,i} = φ_T(b_a, ℓ_a) + ε_a(2T − ℓ_a − 4)**. The extra row is worth 2T − ℓ_a − 4, independent of b_a.

**(3b) The extras.**
- The sorted order puts every high class (ℓ = q + 1) before every low one.
- So the E classes with ε = 1 are min(E, n_+) high classes and E − min(E, n_+) low classes. Which classes these are
  inside each group (the tie rule) does not matter here.
- Therefore Σ_a ε_a(2T − ℓ_a − 4) = min(E, n_+)(2T − q − 5) + (E − min(E, n_+))(2T − q − 4)
  = **E(2T − q − 4) − min(E, n_+)**.

**(3c) The zero block.**
- μ = min_c (T + ε_c − (ℓ_K(c) + 4)/2) ≥ T − (q + 5)/2 ≥ 1/2, since T ≥ 5 if q = 4 and T ≥ 6 if q = 5 (0g).
- Hence w_{0,0} = min(−3/2, μ) = −3/2 and w_{0,1} = min(1/2, μ) = 1/2, so the zero block contributes **−2**,
  whatever the order.

**(3d) Result.**

(G)  γ_p^in = Σ_{(b,ℓ)} c(b, ℓ) φ_T(b, ℓ) + E(2T − q − 4) − min(E, n_+) − 2.

### Step 4: pΓ(K/p) in terms of the measures

The integrand of (5.4) is the step function z ↦ φ_{T_0}(b(x, z), ℓ(x, z)), whose level sets are the four type sets
of Step 2. So p∫_0^{1/2} = Σ P(b, ℓ) φ_{T_0}(b, ℓ).

Put P_sl := p·s = HK − pT_0/2 = 49n − pT_0/2. Then
p[s(2T_0 − q − 5) + (s − n_plus)^+] = P_sl(2T_0 − q − 5) + (P_sl − P_+)^+ = P_sl(2T_0 − q − 4) − min(P_sl, P_+).

(P)  pΓ(K/p) = Σ_{(b,ℓ)} P(b, ℓ) φ_{T_0}(b, ℓ) + P_sl(2T_0 − q − 4) − min(P_sl, P_+).

**Key identity.**

(K)  P_sl − P_+ = (49n − pT_0/2) − (40n − qp/2) = 9n − p(T_0 − q)/2.

- If T_0 − q = 1: P_sl − P_+ = (18n − p)/2 ≥ n/2 > 0.
- If T_0 − q = 2: P_sl − P_+ = 9n − p < 0.

### Step 5: Case A (T = T_0)

Subtract (P) from (G):

R = S_Δ + (E − P_sl)(2T − q − 4) − [min(E, n_+) − min(P_sl, P_+)] − 2, where S_Δ := Σ Δ(b, ℓ) φ_T(b, ℓ).

**(5a)** E − P_sl = (49n − 2 − mT) − (49n − pT/2) = −2 + T(p/2 − m) = **(T − 4)/2**.

**(5b) The bracket.** From (5a) and Step 1, E − n_+ = (P_sl − P_+) + (T − q)/2 = 9n − m(T − q), using (K) and
p − 1 = 2m.
- **T − q = 1.** E − n_+ = 9n − m > 0, since m ≤ (17n − 1)/2. And P_sl > P_+. So the bracket is
  n_+ − P_+ = **(q − 4)/2**.
- **T − q = 2.** E − n_+ = 9n + 1 − p ≤ 0, since p > 40n/3 ≥ 9n + 1. And P_sl < P_+. So the bracket is
  E − P_sl = **(T − 4)/2**.

**(5c) S_Δ, from the Δ tables.**
- q = 4: −φ_T(0, 4)/2 = −T(T − 9)/2.
- q = 5, D ≥ 0: φ_T(4,6) − φ_T(4,5) − φ_T(0,6)/2 = (T − 4)(T − 7) − (T − 4)(T − 6) − T(T − 11)/2
  = −(T − 4) − T(T − 11)/2.
- q = 5, D ≤ −1: φ_T(0,6)/2 − φ_T(0,5) = T(T − 11)/2 − T(T − 10) = T(9 − T)/2.

**(5d) The values.** R = S_Δ + ((T − 4)/2)(2T − q − 4) − bracket − 2:

| (T, q), sign of D | region (by (0e), (0f)) | S_Δ | ((T−4)/2)(2T−q−4) | bracket | R |
|---|---|---|---|---|---|
| (5, 4) | y > 49/120 | 10 | 1 | 0 | **9** |
| (6, 4) | 2/5 < y < 49/120 | 9 | 4 | 1 | **10** |
| (6, 5), D ≤ −1 | 43/120 < y < 2/5 | 9 | 3 | 1/2 | **19/2** |
| (6, 5), D ≥ 0 | 7/20 < y ≤ 43/120 | 13 | 3 | 1/2 | **27/2** |
| (7, 5), D > 0 by (0f) | y < 7/20 | 11 | 15/2 | 3/2 | **15** |

### Step 6: Case B (3p = 49n + 1; T = 6, T_0 = 5, q = 4, E = 0)

1. **The measure side.**
   - 49n = 3p − 1, so P_sl = 49n − 5p/2 = p/2 − 1.
   - By (K) with T_0 − q = 1, P_sl > P_+, so min(P_sl, P_+) = P_+.
   - (P) gives pΓ = Σ P φ_5 + 2P_sl − P_+.
2. **Moving from φ_5 to φ_6.**
   - φ_6 − φ_5 = 2·5 − ℓ − 4 = 6 − ℓ.
   - Σ P = p/2 and Σ P·ℓ = 4·p/2 + P_+.
   - So Σ P φ_5 = Σ P φ_6 − (3p − 2p − P_+) = Σ P φ_6 − p + P_+.
   - Hence pΓ = Σ P φ_6 − p + P_+ + (p − 2) − P_+ = Σ P φ_6 − 2.
3. **The count side.** (G) with E = 0 gives γ_p^in = Σ c φ_6 − 2.
4. **Result.** R = Σ Δ φ_6 = −6(6 − 9)/2 = **9**. Here y = (49n + 1)/(120n) > 49/120, as the theorem states.

### Step 7: assembling the regions

- By (0g), every case with T_0 ∈ {6, 7} is Case A.
- By (0e) and (0f), the five Case-A rows of (5d) correspond exactly to the five y-intervals of the theorem.
- Case B lies in y > 49/120, where R = 9 as well.
- y = 43/120 occurs only at (K, p) = (120, 43) (3p = 43n with p prime forces n = 3). There D = 0 and R = 27/2,
  as the table says. ∎

**Remarks.**
- (i) R is constant exactly on the five pieces on which c_in is affine (§5). Both sides of R come from the same type
  decomposition, and on each piece every count differs from its measure by a fixed constant.
- (ii) This is Fauzan's sketch of (5.7) (p. 14, CITED), made explicit for (5, 8) on 40/17 ≤ x < 3. Fauzan's sketch
  has three parts:
  - grid points versus lengths times p;
  - the change of the number of allocated rows from p/2 to (p − 1)/2;
  - the transition when 2Hx crosses an integer.

  Here they become Step 2, (5a), and Step 6 together with (0g). The reading is mine; the method is Fauzan's.
- (iii) The derivation's two uses of "K large" are not needed here: Theorem U holds for every n ≥ 1.

## 4. COMPUTED check (`uniform58.py`; exact `Fraction` arithmetic; every pair)

| check | range | pairs | result |
|---|---|---|---|
| γ_p^in from the definitions (int64; ℓ by the Step 1 floor formula, rows by the arithmetic series), pΓ by integrating (5.4) over all cut points | n = 1..1000 (K ≤ 40000) | 200,647 | min R = 9 at (40, 17); max R = 15 at (120, 41); **R = ρ(p/K) at every pair; 0 violations of 9 ≤ R ≤ 15**. Distribution 9: 36100, 19/2: 91166, 10: 18186, 27/2: 18319, 15: 36876 (`out/direct.txt`) |
| literal implementation: ℓ by enumerating j ≤ K, each row weight as a Fraction | n ≤ 40 | 494 | identical to the int64 version (assert) |
| closed form of §3 ((G), (P), Δ tables), equal to the direct computation | n ≤ 500 | 54,115 | identical at every pair (assert) |
| closed form | n ≤ 20000 (K ≤ 800,000) | 60,535,920 | min R = 9, max R = 15; **R = ρ(p/K) at every pair; 0 violations**. Per case: A(5,4) 10,931,350 pairs, all R = 9; A(6,4) 5,477,157, all 10; A(6,5,D≤−1) 27,486,623, all 19/2; A(6,5,D≥0) 5,535,585, all 27/2; A(7,5) 11,104,531, all 15; B 674, all 9 (`out/closed.txt`, about 7 min) |
| Case B ⟺ 3p = 49n + 1 | n ≤ 20000 | same | 0 exceptions in either direction (674 Case-B pairs, the first at (320, 131)) |

**Comparisons**, run only after my code had run (`out/compare.txt`):
- residue58.py `inner_alloc_bound(K, N, h, p, L0=2)` equals my γ_p^in at 1036/1036 pairs (n ≤ 60). Its `best_inner`
  picks L_0 = 2 at all of them.
- theta.py's −(R(x) + N(x)) equals my Γ(x) at all 1036 points x = K/p.
- Kimi's alloc.py `alloc(K, p)['gamma']` equals my γ_p^in at 59/59 pairs (n ≤ 12).
- My γ_p^in at the 14 pairs with K ≤ 200 equals the "inner-alloc bound" column of
  `derive_fauzan-residue/out/check.txt`.
- My pΓ(K/p) equals its K·c_in column, so R there is 9 to 15, as the HUMAN_CHECK addendum reports.

**Reproduce** (from this folder; one process each):
- `python3 -B uniform58.py direct 1000` (about 35 s);
- `python3 -B uniform58.py closed 20000` (about 7 min);
- `python3 -B uniform58.py pnt` (about 25 s);
- `python3 -B uniform58.py compare 60` (about 2 min). This imports residue58.py, theta.py and Kimi's alloc.py
  read-only.

Each command writes `out/<cmd>.txt` and `out/<cmd>.json`. The `out/*.log` files are the timed runs.

## 5. From primes to the integral, and the S_K part

**Lemma P (pieces of c_in; COMPUTED).** On [1/3, 17/40], with c_in(1/3) taken as the
right-hand limit, c_in(y) = −yΓ(1/y) is:

| piece | c_in(y) |
|---|---|
| [1/3, 7/20] | −4 + 19y |
| [7/20, 43/120] | −111/40 + (31/2)y |
| [43/120, 2/5] | 61/40 + (7/2)y |
| [2/5, 49/120] | 21/40 + 6y |
| [49/120, 17/40] | 7/4 + 3y |

The pieces agree at the joins, so c_in is continuous. It is increasing, with c_in(1/3+) = 7/3,
c_in(17/40) = 121/40 and total variation 83/120. ∫_{1/3}^{17/40} c_in = **3709/14400**.

*Why the pieces are affine (PROOF-DRAFT).* On each piece, for real x = 1/y:
- T_0, q, ⌊x⌋ = 2, ⌊αx⌋ = 0 and the order of the cut points αx, x − 2, 3 − x in (0, 1/2) are fixed.
- The level-set measures in (5.4) are then affine in x, and so are s and n_plus.
- The sign of s − n_plus is fixed: it equals the sign of (2H − 2)x − (T_0 − q) = (9/20)x − (T_0 − q). This is
  positive on the pieces with T_0 − q = 1 (x ≥ 40/17 > 20/9) and negative on those with T_0 − q = 2 (x < 3 < 40/9).
- So Γ = A + Bx on each piece, and c_in(y) = −Ay − B.

*Coefficients.* COMPUTED: exact affine fit through two points, checked at 41 interior points per piece and at the
joins (`out/pnt.txt`). One piece by hand: on y > 49/120, (P) gives
pΓ = −N − 25(v − N) − 20(p/2 − v) + 2(49n − 5p/2) − (K − 2p) = −70n − 3p, so c_in = (70n + 3p)/(40n) = 7/4 + 3y.

**Lemma PS (partial summation; PROOF-DRAFT).** Let 0 < a < b and let f be continuous on [a, b] with total variation V.
Put e(t) := θ(t) − t, X = aK and Y = bK. Then

|Σ_{X<p≤Y} f(p/K) log p − K∫_a^b f(y) dy| ≤ (|f(a)| + |f(b)| + V)·sup_{X≤t≤Y} |e(t)|.

*Proof.*
1. θ is a right-continuous step function, and f is continuous. So the Riemann–Stieltjes integral gives
   Σ_{X<p≤Y} f(p/K) log p = ∫_X^Y f(t/K) dθ(t).
2. Integrating by parts, this is f(b)θ(Y) − f(a)θ(X) − ∫_X^Y θ(t) d[f(t/K)].
3. The same identity with θ(t) replaced by t gives ∫_X^Y f(t/K) dt = K∫_a^b f.
4. Subtracting leaves f(b)e(Y) − f(a)e(X) − ∫ e d[f(t/K)]. The last term is at most sup|e|·V in absolute value. ∎

**Dusart (CITED).** |θ(x) − x| < 3.965·x/ln²x for x ≥ 2. This is Dusart, arXiv:1002.0442v1, Theorem 5.2, p. 4, the
table column k = 2, η_k = 3.965, x_k = 2. I read it on the rendered page image. For K ≥ 6 and t ∈ [K/3, 17K/40] this
gives |e(t)| ≤ 3.965·(17K/40)/ln²(K/3).

**Corollary U2 (what E50 uses; PROOF-DRAFT).** For every K ∈ 40Z_{>0}:

*[Erratum, orchestrator (Claude Opus 5.5), Sat 10:37 PT: the constant was printed 10.195. The exact product is (121/20)·3.965·(17/40) = 10.19500625, so 10.195 is too small by 1/160000 and the inequalities as printed did not follow. Both the Claude verifier (propA_uniform/verify/) and skeptic 13 (Kimi K3.1 Pro, evidence/skeptic13-kimi/) found this. It is corrected to 10.1951 in the three places below; nothing else changes, since the error term is o(K²) for any fixed constant.]*

Σ_{K/3<p≤17K/40} (−γ_p^in) log p ≤ K²·(3709/14400) + 10.1951·K²/ln²(K/3) − 9(θ(17K/40) − θ(K/3)).

The two-sided form is |Σ γ_p^in log p + K²·3709/14400| ≤ 10.1951 K²/ln²(K/3) + 15θ(17K/40). So (★) holds, and so does
the equality form "Σ_p γ_p^in log p = −K²∫c_in + o(K²)".

*Proof.*
1. −γ_p^in = K c_in(p/K) − R(K, p) ≤ K c_in(p/K) − 9, by Theorem U and −pΓ(K/p) = K c_in(p/K).
2. Multiply by log p and sum over the range.
3. Apply Lemma PS with f = c_in, a = 1/3, b = 17/40, so |f(a)| + |f(b)| + V = 7/3 + 121/40 + 83/120 = 121/20, then
   use Dusart. This bounds the remaining error by (121/20)·3.965·(17/40)·K²/ln²(K/3) ≤ 10.1951 K²/ln²(K/3).
4. No prime equals K/3, so the boundary value f(1/3+) is never sampled. ∎

The bound is asymptotic; it is not useful at small K. COMPUTED illustration (`out/pnt.txt`): (1/K²)·K Σ c_in(p/K) log p
− ∫c_in = −0.0026, −0.0019 and −0.0001 at K = 4·10⁴, 4·10⁵ and 4·10⁶.

**Lemma S (PROOF-DRAFT).**

(i) For y ∈ (1/3, 17/40], **scal(y) = −yN(1/y) = 4λ − 10y + (2λ − 5y)^+**.

*Proof.*
1. Put x = 1/y ∈ [40/17, 3). Then ⌊x⌋ = 2 and ⌊αx⌋ = 0. Let u = λx; then 2u = 2λ/y ∈ [74/17, 5.55), so
   m_u := ⌊2u⌋ ∈ {4, 5}.
2. −yN(1/y) = −4λ + 2y(m_uλ/y − m_u(m_u + 1)/4) = −4λ + Σ_{j=1}^{m_u} (2λ − jy).
3. scal(y) = −2λ⌊1/y⌋ + Σ_{j=1}^{6} (2λ − jy)^+. The term (2λ − jy)^+ equals 2λ − jy for j ≤ m_u and 0 for
   j > m_u, and m_u ≤ 5 < 6. So scal(y) is the same sum.
4. With m_u ∈ {4, 5} the sum is 8λ − 10y + (2λ − 5y)^+. ∎

COMPUTED: residue58 checked (i) at 999 points; I checked both forms at 997 exact points of (1/3, 17/40].
∫_{1/3}^{17/40} scal = −121/24000.

(ii) For K/3 < p ≤ 17K/40, **v_p(S_K) − pN(K/p) = ⌈m_h/2⌉ ∈ {2, 3}**, where m_h := ⌊2h/p⌋ ∈ {4, 5}. This rests on
Legendre's formula (5.3) (Fauzan p. 13, CITED for ν = 6). E13 generalises it to ν = 8, which changes only the
coefficient of the ⌊N/p^a⌋ terms; those terms vanish here because N < p.

*Proof.*
1. p² > 1600n²/9 > 74n = 2h > K, so every a ≥ 2 term vanishes. Also ⌊K/p⌋ = 2, ⌊N/p⌋ = 0 and v_p(4) = 0 (p odd).
   So v_p(S_K) = 4h − 2Σ_{i=1}^{h−1} ⌊2i/p⌋.
2. Σ_{i<h} ⌊2i/p⌋ = Σ_{j≥1} #{i < h : 2i ≥ jp} = Σ_{j=1}^{m_h} (h − ⌈jp/2⌉).
3. pN(K/p) = 4h − 2pJ(h/p), using λK/p = h/p and ⌊αK/p⌋ = 0. And pJ(h/p) = Σ_{j=1}^{m_h} (h − jp/2).
4. So the difference is 2Σ_{j≤m_h} (⌈jp/2⌉ − jp/2) = #{odd j ≤ m_h} = ⌈m_h/2⌉.
5. 74n/p ∈ [74/17, 5.55), so m_h ∈ {4, 5}. ∎

COMPUTED: the difference lies in [2, 3] at all 54,115 pairs with n ≤ 500.

So −v_p(S_K) = K·scal(p/K) − ⌈m_h/2⌉ ≤ K·scal(p/K), and (S) follows by Lemma PS (scal is continuous, affine on two
pieces). As a consistency check, ∫_{1/3}^{17/40} yR(1/y) dy = ∫c_in + ∫scal = 3709/14400 − 121/24000 = **9091/36000**.
This is exactly the value printed by `derive_fauzan-residue/out/integral.txt`, which combine58 uses (COMPUTED).

## 6. Item 4: does the summed version need its own uniform statement?

**Answer.** No new uniformity. The summed estimate (★) is what E50 uses. Given Theorem U, which is pointwise and
uniform with R ≥ 9 > 0, (★) needs only the passage from primes to the integral for one fixed function c_in, which does
not depend on K. Corollary U2 provides it with an explicit error. Fauzan's own proof of Prop. 5.2 (p. 15, CITED)
handles his inner range the same way: (5.7), then partial summation and the PNT.

**The S_K part.** It needs nothing new. It was already in T_out = g + scal, and Lemma S(ii) shows it is also uniform
(error 2 or 3) on this range.

**The values of the integrals** are separate exact computations:
- the gain 1159/28800, C108-LC7, Lean-checked, not redone here;
- ∫c_in = 3709/14400 and ∫yR(1/y) = 9091/36000, here, COMPUTED, matching residue58.

**Finite M.** E50's finite-M margins, for example at M = 2000, are limsup statements in K for fixed M. Corollary U2
applies unchanged.

## 7. What this does not show, and credits

**What this does not show.**
- The valuation half of Proposition A, v_p(Δ_K) ≥ γ_p^in, is not touched. It is still PROOF-DRAFT (E48), and inherits
  Fauzan's Lemmas 3.1-3.2.
- The E13 package (T_out, scal, the inner range) and the analytic side U are not touched.
- No human has checked Theorem U, Corollary U2 or Lemma S. Under the AGENTS.md §2 reporting rules they are reported as
  CONJECTURE until a human reads them. The written proofs are §3 and §5; the computed range is in §4.

**Credits.**
- Fauzan, "ζ(5) is irrational", Zenodo 22826419 v1: (5.1)-(5.7), Prop. 5.2 and its proof, pp. 13-15. The proof plan
  is his sketch of (5.7).
- Dusart, arXiv:1002.0442v1, Thm 5.2, p. 4.
- The team's derivation.md §2 (E48) and residue58.py: the definitions. theta.py (E13): Γ, N, scal.
- combine58.py and COMBINED.md: how the gain enters.
- Kimi K3.1 Pro: alloc.py and REPORT §(d), which named this gap. HUMAN_CHECK.md addendum, item 2.
- No novelty is claimed.

advocate:Claude Opus 5.5
