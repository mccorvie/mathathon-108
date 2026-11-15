# Statement comparison: the arithmetic for symbolic odd s (E300, E302/E310, E303, E305, E311)

Statement comparison by Claude Fable 5.2 (subagent of the integrator); author of the Lean: Codex (GPT family), adapting mo271/Zeta5 by Moritz Firsching; Sat Nov 14, 20:05 PT. Statements only: no proof was read, nothing was built, not checked by a human.

Labels are those of `AGENTS.md` §2. The Lean declarations stay LEAN-CHECKED until the integrator applies §2's three conditions; this file is condition (3) only. Conditions (1) (the `--final` gate in the submitted project) and (2) (statement printed in the report) were not checked here. Every remark of mine about what a statement says is a reading of source text; where I computed something it is marked COMPUTED and the code is in §8.

## 0. What was compared, and with what

- Sheets: `evidence/L-human-check/SHEET.md`, `evidence/L-sharp-outer/SHEET.md`, `evidence/L-sharp-normalization/SHEET.md`. (`evidence/L-unified-full-bridge/SHEET.md` holds only three margin corollaries of lane B and their target definitions; none of this group's declarations is printed there. **`FREEZE_BRIEF.md` says that sheet "lists all 495 declarations": it does not; the list is `evidence/L-unified-lean/DECLARATIONS.md`,** where all 17 declarations below appear once each.)
- Source: `evidence/L-unified-lean/Zeta5S/` (47 files, 8129 lines; imports are `Mathlib` and sibling `Zeta5S.*` files only). COMPUTED: `evidence/C-zeta5-compact/Zeta5S/` is byte-identical file by file, except that it lacks `Distribution.lean` (so `tauS_distribution` is not in lane C's copy).
- COMPUTED: all 55 "VERBATIM file:lines" definition blocks of `L-human-check/SHEET.md` equal the source at the stated lines (script in §8). The definitions printed in the two sharp sheets equal the source lines cited below (read by eye).
- COMPUTED: `grep -nE "\bsorry\b|^\s*axiom |native_decide|bv_decide|admit\b|implemented_by|unsafe "` over `L-unified-lean/Zeta5S/*.lean` finds one hit, a comment (`AssemblyData.lean:15`, "No sorry or axiom is declared"). No custom `notation`, `macro` or `syntax` in these files.
- Gate records read, not re-run: `evidence/L-unified-lean/log/LEAN_CHECK.md` has PASS with axioms `propext, Classical.choice, Quot.sound` for each headline declaration (v4.33.1).
- Upstream: `evidence/zeta5_repo/upstream-be1c0d82/Apery/Arith/` and the copies of upstream's `Apery/Norm.lean` (`evidence/L-assembly-statement/source/Norm.lean`) and `Apery/Construction.lean` (`evidence/L-unified-lean/Apery/Construction.lean`).
- Claim texts: `FREEZE_BRIEF.md` row 1; `evidence/integrator-report-inputs/blocks/claims_table.tex` row 1; `blocks/lean_declarations.tex` D1 to D4; intended mathematics `evidence/criterion5/derivation.md` §1-5, §8.

## 1. Verdicts

| Id | Declaration (all are `theorem`s; file:line in `L-unified-lean/Zeta5S/`) | Verdict |
|---|---|---|
| E311 | `AperyS.AssemblyTarget.normalization_sharp_statement` (`SharpAssembly.lean:138`) | match with the stated differences |
| E311 | `AperyS.AssemblyTarget.local_valuation_sharp` (`SharpAssembly.lean:45`) | match with the stated differences (stronger than the claim) |
| E311 | `AperyS.AssemblyTarget.normalizerSharp_pos` (`:58`), `normalizerSharp_le_raw` (`:66`) | match |
| E303 | `AperyS.AssemblyTarget.local_valuation_statement` (`AssemblyProof.lean:80`), `local_valuation` (`:67`) | match with the stated differences |
| E305 | `AperyS.AssemblyTarget.normalization_statement` (`NormalizationProof.lean:164`), `normalization` (`:130`), `normalizer_pos` (`:19`) | match with the stated differences |
| E300 | `AperyS.tauXs_direct` (`DirectPoly.lean:280`) | match with the stated differences |
| E300 | `AperyS.tauS_distribution` (`Distribution.lean:67`) | match |
| E302 | `AperyS.outer_boundS_clamped` (`OuterScope.lean:70`) | match with the stated differences |
| E302 | `AperyS.determinant_integral_above_K` (`OuterScope.lean:86`) | match (a statement about Δ, not F) |
| E310 | `AperyS.det_lowrank_zero_bound` (`SharpLowRank.lean:58`) | match with the stated differences |
| E310 | `AperyS.outer_boundS_sharp_clamped` (`SharpOuterScope.lean:13`) | match with the stated differences |
| E310 | `AperyS.AssemblyTarget.WO_le_WOsharp` (`SharpOuterScope.lean:40`), `GV_FS_outer_sharp` (`:53`) | match |

No mismatch found. No vacuity found. Five findings that the report must carry are in §5 (F1 to F5).

## 2. The objects, unfolded to Mathlib

`ℚ[X]` is `Polynomial ℚ`; `C` the constant embedding; `/ₘ` Mathlib's quotient by a monic polynomial; `bernoulli` Mathlib's Bernoulli numbers (B₁ = −1/2); `padicValRat p q : ℤ` the p-adic valuation of a rational, with Mathlib's junk value 0 at q = 0; `Nat.log p x` = ⌊log_p x⌋; natural-number `-` and `/` truncate.

### 2.1 Valuation predicates
```lean
-- Val.lean:22
def VG (p : ℕ) (q : ℚ) (r : ℚ) : Prop := q = 0 ∨ r ≤ (padicValRat p q : ℚ)
-- Val.lean:152
def GV (p : ℕ) (f : ℚ[X]) (r : ℚ) : Prop := ∀ n, VG p (f.coeff n) r
```
`GV p f r` says: every **nonzero** coefficient of f has p-adic valuation ≥ r. The junk value `padicValRat p 0 = 0` cannot leak, because a zero coefficient is handled by the left disjunct. Consequence: `GV p 0 r` holds for every r.

### 2.2 The functional, the determinant, F
```lean
-- Base.lean:12
noncomputable def D (m : ℕ) : ℚ[X] := ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2))
-- Monomial.lean:58-60
def μmonoS (s e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) *
    (((2 * e + s).factorial : ℚ) / ((2 * e + 2).factorial : ℚ)) / ((s - 1).factorial : ℚ)
-- Monomial.lean:64
noncomputable def μpolyS (s : ℕ) (P : ℚ[X]) : ℚ := P.sum fun e c => c * μmonoS s e
-- PoleFun.lean:55
def Hs (s j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, 1 / (v : ℚ) ^ s
-- Pullback.lean:247-248
noncomputable def poleValueS (s j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ (s - 1)) * (X - C (Hs s j)) - C (1 / ((s : ℚ) - 1)) + C (1 / (2 * (j : ℚ)))
-- Pullback.lean:252-255
noncomputable def μXS (s K : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (μpolyS s (P /ₘ D K)) +
    ∑ j ∈ Icc 1 K,
      C (P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)) * poleValueS s j
-- BasisChange.lean:90-91, 94
noncomputable def GS (s ν K N h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => μXS s K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ)))
noncomputable def ΔS (s ν K N h : ℕ) : ℚ[X] := (GS s ν K N h).det
-- SmallPrimeF.lean:212-214, 217
noncomputable def SS (ν K N h : ℕ) : ℚ :=
  (K.factorial : ℚ) ^ (2 * h) * 4 ^ (h - 1) /
    ((N.factorial : ℚ) ^ (2 * ν * h) * ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2)
noncomputable def FS (s ν K N h : ℕ) : ℚ[X] := C (SS ν K N h) * ΔS s ν K N h
```
In mathematics. D_m(t) = ∏_{j=1}^m (t + j²). The linear functional μ_X is **formal**: on a monomial, μ(t^e) = (−1)^e B_{2e+2} (2e+s)! / ((2e+2)! (s−1)!); on a simple pole, μ_X(1/(t+j²)) = j^{s−1}(X − H_j^{(s)}) − 1/(s−1) + 1/(2j), a polynomial of degree 1 in an indeterminate X (X stands for ζ(s), but no theorem of this group says so). `μXS s K P` is μ_X(P(t)/D_K(t)), computed as (polynomial quotient) + Σ_j (residue at t = −j²)·(pole value). `GS` is the h×h Hankel matrix with entries μ_X(D_N(t)^ν t^{i+j} / D_K(t)), 0 ≤ i, j < h; Δ its determinant, in ℚ[X]; S = (K!)^{2h} 4^{h−1} / ((N!)^{2νh} ∏_{i=1}^{h−1} ((2i)!)²) > 0; **F = S·Δ ∈ ℚ[X]**. Every statement below takes h = K − N. These agree with `derivation.md` §0 and (s1). In `GS`, the `X` inside `μXS`'s argument is the variable t of the numerator; the `X` of the result is the ζ-indeterminate.

### 2.3 Classes, inner weights
```lean
-- ClassCount.lean:27-28 (context: {p : ℕ} [Fact p.Prime] {m : ℕ})
def ccls (hm : 2 * m + 1 = p) (c : ZMod p) : Fin (m + 1) :=
  if h : c.val ≤ m then ⟨c.val, by omega⟩ else ⟨p - c.val, by have := c.val_lt; omega⟩
-- ClassCount.lean:99-101
def SX (p X : ℕ) (c : ZMod p) : ℕ :=
  ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = c).card +
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = -c).card
-- ClassCount.lean:115-117
noncomputable def BseS (s ν : ℕ) (p K N : ℕ) (a : ℕ) : ℚ :=
  (if a = 0 then (s : ℚ) else 0) + (ν : ℚ) * (SX p N (((a : ℤ) : ZMod p)) : ℚ) -
    SX p K (((a : ℤ) : ZMod p))
-- InnerWeights.lean:25-26, 30-31, 133-134, 138-140 (context: {m : ℕ})
noncomputable def topwS (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (a : Fin (m + 1)) : ℚ :=
  L a + (b a - ℓ) / 2
noncomputable def tminS (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) : ℚ :=
  (Finset.univ.erase (0 : Fin (m + 1))).inf' ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩ (topwS ℓ L b)
noncomputable def wrawS (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - ℓ) / 2 else (s.2 : ℚ) + (b s.1 - ℓ) / 2
noncomputable def wcapS (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  min (wrawS ℓ L b s) (tminS ℓ hm L b)
-- Pullback.lean:86-87
def PlK (K : ℕ) : Finset ℤ :=
  (Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))
-- DirectBound.lean:152-153
def Sep (p : ℕ) (Pl : Finset ℤ) : Prop :=
  ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬ (p : ℤ) ^ 2 ∣ r - s
```
In mathematics, with m = (p−1)/2 and classes a ∈ {0, …, m} (a stands for ±a mod p): S_X(a) = #{1 ≤ j ≤ X : j ≡ a} + #{1 ≤ j ≤ X : j ≡ −a} (class 0 is counted twice); b_a = s·[a = 0] + ν S_N(a) − S_K(a). With loss ℓ = s − 1 and an allocation L (L(a) rows for class a): raw weight of row (a, i) is i + (b_a − ℓ)/2 for a ≠ 0 and 2i + (b_0 − ℓ)/2 for a = 0; the cap is t_min = min_{a ≠ 0} (L(a) + (b_a − ℓ)/2); the weight is min(raw, t_min). This is `derivation.md` (2.1) with ν/2 and s − 1 in place of 3 and 4.

### 2.4 Outer weights, rank, zero count
```lean
-- OuterBasis.lean:25, 51, 54, 57, 60, 63 (context: {p} [Fact p.Prime] {m}; (hm : 2 * m + 1 = p) (σ ν N K : ℕ))
def jc (hm : 2 * m + 1 = p) (j : ℕ) : Fin (m + 1) := ccls hm (((j : ℤ) : ZMod p))
def tailO (N K : ℕ) : Finset ℕ := Icc (N + 1) (K)
def tailC (c : Fin (m + 1)) : Finset ℕ := (tailO N K).filter fun j => jc hm j = c
def LoC (c : Fin (m + 1)) : ℕ := (tailC hm N K c).card
def bigC (c : Fin (m + 1)) : Finset ℕ := (tailC hm N K c).filter fun j => p < j
def nbC (c : Fin (m + 1)) : ℕ := (bigC hm N K c).card
-- OuterEntryMain.lean:97, 101, 105-107
def ellC (c : Fin (m + 1)) : ℕ := ((Icc 1 (K)).filter fun j => jc hm j = c).card
def delC (c : Fin (m + 1)) : ℕ := if (c : ℕ) ≤ N then 1 else 0
noncomputable def wO (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  if c = 0 then (if i < nbC hm N K 0 then -2 else if nbC hm N K 0 = 0 then -1 / 2 else 0)
  else (if i < nbC hm N K c then min 0 ((i : ℚ) + ((ν : ℚ) / 2) * delC N c - ((ellC hm K c : ℚ) + ((σ : ℚ) - 1)) / 2) else 0)
-- OuterScope.lean:14
def momentCutS (s p : ℕ) : ℕ := ((s - 1) / 2) * (p - 1) - 1
-- OuterFiniteStep.lean:83-84
def rawRank (s ν K N p : ℕ) : ℕ :=
  min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1))
-- SharpLowRank.lean:14-15
noncomputable def zeroWeightCount {h : ℕ} (w : Fin h → ℚ) : ℕ :=
  (Finset.univ.filter fun s => w s = 0).card
-- SharpOuterWeights.lean:41-42
noncomputable def outerZeroCount (hm : 2 * m + 1 = p) (s ν N K : ℕ) : ℕ :=
  ∑ c, ((range (LoC hm N K c)).filter fun i => wO hm s ν N K c i = 0).card
```
In mathematics: class c gets `LoC(c)` = #{N < j ≤ K : j ≡ ±c} rows (they add up to h = K − N); ℓ(c) = #{1 ≤ j ≤ K : j ≡ ±c}; δ(c) = [c ≤ N]; n_b(c) = #{N < j ≤ K : j ≡ ±c, j > p}. For c ≠ 0 the weight of row i is min(0, i + (ν/2)δ(c) − (ℓ(c) + s − 1)/2) if i < n_b(c), and 0 otherwise: `derivation.md` §3. **Class 0 is special and does not depend on s or ν:** −2 for i < n_b(0); otherwise −1/2 if n_b(0) = 0, else 0. `rawRank` = min(h, max(0, K + (ν−2)N − ((s−1)/2)(p−1))): the truncated subtraction is the positive part, as intended (the clamp r̂ of the derivation). It is an **upper bound used for the rank** of the moment correction, not the rank itself. `outerZeroCount` = the number of rows (c, i) whose table weight is exactly 0.

### 2.5 The assembly
```lean
-- AssemblyData.lean:24, 26, 28-30, 32, 34-40, 42-46, 48-49, 51-59, 61-68, 72, 74-76
abbrev Allocations := (p : ℕ) → Fin (p / 2 + 1) → ℕ
def degreeBound (s ν K N : ℕ) : ℕ := s + 2 * (ν * N) + 4 * ((K - N) - 1)
def Lsmall (s ν K N p : ℕ) : ℤ :=
  -(((s + 1 : ℕ) : ℤ) * (K - N : ℕ) * Nat.log p (degreeBound s ν K N + 1) +
    (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℤ))
def vSK (ν K N p : ℕ) : ℤ := padicValRat p (SS ν K N (K - N))
def InnerOK (s ν K N p : ℕ) (L : Allocations) : Prop :=
  ∃ hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2,
    s ≤ p ∧ Sep p (PlK K) ∧ K < p ^ 2 ∧
    s + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2 ∧
    ∑ c, L p c = K - N ∧
    tminS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) ≤
      2 * (L p 0 : ℚ) + (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2
def WI (s ν K N p : ℕ) (L : Allocations) : ℚ := by
  classical
  exact if hm1 : 1 ≤ p / 2 then
    ∑ x, wcapS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) x
  else 0
def OuterOK (s K N p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ s ≤ p ∧ 7 ≤ p ∧ K < 3 * p ∧ 2 * K < p ^ 2 ∧ N < p
def WO (s ν K N p : ℕ) : ℚ := by
  classical
  exact if hpp : p.Prime then
    letI : Fact p.Prime := ⟨hpp⟩
    if hm : 2 * (p / 2) + 1 = p then
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1)) : ℕ) : ℚ)
    else 0
  else 0
def Lp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WO s ν K N p⌋
  else Lsmall s ν K N p
def primeBound (s K N : ℕ) : ℕ := max 7 (max s (2 * (K - N)))
def normalizer (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-Lp s ν K N M p L)
-- SharpOuterScope.lean:30-38
noncomputable def WOsharp (s ν K N p : ℕ) : ℚ := by
  classical
  exact if hpp : p.Prime then
    letI : Fact p.Prime := ⟨hpp⟩
    if hm : 2 * (p / 2) + 1 = p then
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (rawRank s ν K N p) (outerZeroCount hm s ν N K) : ℕ) : ℚ)
    else 0
  else 0
-- SharpAssembly.lean:15-22, 24-26
def LpSharp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WOsharp s ν K N p⌋
  else Lsmall s ν K N p
def normalizerSharp (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-LpSharp s ν K N M p L)
```
In mathematics, with h = K − N. An allocation L gives, for each p, a vector (L_p(a))_{0 ≤ a ≤ ⌊p/2⌋} of natural numbers. The selected exponent at a prime p:

- **small** (pM ≤ K): L_small = −[(s+1)·h·⌊log_p(s + 2νN + 4(h−1) + 1)⌋ + h·v_p((s−1)!)];
- **inner** (K/M < p ≤ K/3): v_p(S) + ⌊2 W_I⌋ if `InnerOK` holds, else L_small. `InnerOK`: p odd, p ≥ 3, p ≥ s, no two of ±1, …, ±K are congruent mod p², K < p², s + 2νN + 4h − 2K + 1 < p², Σ_a L_p(a) = h, and t_min ≤ 2L_p(0) + (b_0 − (s−1))/2;
- **outer** (p > K/3, which includes every p > K up to the prime bound): v_p(S) + ⌊W_O⌋ if `OuterOK` holds (p odd, p ≥ max(7, s), 2K < p², N < p), else L_small; W_O = 2 Σ (outer weights) − loss, with loss = `rawRank` in `Lp` and loss = min(`rawRank`, zero count) in `LpSharp`.

The normaliser is ∏_{p prime, p ≤ max(7, s, 2h)} p^{−L_p}. It is defined from these explicit exponents, **not** as "the least number clearing the denominators of F", so integrality is a real statement. v_p(S) is the true valuation of the explicit rational S ≠ 0. The `else 0` junk branches of `WO`, `WOsharp`, `WI` are never selected at a prime: `OuterOK` and `InnerOK` both force p odd, and the theorems take `Fact p.Prime`; the normaliser's product runs over primes only.

```lean
-- AssemblyData.lean:80-86
def LocalValuationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∀ (p : ℕ) (_ : Fact p.Prime),
      GV p (FS s ν K N (K - N)) (Lp s ν K N M p L)
-- AssemblyData.lean:90-96
def NormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizer s ν K N M L) * FS s ν K N (K - N)
-- SharpAssembly.lean:29-35
def SharpNormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizerSharp s ν K N M L) * FS s ν K N (K - N)
```

### 2.6 Objects of the key step (E300)
```lean
-- BinomBasis.lean:34
noncomputable def Lb (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * _root_.bernoulli n
-- TauBound.lean:24-25
noncomputable def tauS (s : ℕ) (P : ℚ[X]) : ℚ :=
  Lb (derivative^[s - 2] P) / ((s - 1).factorial : ℚ)
-- PoleFun.lean:26, 41, 45-46, 50, 58-59
noncomputable def piPl (Pl : Finset ℤ) : ℚ[X] := ∏ r ∈ Pl, (X - C (r : ℚ))
noncomputable def polyPart (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] := A /ₘ piPl Pl
noncomputable def resP (A : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) : ℚ :=
  A.eval (r : ℚ) / ∏ s ∈ Pl.erase r, ((r : ℚ) - s)
def dd (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat
noncomputable def tauXs (s : ℕ) (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  C (tauS s (polyPart A Pl)) + ∑ r ∈ Pl, C (resP A Pl r) * (C (Hs s (dd r)) - X)
-- DirectBound.lean:29-30, 34, 38
noncomputable def numOf (κ : ℚ) (Z : Multiset ℤ) : ℚ[X] :=
  C κ * (Z.map fun ζ : ℤ => X - C (ζ : ℚ)).prod
def cnt (p : ℕ) (Z : Multiset ℤ) (c : ZMod p) : ℕ := (Z.filter fun ζ : ℤ => (ζ : ZMod p) = c).card
def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ := Pl.filter fun r : ℤ => (r : ZMod p) = c
```
In mathematics: L(x^k) = B_k; τ_s(P) = L(P^{(s−2)})/(s−1)!; `tauXs s A Pl` is τ_X applied to the rational function A(x)/∏_{r ∈ Pl}(x − r), namely τ_s(polynomial part) + Σ_r Res_r · (H^{(s)}_{d(r)} − X), with d(r) = r for r ≥ 0 and −r − 1 for r < 0. This is `derivation.md` (s1).

## 3. Declaration by declaration

### 3.1 E311: `AperyS.AssemblyTarget.normalization_sharp_statement`
(a) Sheet (`L-sharp-normalization/SHEET.md`): `AperyS.AssemblyTarget.normalization_sharp_statement : AperyS.AssemblyTarget.SharpNormalizationStatement`. Source: `SharpAssembly.lean:138`, a `theorem` whose type is the `def … : Prop` of lines 29-35 (quoted in §2.5).

(c) For all natural numbers s, ν, K, N, M and every allocation L: **if** s is odd, s ≥ 3, ν is even, ν ≥ 2, N < K, M ≥ 1, 6N ≤ K, K + (ν−2)N ≤ ((s−1)/2)·K, and 2K ≤ s + 2νN + 4(K−N−1), **then** there is Q ∈ ℤ[X] whose image in ℚ[X] is m·F, where F = `FS s ν K N (K − N)` (§2.2) and m = `normalizerSharp s ν K N M L` (§2.5). In words: m·F has integer coefficients. Equivalently: at every prime p ≤ max(7, s, 2h) every nonzero coefficient of F has v_p ≥ `LpSharp`, and at every larger prime F is p-integral.

(d) Hunt.
- Natural arithmetic: ν − 2 is exact (ν ≥ 2); (s − 1)/2 is exact (s odd, assumed); K − N is exact (N < K); (K − N) − 1 is exact. No truncation changes the meaning.
- The normaliser is not 0: `normalizerSharp_pos : ∀ (s ν K N M : ℕ) (L : Allocations), 0 < normalizerSharp s ν K N M L` (`:58`), with no hypothesis. It does not clear denominators by definition (§2.5).
- **F1 (redundant hypothesis).** The "degree condition" `2 * K ≤ degreeBound s ν K N` follows from s ≥ 3, ν ≥ 2, N < K: degreeBound − 2K = (s − 3) + 2(K − 1) + 2(ν − 2)N + 1 ≥ 1 (PROOF-DRAFT, this line; COMPUTED: no failure for odd s < 40, ν < 30, K < 60, §8). It restricts nothing.
- **F2 (range at s = 3).** At s = 3 the hypothesis K + (ν−2)N ≤ ((s−1)/2)K reads (ν − 2)N = 0. So at s = 3 the two normalisation statements say something only for ν = 2 or N = 0 (COMPUTED, §8). For s ≥ 5 the hypothesis bounds ν in terms of N/K: with 6N ≤ K it holds for every ν ≤ 3s − 7; on K = 40n, N = 3n it holds for even ν ≤ 14 at s = 5 and ν ≤ 28 at s = 7. This agrees with `derivation.md` §8 (H2), which found the unrestricted statement false at s = 3, ν ≥ 4.
- **F3 (not asserted: F ≠ 0).** If F were the zero polynomial the statement would hold trivially. No declaration of this group says F ≠ 0. Outside this group, lane B's real-bound statement has `0 < aeval (zetaS s) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n))` (`L-unified-lean/BRealStatement.lean:31`, ν = 6 only; its hypotheses were not read here).
- "Odd s" is an explicit hypothesis; even s is not covered. `Even ν` and `1 ≤ M` are hypotheses of the proposition; the underlying theorem `normalization_sharp` does not take them (the proof term of line 139 binds them as `_heven`, `_hM`), so the proposition is narrower than what was proved, never wider.
- Not vacuous on the template: K = 40, N = 3 (n = 1), ν = 6, M = 400. s = 5: 5 odd, 6 even, 3 < 40, 18 ≤ 40, 52 ≤ 2·40 = 80, 80 ≤ 185. s = 7: 52 ≤ 3·40 = 120, 80 ≤ 187. For general n: 18n ≤ 40n, 52n ≤ 80n. The exponents at these points are non-trivial (§6).
- **The same normaliser as lane B's limit theorem: yes.** `ExplicitNormalizerLimitStatement` (`evidence/B-full-bridge/ExplicitTargets.lean:58-63`, and the byte-identical copy `L-unified-lean/BInnerStatement.lean`) has `normalizerSharp s ν (40 * n) (3 * n) M (explicitAllocation s ν (40 * n) (3 * n) M)` under `open AperyS AperyS.AssemblyTarget`: the same constant, with arguments in the same order (s, ν, K = 40n, N = 3n, M, L). COMPUTED: in the unified project there is exactly one `def normalizerSharp` and one `def LpSharp` (`Zeta5S/SharpAssembly.lean`). Lane B's own probe uses a vendored copy `B-full-bridge/vendor/Zeta5S/`; its 46 files are byte-identical to lane L's (which has one more, `Distribution.lean`) except one tactic line in the proof of `normalizerSharp_le_raw` (`SharpAssembly.lean:69`); every definition is the same text. On lane B's scope (odd s ≥ 5, even 2 ≤ ν ≤ 10, M ≥ 40, n ≥ 1) all hypotheses of E311 hold (64n ≤ 80n), so E311 does apply to the normaliser of the limit. One seam: E311 has F = `FS s ν K N (K − N)`, i.e. size 40n − 3n, and lane B's analytic statement has the literal size 37n; they agree after rewriting 40n − 3n = 37n.
- Upstream (s = 5): `Apery.integral_mN {n : ℕ} (hn : 1 ≤ n) : ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mN n) * F n` (`Norm.lean:269-271`). The upstream analogue is the **raw** statement E305, see 3.3. The sharp normaliser has no upstream counterpart (upstream's outer loss is the rank alone).

(e) Differences from `FREEZE_BRIEF.md` row 1 and `claims_table.tex` row 1: see §4, which applies to 3.1 to 3.4 together.

(f) **match with the stated differences.** Corrected sentence: *"For odd s ≥ 3, even ν ≥ 2, N < K, a cutoff M ≥ 1, 6N ≤ K and K + (ν−2)N ≤ ((s−1)/2)K, and for every supplied allocation, the polynomial m·F_K has integer coefficients, where F_K = S_K Δ_K ∈ ℚ[X] is the scaled Hankel determinant of size h = K − N of the formal functional, and m = ∏_{p ≤ max(7, s, 2h)} p^{−L_p} > 0 with L_p the selected exponent (crude, inner when the allocation passes its check, outer with loss min(rank bound, zero count), crude otherwise). At s = 3 the second condition forces ν = 2 or N = 0. Nothing is asserted about the size of m, about F_K ≠ 0, or about ζ(s)."*

### 3.2 E311: `local_valuation_sharp`, `normalizerSharp_pos`, `normalizerSharp_le_raw`
(a) Sheet:
```lean
@AperyS.AssemblyTarget.local_valuation_sharp : ∀ {p : ℕ} [Fact (Nat.Prime p)] (s ν K N M : ℕ)
  (L : AperyS.AssemblyTarget.Allocations),
  Odd s → 3 ≤ s → 2 ≤ ν → N < K → 2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
    AperyS.GV p (AperyS.FS s ν K N (K - N)) ↑(AperyS.AssemblyTarget.LpSharp s ν K N M p L)
AperyS.AssemblyTarget.normalizerSharp_pos : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  0 < AperyS.AssemblyTarget.normalizerSharp s ν K N M L
AperyS.AssemblyTarget.normalizerSharp_le_raw : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  AperyS.AssemblyTarget.normalizerSharp s ν K N M L ≤ AperyS.AssemblyTarget.normalizer s ν K N M L
```
(line breaks of the sheet joined). Source: `SharpAssembly.lean:45-49`, `:58-59`, `:66-67`; all `theorem`s; same hypotheses as printed.

(c) For every prime p, odd s ≥ 3, every ν ≥ 2 (even **or odd**), N < K, **every** M (0 included) and every allocation: each nonzero coefficient of F has v_p ≥ `LpSharp`. (The degree hypothesis is automatic, F1.) The sharp normaliser is positive and at most the raw one, unconditionally.

(d) No H1, no H2, no parity of ν, no M ≥ 1: strictly stronger than the claim's hypothesis list. `LpSharp` is a selected lower bound; with an allocation that fails `InnerOK` the inner primes fall back to the crude bound. F3 applies (vacuous if F = 0).

(f) **match with the stated differences** (the theorem is stronger); `normalizerSharp_pos`, `normalizerSharp_le_raw`: **match**. Sentence: *"At every prime p, every nonzero coefficient of F_K has p-adic valuation at least the selected integer L_p, for odd s ≥ 3, ν ≥ 2 and N < K, any cutoff and any supplied allocation. L_p is a lower bound, not the valuation."*

### 3.3 E303 and E305: `local_valuation_statement`, `local_valuation`, `normalization_statement`, `normalization`, `normalizer_pos`
(a) Sheet (`L-human-check/SHEET.md`), verbatim:
```lean
AperyS.AssemblyTarget.local_valuation_statement : AperyS.AssemblyTarget.LocalValuationStatement
@AperyS.AssemblyTarget.local_valuation : ∀ {p : ℕ} [Fact (Nat.Prime p)] (s ν K N M : ℕ)
  (L : AperyS.AssemblyTarget.Allocations),
  Odd s → 3 ≤ s → 2 ≤ ν → N < K → 2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
    AperyS.GV p (AperyS.FS s ν K N (K - N)) ↑(AperyS.AssemblyTarget.Lp s ν K N M p L)
AperyS.AssemblyTarget.normalization_statement : AperyS.AssemblyTarget.NormalizationStatement
AperyS.AssemblyTarget.normalization : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  Odd s → 3 ≤ s → 2 ≤ ν → N < K → 6 * N ≤ K → K + (ν - 2) * N ≤ (s - 1) / 2 * K →
    2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
      ∃ Q, Polynomial.map (Int.castRingHom ℚ) Q =
          Polynomial.C (AperyS.AssemblyTarget.normalizer s ν K N M L) * AperyS.FS s ν K N (K - N)
AperyS.AssemblyTarget.normalizer_pos : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  0 < AperyS.AssemblyTarget.normalizer s ν K N M L
```
Source: `AssemblyProof.lean:80` and `:67-70`; `NormalizationProof.lean:164`, `:130-135`, `:19-20`. All `theorem`s; the two `…_statement` theorems have the `def … : Prop` types of `AssemblyData.lean:80-86` and `:90-96`.

(c) As 3.1 and 3.2 with the raw outer loss (`Lp`, `normalizer` instead of `LpSharp`, `normalizerSharp`). `(s - 1) / 2 * K` parses as ((s−1)/2)·K.

(d) Same hunt, same findings F1 to F3. Upstream at s = 5. COMPUTED by reading: with (s, ν, K, N, M) = (5, 6, 40n, 3n, 400) and L = upstream's `allocI`, the definitions specialise to upstream's `Norm.lean:27-90` item by item (`InnerOK`: 5 ≤ p and "−4"; `OuterOK`: the extra conjunct s ≤ p follows from 7 ≤ p; prime bound max(7, 5, 74n) = 74n; the outer rank loss min(37n, (52n − 2p + 2)₊) equals upstream's `37n − ((2p + 22n − 3) − (37n − 1))` in ℕ, COMPUTED for n < 60, p < 400, §8), **with two differences**: (i) the crude exponent uses ⌊log_p(184n + 2)⌋ where upstream has ⌊log_p(200n)⌋, so the general `Lsmall` is ≥ upstream's and the general normaliser is ≤ upstream's `mN` (equal at n = 1; first difference at n = 5, p = 31; COMPUTED, §8); (ii) F has size 40n − 3n instead of the literal 37n. So specialising gives upstream's `integral_mN` with a normaliser that divides upstream's; not the literally identical statement. The hypothesis N < K becomes n ≥ 1, which is upstream's `hn`. The library also proves `F n = FS 5 6 (40 * n) (3 * n) (37 * n)` (`AtFive.lean:416`) and three exponent equalities with upstream's `Lp 1 p` at p = 2, 13, 17 (`AssemblyAnchors.lean:108-111`), for copies of upstream's definitions made inside `Zeta5S` (the `Zeta5S` files do not import upstream's modules).

(f) **match with the stated differences**; `normalizer_pos`: **match**. Sentences: as in 3.1 and 3.2 with "outer loss = the rank bound".

### 3.4 E300: `AperyS.tauXs_direct`, `AperyS.tauS_distribution`
(a) Sheet, verbatim:
```lean
@AperyS.tauXs_direct : ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (s : ℕ),
  2 ≤ s →
    s ≤ p →
      ∀ (κ : ℚ),
        AperyS.VG p κ 0 →
          ∀ (Z : Multiset ℤ) (Pl : Finset ℤ),
            AperyS.Sep p Pl →
              (∀ r ∈ Pl, AperyS.dd r < p ^ 2) →
                Z.card - Pl.card + 1 < p ^ 2 →
                  ∀ (β : ℚ),
                    (∀ (c : ZMod p), β ≤ ↑(AperyS.cnt p Z c) - ↑(AperyS.plc p Pl c).card) →
                      AperyS.GV p (AperyS.tauXs s (AperyS.numOf κ Z) Pl) (β - (↑s - 1))
AperyS.tauS_distribution : ∀ (s : ℕ),
  2 ≤ s →
    ∀ (n : ℕ) (P : Polynomial ℚ),
      ∑ a ∈ Finset.range n, AperyS.tauS s (P.comp (Polynomial.C ↑a + Polynomial.C ↑n * Polynomial.X)) =
        ↑n ^ (s - 1) * AperyS.tauS s P
```
Source: `DirectPoly.lean:280-284` and `Distribution.lean:67-68`; `theorem`s; hypotheses as printed.

(c) `tauXs_direct`: for every integer s ≥ 2 (**any parity**), every prime p ≥ s, every rational κ that is 0 or p-integral, every finite multiset Z of integers (zeros, with multiplicity) and finite set Pl of integers (simple poles) such that (i) two distinct poles congruent mod p are not congruent mod p², (ii) d(r) < p² for every pole, (iii) #Z − #Pl + 1 < p² (truncated subtraction: automatically true when #Z < #Pl, where the polynomial part is 0), and every rational β with β ≤ #{zeros ≡ c} − #{poles ≡ c} **for all residue classes c mod p**: every nonzero coefficient of τ_X(κ∏_{ζ∈Z}(x − ζ) / ∏_{r∈Pl}(x − r)) (a polynomial of degree ≤ 1 in X) has v_p ≥ β − (s − 1). `tauS_distribution`: for s ≥ 2, every natural n (not only primes; n = 0 gives 0 = 0) and every P ∈ ℚ[x]: Σ_{a=0}^{n−1} τ_s(P(a + nx)) = n^{s−1} τ_s(P).

(d) The subtraction `↑s - 1` in the conclusion is in ℚ: no truncation. "Loss s − 1" is relative to the minimum over all classes of (zeros − poles), not class by class. Nothing here mentions the determinant. Upstream: `tauX_direct (hp5 : 5 ≤ p) … : GV p (tauX (numOf κ Z) Pl) (β - 4)` (`Arith/DirectPoly.lean:265-268`): specialising s = 5 gives exactly this (2 ≤ 5 is trivial; `tauS 5` is upstream's `tau` = L(P''')/24, `Hs 5` its `H5`). The distribution identity is `derivation.md` (s2) and Fauzan's Lemma 3.2 at s = 5.

(f) `tauXs_direct`: **match with the stated differences** (s ≥ 2 of any parity, p ≥ s, the loss is measured from the worst class). `tauS_distribution`: **match**. Sentence: *"Key step: for every s ≥ 2 and every prime p ≥ s, the functional τ_X of a rational function with integer zeros and simple integer poles (poles separated mod p², sizes below p²) has all coefficients of p-adic valuation at least min over classes c mod p of (zeros in c − poles in c), minus s − 1. It rests on the identity Σ_{a<n} τ_s(P(a + nx)) = n^{s−1} τ_s(P)."*

### 3.5 E302: `AperyS.outer_boundS_clamped`, `AperyS.determinant_integral_above_K`
(a) Sheet, verbatim:
```lean
@AperyS.outer_boundS_clamped : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {m : ℕ} (hm : 2 * m + 1 = p) (s ν N K : ℕ),
  Odd s → 3 ≤ s → s ≤ p → 2 ≤ ν → N ≤ K → 7 ≤ p → K < 3 * p → 2 * K < p ^ 2 → N < p →
    AperyS.GV p (AperyS.ΔS s ν K N (K - N))
      (2 * ∑ c, ∑ i ∈ Finset.range (AperyS.LoC hm N K c), AperyS.wO hm s ν N K c i -
        ↑(min (K - N) (K + (ν - 2) * N - (s - 1) / 2 * (p - 1))))
@AperyS.determinant_integral_above_K : ∀ {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ},
  2 * m + 1 = p →
    ∀ (s ν N K : ℕ),
      Odd s → 3 ≤ s → s ≤ p → 2 ≤ ν → N ≤ K → 7 ≤ p → K < p →
        K + (ν - 2) * N ≤ (s - 1) / 2 * K → AperyS.GV p (AperyS.ΔS s ν K N (K - N)) 0
```
(line breaks joined). Source: `OuterScope.lean:70-76` and `:86-91`; `theorem`s. Note the argument order (s ν **N K**) of these two theorems against (s ν **K N**) of `ΔS`, `WO`, `Lp`: the bodies use `ΔS s ν K N (K − N)`, `LoC hm N K`, `wO hm s ν N K` consistently (checked against the section variables `(hm) (σ ν N K)` of `OuterBasis.lean`).

(c) For odd s ≥ 3, ν ≥ 2, N ≤ K and an odd prime p ≥ max(7, s) with K < 3p, 2K < p², N < p: every nonzero coefficient of Δ (size h = K − N) has v_p ≥ 2 Σ_c Σ_{i < LoC(c)} w_O(c, i) − min(h, (K + (ν−2)N − ((s−1)/2)(p−1))₊). Second: for such s, ν, N ≤ K and an odd prime p ≥ max(7, s) with p > K, if K + (ν−2)N ≤ ((s−1)/2)K then Δ is p-integral.

(d) Truncated subtraction in the rank term is the intended positive part. Neither theorem assumes 6N ≤ K: the outer bound needs only N < p (the weight table uses δ(c) = [c ≤ N] ∈ {0, 1} whatever the number of removed poles in the class). The second theorem is about Δ, not about F = SΔ. Upstream: `outer_bound (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2) (hpN : 3 * n < p)` (`Arith/OuterEntryMain.lean:483-486`): specialising (s, ν, N, K) = (5, 6, 3n, 40n) gives the same hypotheses (the added ones are true) and the same bound, the rank term being written differently but equal in ℕ (§8). `determinant_integral_above_K` generalises Fauzan's Proposition 4.3 with the condition (H2) of `derivation.md` §8 as an explicit hypothesis.

(f) `outer_boundS_clamped`: **match with the stated differences** (finite side conditions; the loss is a rank *bound*; class 0 has its own s-free weights). `determinant_integral_above_K`: **match**.

### 3.6 E310: `det_lowrank_zero_bound`, `outer_boundS_sharp_clamped`, `WO_le_WOsharp`, `GV_FS_outer_sharp`
(a) Sheet (`L-sharp-outer/SHEET.md`), verbatim:
```lean
@AperyS.det_lowrank_zero_bound : ∀ {p : ℕ} [Fact (Nat.Prime p)] {h r : ℕ} (A : Matrix (Fin h) (Fin h) (Polynomial ℚ))
  (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ),
  (∀ (s : Fin h), w s = 0 ∨ w s ≤ -1 / 2) →
    (∀ (s t : Fin h), AperyS.GV p (A s t) (w s + w t)) →
      (∀ (s : Fin h) (u : Fin r), AperyS.VG p (U s u) 0) →
        (∀ (u : Fin r) (t : Fin h), AperyS.VG p (V u t) 0) →
          AperyS.GV p (A + ((↑p)⁻¹ • (U * V)).map ⇑Polynomial.C).det
            (2 * ∑ s, w s - ↑(min r (AperyS.zeroWeightCount w)))
@AperyS.outer_boundS_sharp_clamped : ∀ {p m : ℕ} [inst : Fact (Nat.Prime p)] (hm : 2 * m + 1 = p) (s ν N K : ℕ),
  Odd s → 3 ≤ s → s ≤ p → 2 ≤ ν → N ≤ K → 7 ≤ p → K < 3 * p → 2 * K < p ^ 2 → N < p →
    AperyS.GV p (AperyS.ΔS s ν K N (K - N))
      (2 * ∑ c, ∑ i ∈ Finset.range (AperyS.LoC hm N K c), AperyS.wO hm s ν N K c i -
        ↑(min (AperyS.AssemblyTarget.rawRank s ν K N p) (AperyS.outerZeroCount hm s ν N K)))
AperyS.AssemblyTarget.WO_le_WOsharp : ∀ (s ν K N p : ℕ),
  AperyS.AssemblyTarget.WO s ν K N p ≤ AperyS.AssemblyTarget.WOsharp s ν K N p
AperyS.AssemblyTarget.GV_FS_outer_sharp : ∀ (s ν K N p : ℕ) [Fact (Nat.Prime p)],
  Odd s → 3 ≤ s → 2 ≤ ν → N ≤ K → AperyS.AssemblyTarget.OuterOK s K N p →
    AperyS.GV p (AperyS.FS s ν K N (K - N))
      (↑(AperyS.AssemblyTarget.vSK ν K N p) + ↑⌊AperyS.AssemblyTarget.WOsharp s ν K N p⌋)
```
(line breaks joined). Source: `SharpLowRank.lean:58-64`; `SharpOuterScope.lean:13-19`, `:40`, `:53-56`; `theorem`s.

(c) Linear algebra lemma: p prime; A an h×h matrix over ℚ[X]; U (h×r) and V (r×h) rational with all nonzero entries p-integral; weights w ∈ ℚ^h with each w_s = 0 or w_s ≤ −1/2; every nonzero coefficient of A_{st} of valuation ≥ w_s + w_t. Then every nonzero coefficient of det(A + p^{−1}UV) has v_p ≥ 2Σ_s w_s − min(r, #{s : w_s = 0}). Outer bound: under exactly the hypotheses of 3.5, v_p of every nonzero coefficient of Δ is ≥ 2Σ w_O − min(`rawRank`, `outerZeroCount`). `WO_le_WOsharp`: the sharp exponent is at least the raw one, for all arguments (including the junk branches, where both are 0). `GV_FS_outer_sharp`: for odd s ≥ 3, ν ≥ 2, N ≤ K and a prime p with `OuterOK`: every nonzero coefficient of F has v_p ≥ v_p(S) + ⌊W_O^sharp⌋.

(d) The gap hypothesis (negative weights ≤ −1/2) is extra with respect to upstream's `det_lowrank_bound` (`Arith/LowRank.lean:17-21`: weights ≤ 0, loss r); it is what makes min(r, zero count) valid, and the outer table satisfies it by construction (half-integers). "Rank" in "min(rank, zero count)" is the bound `rawRank`, not the rank of a matrix; "zero count" is the number of rows of the weight table with weight exactly 0 (the −1/2 row of class 0 is not counted). No upstream counterpart at s = 5; the lemma is Fauzan (4.13)-(4.14), and `FREEZE_BRIEF.md` records that the pre-event repository [team handle]/zeta7-irrational already has a min(rank, zero count) lemma at s = 7, ν = 8 (not compared here).

(f) `det_lowrank_zero_bound`, `outer_boundS_sharp_clamped`: **match with the stated differences**. `WO_le_WOsharp`, `GV_FS_outer_sharp`: **match**. Sentence: *"For odd s ≥ 3, ν ≥ 2, N ≤ K and an odd prime p ≥ max(7, s) with K < 3p, 2K < p², N < p, every nonzero coefficient of Δ_K has p-adic valuation at least 2Σ(outer weights) − min(R_p, Z_p), where R_p = min(h, (K + (ν−2)N − ((s−1)/2)(p−1))₊) bounds the rank of the moment correction and Z_p is the number of zero outer weights."*

## 4. Differences from the claim as the report states it

Claim (`FREEZE_BRIEF.md` row 1): "For odd s ≥ 3 and even ν ≥ 2, under 6N ≤ K, K + (ν−2)N ≤ ((s−1)/2)K and one degree condition, the normalised determinant F = S_K Δ_K has an explicit valuation bound at every prime and an integer normalisation, for every finite K. Key step: a class bound with loss s − 1."

Every difference found:

1. **Hypotheses not in the sentence:** N < K and a cutoff M ≥ 1 (both in the Lean propositions; `claims_table.tex` row 1 has them).
2. **"One degree condition" is not a condition** (F1): it follows from s ≥ 3, ν ≥ 2, N < K. The report can drop it or say it is automatic.
3. **Range of (s, ν) actually covered** (F2): at s = 3 only ν = 2 (or N = 0); for s ≥ 5, ν is bounded by K + (ν−2)N ≤ ((s−1)/2)K. "Odd s ≥ 3 and even ν ≥ 2" overstates the range unless the reader applies that hypothesis. The valuation theorems alone (`local_valuation`, `local_valuation_sharp`) need neither that hypothesis nor 6N ≤ K nor even ν.
4. **The allocation is an arbitrary supplied one,** checked by `InnerOK`; if the check fails the crude bound is used. So the theorem gives validity for every allocation and says nothing about how small the normaliser is. Quality is lane B's limit theorem, for one explicit allocation, odd s ≥ 5, ν ≤ 10.
5. **"Valuation bound"** means: each nonzero coefficient of F has v_p ≥ L_p. L_p is a selected lower bound, not the valuation.
6. **"Integer normalisation"** means m·F ∈ ℤ[X] with m = ∏ over primes p ≤ max(7, s, 2(K − N)) of p^{−L_p}; this includes the assertion that F is p-integral at every larger prime. m > 0 is a separate theorem.
7. **Size:** h = K − N always. **Finite K only**: no growth rate, no limit, no optimality, no comparison with the true valuations.
8. **Not asserted** (F3): F ≠ 0; any link between the indeterminate X and ζ(s); any real bound; any irrationality.
9. **Two normalisers:** the raw one (E305, the analogue of upstream's) and the sharp one (E311, the one lane B's limit uses); sharp ≤ raw.
10. **Key step:** stated for s ≥ 2 of any parity and primes p ≥ s; the loss s − 1 is measured from the worst class.
11. **Against upstream at s = 5:** not literally upstream's statement (the allocation is a parameter; the crude logarithm has a smaller argument; size 40n − 3n), see 3.3.

`claims_table.tex` row 1. Its hypothesis list equals the Lean's. Three remarks. (a) "for any supplied allocation" is right. (b) **F4:** the sentence "From s to s + 2 the inner exponent changes by an amount in [−2h, 0]" lacks its conditions: the Lean statement (`FiniteStep.lean:150-154`, `Lp_inner_sstep`, outside this group, statement read only) is for a fixed allocation, an inner-range prime, and `InnerOK` holding **at both s and s + 2**; without them the selected exponent can go up (row 15 of the same table: −444 to −119). Add "for a fixed allocation that passes the inner check at s and at s + 2". (c) It should say that at s = 3 the hypotheses force ν = 2 or N = 0.

`lean_declarations.tex` D1 to D4. The four verbatim blocks equal the sheets and the source. The "difference from the claim" sentences are accurate. Additions I would make: D1, "for every s ≥ 2, of any parity"; D2 and D4, "the degree condition is implied by the other hypotheses; at s = 3 the hypotheses force ν = 2 or N = 0; F ≠ 0 is not asserted"; D3, "also without even ν and without M ≥ 1". D4's sentence that `normalizerSharp` is the normaliser of D12 and D13 is **confirmed** (3.1 (d)). **F5:** `FREEZE_BRIEF.md`'s pointer to `L-unified-full-bridge/SHEET.md` as the list of 495 declarations is wrong (§0).

## 5. Findings, in one place

- **F1** The degree hypothesis is redundant (PROOF-DRAFT one line, 3.1 (d); COMPUTED on a range).
- **F2** At s = 3 the normalisation statements cover only ν = 2 or N = 0 (COMPUTED; consistent with `derivation.md` §8).
- **F3** No statement of this group says F ≠ 0; all of them hold trivially for a zero polynomial. Junk values: none leaks (`padicValRat p 0` is excluded by `VG`; the `else 0` branches are unreachable at a prime; `vSK` is the valuation of a nonzero rational).
- **F4** `claims_table.tex` row 1, the s-step sentence, lacks its conditions.
- **F5** A wrong locator in `FREEZE_BRIEF.md`.

## 6. Hand tests on the template, n = 1 (K = 40, N = 3, h = 37, ν = 6, M = 400)

COMPUTED by hand from the definitions of §2 (no Lean run), and compared with the kernel-checked anchors in the source.

- Hypotheses of E303/E305/E311 hold at s = 5 and s = 7 (3.1 (d)).
- p = 17 (m = 8): 17·400 > 40 and 51 > 40, so outer; `OuterOK` holds (17 odd, ≥ 7 ≥ s, 80 < 289, 3 < 17). v_17(S) = 74·2 − 2·62 = 24 (anchor `VS17`). Rows per class: class 0: 2; c = 1, 2, 3: 4 each; c = 4, 5, 6: 5 each; c = 7, 8: 4 each; total 37.
  - s = 5: Σw = −2 − 3·2 − 3·10.5 − 2·7 = −53.5; rank bound min(37, 52 − 32) = 20; W_O = −107 − 20 = −127 (anchor `WO5`); zero count 1 + 6 + 6 + 4 = 17; W_O^sharp = −107 − 17 = −124 (anchor `WOsharp5_17`); L_17 = −103 raw (upstream's value), −100 sharp (anchor `LpSharp5_outer17`).
  - s = 7: Σw = −2 − 3·4.5 − 3·13.5 − 2·9 = −74; rank bound min(37, 52 − 48) = 4; zero count 14; W_O = W_O^sharp = −152 (anchors `WO7`, `WOsharp7_17`); L_17 = −128 in both forms. The sheet quotes a stored exact valuation −126 at this point, which is ≥ −128.
  - A class without removed pole and ℓ = 5 costs −2Σw = 21 = 7·3 at s = 5 and 27 = 9·3 at s = 7: the per-pole cost s + 2 of `derivation.md` §3.
- p = 2: 3·2 ≤ 40 and `InnerOK` fails (2 is even): L_2 = −(6·37·⌊log₂ 186⌋ + 37·v_2(24)) = −(222·7 + 111) = −1665 (anchor `exponent5_fallback2`, and upstream's value).
- p = 13: inner range; the anchors give `InnerOK` true at s = 5 and s = 7 for upstream's allocation [15, 3, 2, 2, 5, 5, 5], W_I = −117/2 and −94, v_13(S) = 50, so L_13 = −67 and −138 (not recomputed by hand).

So the statements are not vacuous at the template, and the inner and outer branches are both exercised at s = 5 and at s = 7.

## 7. For the integrator

Board lines this file supports (the integrator posts them; this agent wrote no other file):
```text
DONE statement-compare AperyS.AssemblyTarget.normalization_sharp_statement by Claude Fable 5.2 (author Codex GPT): match with the stated differences; evidence/integrator-statement-compare/arithmetic.md §3.1, §4
DONE statement-compare AperyS.AssemblyTarget.local_valuation_sharp by Claude Fable 5.2 (author Codex GPT): match with the stated differences (stronger); §3.2
DONE statement-compare AperyS.AssemblyTarget.local_valuation_statement, AperyS.AssemblyTarget.normalization_statement by Claude Fable 5.2 (author Codex GPT): match with the stated differences; §3.3
DONE statement-compare AperyS.tauXs_direct by Claude Fable 5.2 (author Codex GPT): match with the stated differences; AperyS.tauS_distribution: match; §3.4
DONE statement-compare AperyS.outer_boundS_clamped, AperyS.outer_boundS_sharp_clamped, AperyS.det_lowrank_zero_bound by Claude Fable 5.2 (author Codex GPT): match with the stated differences; AperyS.determinant_integral_above_K: match; §3.5, §3.6
```
Not done here: the `log/AI_USE.md` row for this session; the `--final` gate of the submitted project; a check that the report prints these statements beside the claim; any reading of a proof; the non-headline helpers (`GV_FS_Lsmall`, `GV_FS_big`, `padicValRat_normalizer`, `Lp_inner_sstep` beyond its statement); lane B's allocation `explicitAllocation` and its limit theorem (another group).

## 8. Code of the COMPUTED checks (Python 3, standard library; run from `problems/108-zeta-odd-autopsy/evidence`)

```python
import re
# (1) the 55 VERBATIM blocks of L-human-check/SHEET.md equal the source at the stated lines
sheet = open('L-human-check/SHEET.md', encoding='utf-8').read().split('\n'); ok = bad = 0
for i, line in enumerate(sheet):
    m = re.match(r'-- VERBATIM (\S+):(\d+)-(\d+)\s+(\S+)', line)
    if m:
        f, a, b = m.group(1), int(m.group(2)), int(m.group(3))
        src = open('L-unified-lean/Zeta5S/' + f, encoding='utf-8').read().split('\n')[a-1:b]
        ok += sheet[i+1:i+1+(b-a+1)] == src; bad += sheet[i+1:i+1+(b-a+1)] != src
print(ok, bad)                                   # 55 0
# (2) F1: the degree condition never fails
print(sum(not (2*K <= s + 2*nu*N + 4*(K-N-1)) for s in range(3, 40, 2) for nu in range(2, 30)
          for K in range(1, 60) for N in range(K)))                                   # 0
# (3) F2: at s = 3, no instance with nu > 2 and N > 0
print(sum(6*N <= K and K + (nu-2)*N <= K for nu in range(4, 30, 2) for K in range(1, 80) for N in range(1, K)))  # 0
print([nu for nu in range(2, 60, 2) if 40 + (nu-2)*3 <= 2*40][-1], [nu for nu in range(2, 60, 2) if 40 + (nu-2)*3 <= 3*40][-1])  # 14 28
# (4) upstream's rank loss equals the general one at (s, nu, K, N) = (5, 6, 40n, 3n)
print(sum(max(37*n - max((2*p + 22*n - 3) - (37*n - 1), 0), 0) != min(37*n, max(52*n - 2*(p-1), 0))
          for n in range(1, 60) for p in range(2, 400)))                              # 0
# (5) floor(log_p(184n+2)) against floor(log_p(200n)), primes p <= 74n
def nlog(b, x):
    k = 0
    while b**(k+1) <= x: k += 1
    return k
def primes(N): return [q for q in range(2, N+1) if all(q % d for d in range(2, int(q**.5)+1))]
d = [(n, p) for n in range(1, 201) for p in primes(74*n) if nlog(p, 184*n+2) != nlog(p, 200*n)]
print(len(d), d[0])                              # 327 (5, 31)
```
Shell checks: `cmp` of each `L-unified-lean/Zeta5S/*.lean` with `C-zeta5-compact/Zeta5S/` and with `B-full-bridge/vendor/Zeta5S/`; `diff B-full-bridge/vendor/Zeta5S/SharpAssembly.lean L-unified-lean/Zeta5S/SharpAssembly.lean` (one tactic line, 69); `grep -rn "def normalizerSharp\|def LpSharp"` over `L-unified-lean`; `grep -c "| <name> |" L-unified-lean/DECLARATIONS.md` for the 17 names.
