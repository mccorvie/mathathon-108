# L9 / E308 — human statement-comparison sheet

Codex lane L, Sat Nov 14 2026. This sheet is for a human comparison of statements, definitions and the plain-language claims. No human verdict is assumed or recorded by this file.

**Current label: LEAN-CHECKED.** The v4.33.1 gate passed all120 listed declarations at13:55 PT; every axiom list is standard. A human must compare each chosen declaration before the integrator can record LEAN-VERIFIED. The isolated v4.35 trial also builds unchanged and prints the same120 statements; the root pins remainv4.33.1.

## Twenty-minute route for E303 and E305

1. **Minutes0–4:** read the two claims and exact printed statements below, then `LocalValuationStatement` and `NormalizationStatement` at the end of the definition block. The alias statements point to those explicit propositions; `local_valuation` and `normalization` print their stronger, fully expanded hypotheses.
2. **Minutes4–9:** in the definition block read `D`, `μmonoS`, `μpolyS`, `poleValueS`, `μXS`, `GS`, `ΔS`, `SS`, and `FS`. These define the finite object being normalized; they assert no analytic identification with zeta(s).
3. **Minutes9–15:** read `VG`, `GV`, the four capped-weight definitions, and all thirteen `AssemblyData` definitions. Follow `BseS`, the class-count definitions and `wO` when checking WI/WO. The source contexts and every model definition are included verbatim, in dependency order; the standalone block also typechecks with Mathlib alone.
4. **Minutes15–18:** read the differences and E304 anchors below. Check in particular the raw rank loss, the supplied allocation/fallback, and the support/degree changes from upstream.
5. **Minutes18–20:** answer the yes/no questions and post a per-declaration human verdict on BOARD.md. A partial reading is recorded as partial; it does not upgrade the unread declarations.

Standard library notation: `C` and `X` are polynomial constants and the indeterminate; `/ₘ` is monic polynomial quotient; `P.sum` sums coefficients over finite support; `padicValRat` and `padicValNat` are Mathlib valuations; `⌊q⌋` is integer floor. Natural subtraction and division truncate, while the valuation bounds are rational. `Fin`, finite sums/products, matrices, derivative iteration, Bernoulli numbers and casts have their standard Mathlib meanings. The block unfolds all custom mathematical definitions used by these statements; library internals and proof terms are outside a statement comparison.

## Differences that remain part of every approved claim

- **From E13:** this is the upstream raw rank-loss bound. The sharper `min(rank, zero-count)` correction, a limiting arithmetic exponent, prime-number-theorem passage, optimality of an allocation, the real bound, an analytic zeta(s) identification and irrationality are outside these results.
- **From upstream Zeta5:** the fixed `(s,nu,K,N,h)=(5,6,40n,3n,37n)` becomes symbolic. The pole constant is `-1/(s-1)`; the outer moment threshold is `((s-1)/2)(p-1)-1` and is proved positive where used. The crude logarithm uses the exact degree bound rather than200n. L(p) is supplied explicitly and its side conditions are checked before selection; the original numerical water-filling window is not silently generalized. The finite prime support is `max(7,s,2h)` rather than2h; at the original positive-n shape these agree.
- **Finite hypotheses:** H1 is `6N<=K`, including the safe boundary; H2 is `K+(nu-2)N<=((s-1)/2)K`. The small-prime shape `2K<=s+2nuN+4(h-1)` is explicit. The local raw theorem is stronger than its approved wrapper and drops conditions it does not use; the normalization wrapper retains all approved conditions.
- **Evidence level:** the cross-family Kimi review E216 found no statement mismatch or unsupported branch, with qualifications about which calculations were fresh. It did not replace a human comparison. Proofs closely adapt Firsching/Paul-Lez mo271/Zeta5@be1c0d82 (Apache-2.0, prior work); general-s adaptations and the source/gate comparisons are event work by the scout and driver, not a novelty verdict.

## R2 anchors (kernel checked; exact determinant values are stored computation)

The original allocation at p13 is `[15,3,2,2,5,5,5]`. At s5,nu6,K40,N3,M400, Lp at p2/13/17 is `-1665/-67/-103`, equal to upstream's exponent data; p2 is an explicit fallback. An extra M20 theorem exercises the selected-small branch at p2. At s7 the inner13/outer17 flags are true and Lp is `-138/-128`, below stored exact valuations `-116/-126`. Fresh bound reconstruction is in E304; no fresh determinant recomputation is claimed.


## E303 — finite all-prime valuation

**LEAN-CHECKED claim (two sentences).** The defined rational polynomial F has the stated integer lower valuation bound at every prime. Lp selects a checked inner or raw outer bound and otherwise uses the already proved all-prime crude bound.

### AperyS.AssemblyTarget.local_valuation_statement

Exact gate output:
```lean
AperyS.AssemblyTarget.local_valuation_statement : AperyS.AssemblyTarget.LocalValuationStatement
```

### AperyS.AssemblyTarget.local_valuation

Exact gate output:
```lean
@AperyS.AssemblyTarget.local_valuation : ∀ {p : ℕ} [Fact (Nat.Prime p)] (s ν K N M : ℕ)
  (L : AperyS.AssemblyTarget.Allocations),
  Odd s →
    3 ≤ s →
      2 ≤ ν →
        N < K →
          2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
            AperyS.GV p (AperyS.FS s ν K N (K - N)) ↑(AperyS.AssemblyTarget.Lp s ν K N M p L)
```

Questions (yes/no; explain each no):

- [ ] Is the statement about the explicit finite polynomial FS, with all hypotheses shown in LocalValuationStatement?
- [ ] Does the arbitrary supplied allocation get used only after InnerOK verifies its total, degree, separation and zero-class constraint?
- [ ] Does the fallback remain available at every prime, including when s exceeds p?
- [ ] Do you accept that local_valuation is stronger than the approved proposition because it retains the raw rank correction and does not require H1/H2?

## E305 — finite normalization

**LEAN-CHECKED claim (two sentences).** Multiplying F by the explicit finite prime product produces an integer polynomial. The product is positive, so this conclusion does not arise from multiplying F by zero.

### AperyS.AssemblyTarget.normalization_statement

Exact gate output:
```lean
AperyS.AssemblyTarget.normalization_statement : AperyS.AssemblyTarget.NormalizationStatement
```

### AperyS.AssemblyTarget.normalization

Exact gate output:
```lean
AperyS.AssemblyTarget.normalization : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  Odd s →
    3 ≤ s →
      2 ≤ ν →
        N < K →
          6 * N ≤ K →
            K + (ν - 2) * N ≤ (s - 1) / 2 * K →
              2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
                ∃ Q,
                  Polynomial.map (Int.castRingHom ℚ) Q =
                    Polynomial.C (AperyS.AssemblyTarget.normalizer s ν K N M L) * AperyS.FS s ν K N (K - N)
```

### AperyS.AssemblyTarget.normalizer_pos

Exact gate output:
```lean
AperyS.AssemblyTarget.normalizer_pos : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  0 < AperyS.AssemblyTarget.normalizer s ν K N M L
```

Questions (yes/no; explain each no):

- [ ] Does NormalizationStatement retain odd s>=3, even nu>=2, N<K, M>=1, H1, H2 and the finite degree-shape condition?
- [ ] Is the prime product exactly over primes up to max(7,s,2h), with exponent minus Lp?
- [ ] Does the claim stop at the integer-polynomial lift, with the raw-loss and analytic limitations below retained?
- [ ] Do the original-allocation s5 anchors and actual s7 inner/outer flags in E304 show the intended nonempty cases?

## E300 — the key general-s step

**LEAN-CHECKED claim (two sentences).** For polynomials, the Bernoulli functional after s-2 derivatives obeys the exact dilation identity with power s-1. The direct class-wise rational-function bound loses s-1 under its displayed prime, separation and degree hypotheses.

### AperyS.tauS_distribution

Exact gate output:
```lean
AperyS.tauS_distribution : ∀ (s : ℕ),
  2 ≤ s →
    ∀ (n : ℕ) (P : Polynomial ℚ),
      ∑ a ∈ Finset.range n, AperyS.tauS s (P.comp (Polynomial.C ↑a + Polynomial.C ↑n * Polynomial.X)) =
        ↑n ^ (s - 1) * AperyS.tauS s P
```

### AperyS.tauXs_direct

Exact gate output:
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
```

Questions (yes/no; explain each no):

- [ ] Does tauS use precisely s-2 derivatives and divide by (s-1)!?
- [ ] Is tauS_distribution only the polynomial identity, and is the complete set of tauXs_direct hypotheses visible?
- [ ] Do VG and GV explicitly permit zero coefficients?

## E302 — raw outer estimate and its scope

**LEAN-CHECKED claim (two sentences).** The outer determinant bound subtracts the clamped raw moment rank from twice the defined weight sum. For p>K, the separate finite rank budget makes the determinant integral under the stated prime and index conditions.

### AperyS.outer_boundS_clamped

Exact gate output:
```lean
@AperyS.outer_boundS_clamped : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {m : ℕ} (hm : 2 * m + 1 = p) (s ν N K : ℕ),
  Odd s →
    3 ≤ s →
      s ≤ p →
        2 ≤ ν →
          N ≤ K →
            7 ≤ p →
              K < 3 * p →
                2 * K < p ^ 2 →
                  N < p →
                    AperyS.GV p (AperyS.ΔS s ν K N (K - N))
                      (2 * ∑ c, ∑ i ∈ Finset.range (AperyS.LoC hm N K c), AperyS.wO hm s ν N K c i -
                        ↑(min (K - N) (K + (ν - 2) * N - (s - 1) / 2 * (p - 1))))
```

### AperyS.determinant_integral_above_K

Exact gate output:
```lean
@AperyS.determinant_integral_above_K : ∀ {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ},
  2 * m + 1 = p →
    ∀ (s ν N K : ℕ),
      Odd s →
        3 ≤ s →
          s ≤ p →
            2 ≤ ν →
              N ≤ K → 7 ≤ p → K < p → K + (ν - 2) * N ≤ (s - 1) / 2 * K → AperyS.GV p (AperyS.ΔS s ν K N (K - N)) 0
```

Questions (yes/no; explain each no):

- [ ] Is the correction min(h, max(0,K+(nu-2)N-r(p-1))) with r=(s-1)/2, without the sharper zero-count minimum?
- [ ] Does the above-K result concern Delta rather than scalar-normalized F?
- [ ] Do you accept that the raw estimate needs N<p, while H1 remains a restriction of the sharper paper class model?

## Verbatim model definitions, in dependency order

Generated directly from the frozen source. Only imports, namespace/section wrappers and source-location comments were added; each declaration text is unchanged. The context lines reproduce the source section parameters. Full source hashes and declaration ranges are in `definition-manifest.json`.

```lean
import Mathlib
set_option autoImplicit false
open Finset Polynomial
namespace AperyS

section
-- VERBATIM Val.lean:22-22  VG
def VG (p : ℕ) (q : ℚ) (r : ℚ) : Prop := q = 0 ∨ r ≤ (padicValRat p q : ℚ)

-- VERBATIM Val.lean:152-152  GV
def GV (p : ℕ) (f : ℚ[X]) (r : ℚ) : Prop := ∀ n, VG p (f.coeff n) r

end

section
-- VERBATIM BinomBasis.lean:34-34  Lb
noncomputable def Lb (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * _root_.bernoulli n

end

section
-- VERBATIM TauBound.lean:24-25  tauS
noncomputable def tauS (s : ℕ) (P : ℚ[X]) : ℚ :=
  Lb (derivative^[s - 2] P) / ((s - 1).factorial : ℚ)

end

section
-- VERBATIM PoleFun.lean:26-26  piPl
noncomputable def piPl (Pl : Finset ℤ) : ℚ[X] := ∏ r ∈ Pl, (X - C (r : ℚ))

-- VERBATIM PoleFun.lean:41-41  polyPart
noncomputable def polyPart (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] := A /ₘ piPl Pl

-- VERBATIM PoleFun.lean:45-46  resP
noncomputable def resP (A : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) : ℚ :=
  A.eval (r : ℚ) / ∏ s ∈ Pl.erase r, ((r : ℚ) - s)

-- VERBATIM PoleFun.lean:50-50  dd
def dd (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat

-- VERBATIM PoleFun.lean:55-55  Hs
def Hs (s j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, 1 / (v : ℚ) ^ s

-- VERBATIM PoleFun.lean:58-59  tauXs
noncomputable def tauXs (s : ℕ) (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  C (tauS s (polyPart A Pl)) + ∑ r ∈ Pl, C (resP A Pl r) * (C (Hs s (dd r)) - X)

end

section
-- VERBATIM DirectBound.lean:29-30  numOf
noncomputable def numOf (κ : ℚ) (Z : Multiset ℤ) : ℚ[X] :=
  C κ * (Z.map fun ζ : ℤ => X - C (ζ : ℚ)).prod

-- VERBATIM DirectBound.lean:34-34  cnt
def cnt (p : ℕ) (Z : Multiset ℤ) (c : ZMod p) : ℕ := (Z.filter fun ζ : ℤ => (ζ : ZMod p) = c).card

-- VERBATIM DirectBound.lean:38-38  plc
def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ := Pl.filter fun r : ℤ => (r : ZMod p) = c

-- VERBATIM DirectBound.lean:152-153  Sep
def Sep (p : ℕ) (Pl : Finset ℤ) : Prop :=
  ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬ (p : ℤ) ^ 2 ∣ r - s

end

section
-- VERBATIM Base.lean:12-12  D
noncomputable def D (m : ℕ) : ℚ[X] := ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2))

-- VERBATIM Base.lean:15-16  res
noncomputable def res (K : ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)

end

section
-- VERBATIM Monomial.lean:58-60  μmonoS
def μmonoS (s e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) *
    (((2 * e + s).factorial : ℚ) / ((2 * e + 2).factorial : ℚ)) / ((s - 1).factorial : ℚ)

-- VERBATIM Monomial.lean:64-64  μpolyS
noncomputable def μpolyS (s : ℕ) (P : ℚ[X]) : ℚ := P.sum fun e c => c * μmonoS s e

end

section
-- VERBATIM Pullback.lean:86-87  PlK
def PlK (K : ℕ) : Finset ℤ :=
  (Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))

-- VERBATIM Pullback.lean:247-248  poleValueS
noncomputable def poleValueS (s j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ (s - 1)) * (X - C (Hs s j)) - C (1 / ((s : ℚ) - 1)) + C (1 / (2 * (j : ℚ)))

-- VERBATIM Pullback.lean:252-255  μXS
noncomputable def μXS (s K : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (μpolyS s (P /ₘ D K)) +
    ∑ j ∈ Icc 1 K,
      C (P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)) * poleValueS s j

end

section
-- VERBATIM BasisChange.lean:90-91  GS
noncomputable def GS (s ν K N h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => μXS s K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ)))

-- VERBATIM BasisChange.lean:94-94  ΔS
noncomputable def ΔS (s ν K N h : ℕ) : ℚ[X] := (GS s ν K N h).det

end

section
-- VERBATIM SmallPrimeF.lean:212-214  SS
noncomputable def SS (ν K N h : ℕ) : ℚ :=
  (K.factorial : ℚ) ^ (2 * h) * 4 ^ (h - 1) /
    ((N.factorial : ℚ) ^ (2 * ν * h) * ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2)

-- VERBATIM SmallPrimeF.lean:217-217  FS
noncomputable def FS (s ν K N h : ℕ) : ℚ[X] := C (SS ν K N h) * ΔS s ν K N h

end

section
variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
-- VERBATIM ClassCount.lean:27-28  ccls
def ccls (hm : 2 * m + 1 = p) (c : ZMod p) : Fin (m + 1) :=
  if h : c.val ≤ m then ⟨c.val, by omega⟩ else ⟨p - c.val, by have := c.val_lt; omega⟩

-- VERBATIM ClassCount.lean:99-101  SX
def SX (p X : ℕ) (c : ZMod p) : ℕ :=
  ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = c).card +
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = -c).card

-- VERBATIM ClassCount.lean:115-117  BseS
noncomputable def BseS (s ν : ℕ) (p K N : ℕ) (a : ℕ) : ℚ :=
  (if a = 0 then (s : ℚ) else 0) + (ν : ℚ) * (SX p N (((a : ℤ) : ZMod p)) : ℚ) -
    SX p K (((a : ℤ) : ZMod p))

end

section
variable {m : ℕ}
-- VERBATIM InnerWeights.lean:25-26  topwS
noncomputable def topwS (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (a : Fin (m + 1)) : ℚ :=
  L a + (b a - ℓ) / 2

-- VERBATIM InnerWeights.lean:30-31  tminS
noncomputable def tminS (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) : ℚ :=
  (Finset.univ.erase (0 : Fin (m + 1))).inf' ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩ (topwS ℓ L b)

-- VERBATIM InnerWeights.lean:133-134  wrawS
noncomputable def wrawS (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - ℓ) / 2 else (s.2 : ℚ) + (b s.1 - ℓ) / 2

-- VERBATIM InnerWeights.lean:138-140  wcapS
noncomputable def wcapS (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  min (wrawS ℓ L b s) (tminS ℓ hm L b)

end

section
variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable (hm : 2 * m + 1 = p) (σ ν N K : ℕ)
-- VERBATIM OuterBasis.lean:25-25  jc
def jc (hm : 2 * m + 1 = p) (j : ℕ) : Fin (m + 1) := ccls hm (((j : ℤ) : ZMod p))

-- VERBATIM OuterBasis.lean:51-51  tailO
def tailO (N K : ℕ) : Finset ℕ := Icc (N + 1) (K)

-- VERBATIM OuterBasis.lean:54-54  tailC
def tailC (c : Fin (m + 1)) : Finset ℕ := (tailO N K).filter fun j => jc hm j = c

-- VERBATIM OuterBasis.lean:57-57  LoC
def LoC (c : Fin (m + 1)) : ℕ := (tailC hm N K c).card

-- VERBATIM OuterBasis.lean:60-60  bigC
def bigC (c : Fin (m + 1)) : Finset ℕ := (tailC hm N K c).filter fun j => p < j

-- VERBATIM OuterBasis.lean:63-63  nbC
def nbC (c : Fin (m + 1)) : ℕ := (bigC hm N K c).card

end

section
variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable (hm : 2 * m + 1 = p) (σ ν N K : ℕ)
-- VERBATIM OuterEntryMain.lean:97-97  ellC
def ellC (c : Fin (m + 1)) : ℕ := ((Icc 1 (K)).filter fun j => jc hm j = c).card

-- VERBATIM OuterEntryMain.lean:101-101  delC
def delC (c : Fin (m + 1)) : ℕ := if (c : ℕ) ≤ N then 1 else 0

-- VERBATIM OuterEntryMain.lean:105-107  wO
noncomputable def wO (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  if c = 0 then (if i < nbC hm N K 0 then -2 else if nbC hm N K 0 = 0 then -1 / 2 else 0)
  else (if i < nbC hm N K c then min 0 ((i : ℚ) + ((ν : ℚ) / 2) * delC N c - ((ellC hm K c : ℚ) + ((σ : ℚ) - 1)) / 2) else 0)

end

section
-- VERBATIM OuterScope.lean:14-14  momentCutS
def momentCutS (s p : ℕ) : ℕ := ((s - 1) / 2) * (p - 1) - 1

end

end AperyS
namespace AperyS.AssemblyTarget
noncomputable section

section
-- VERBATIM AssemblyData.lean:24-24  Allocations
abbrev Allocations := (p : ℕ) → Fin (p / 2 + 1) → ℕ

-- VERBATIM AssemblyData.lean:26-26  degreeBound
def degreeBound (s ν K N : ℕ) : ℕ := s + 2 * (ν * N) + 4 * ((K - N) - 1)

-- VERBATIM AssemblyData.lean:28-30  Lsmall
def Lsmall (s ν K N p : ℕ) : ℤ :=
  -(((s + 1 : ℕ) : ℤ) * (K - N : ℕ) * Nat.log p (degreeBound s ν K N + 1) +
    (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℤ))

-- VERBATIM AssemblyData.lean:32-32  vSK
def vSK (ν K N p : ℕ) : ℤ := padicValRat p (SS ν K N (K - N))

-- VERBATIM AssemblyData.lean:34-40  InnerOK
def InnerOK (s ν K N p : ℕ) (L : Allocations) : Prop :=
  ∃ hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2,
    s ≤ p ∧ Sep p (PlK K) ∧ K < p ^ 2 ∧
    s + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2 ∧
    ∑ c, L p c = K - N ∧
    tminS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) ≤
      2 * (L p 0 : ℚ) + (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2

-- VERBATIM AssemblyData.lean:42-46  WI
def WI (s ν K N p : ℕ) (L : Allocations) : ℚ := by
  classical
  exact if hm1 : 1 ≤ p / 2 then
    ∑ x, wcapS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) x
  else 0

-- VERBATIM AssemblyData.lean:48-49  OuterOK
def OuterOK (s K N p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ s ≤ p ∧ 7 ≤ p ∧ K < 3 * p ∧ 2 * K < p ^ 2 ∧ N < p

-- VERBATIM AssemblyData.lean:51-59  WO
def WO (s ν K N p : ℕ) : ℚ := by
  classical
  exact if hpp : p.Prime then
    letI : Fact p.Prime := ⟨hpp⟩
    if hm : 2 * (p / 2) + 1 = p then
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1)) : ℕ) : ℚ)
    else 0
  else 0

-- VERBATIM AssemblyData.lean:61-68  Lp
def Lp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WO s ν K N p⌋
  else Lsmall s ν K N p

-- VERBATIM AssemblyData.lean:72-72  primeBound
def primeBound (s K N : ℕ) : ℕ := max 7 (max s (2 * (K - N)))

-- VERBATIM AssemblyData.lean:74-76  normalizer
def normalizer (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-Lp s ν K N M p L)

-- VERBATIM AssemblyData.lean:80-86  LocalValuationStatement
def LocalValuationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∀ (p : ℕ) (_ : Fact p.Prime),
      GV p (FS s ν K N (K - N)) (Lp s ν K N M p L)

-- VERBATIM AssemblyData.lean:90-96  NormalizationStatement
def NormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizer s ν K N M L) * FS s ν K N (K - N)

end

end
end AperyS.AssemblyTarget

```

## Record the human verdict

For each declaration you read, record the declaration name, pass/partial/fail, your name, and the claim you compared it with. Example board entry (fill your own name and verdict):

```text
DONE human-read evidence/L-human-check/SHEET.md, AperyS.AssemblyTarget.normalization_statement by <name>: pass; statement matches the finite raw normalization claim, differences above retained.
```

Only the integrator upgrades the corresponding claim after that board record. Agent source checks and the Kimi review remain supporting evidence.
