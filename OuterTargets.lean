import Zeta5S.SharpAssembly
import Zeta5S.InnerAlloc
import Mathathon.P108.OuterDefs
import Mathathon.P108.InnerShift

/-!
C4 / E405, Codex range_targets worker, lane B, 2026-11-14.
CONJECTURE TARGETS ONLY: these commands define propositions; they do not prove them.

Finite inputs are imported unchanged from lane L's sharp assembly E310/E311.
End2 inputs are the actual root Iout/Tout/innerR definitions, also unchanged.
The source import closure is copied byte-for-byte by prepare.py, with hashes
and original Firsching/Paul-Lez Apache-2.0 attribution in SOURCE_MANIFEST.json.

Architecture: mo271/Zeta5@be1c0d82, Apery/Norm.lean:37-48,
Apery/Growth/InnerPrime.lean:134-177,179-251 and
Apery/Growth/OuterPrime.lean:72-204; the sharp outer minimum is Fauzan's
min(rank, zero count), implemented in lane L's SharpOuterScope/SharpAssembly.
No proof of the asymptotic identification is inherited from those files.
-/

open Filter Finset

namespace Mathathon.P108.RangeBridgeTarget

noncomputable section

open AperyS AperyS.AssemblyTarget

/-- CONJECTURE target scope: the slice of E13 covered by its section8 repairs. -/
def ParameterScope (s ν : ℕ) : Prop :=
  Odd s ∧ 5 ≤ s ∧ Even ν ∧ 2 ≤ ν ∧ ν ≤ 10

/-- A derived range of the actual sharp normalizer, not a new exponent.
The strict outer boundary agrees with the selected LpSharp branch. -/
def outerPrimeLogContribution (s ν K N M : ℕ) (L : Allocations) : ℝ :=
  ∑ p ∈ (range (primeBound s K N + 1)).filter
      (fun p => p.Prime ∧ K < 3 * p),
    Real.log (p : ℝ) * (-(LpSharp s ν K N M p L : ℝ))

/-- The middle/inner range of that same sharp normalizer. -/
def innerPrimeLogContribution (s ν K N M : ℕ) (L : Allocations) : ℝ :=
  ∑ p ∈ (range (primeBound s K N + 1)).filter
      (fun p => p.Prime ∧ K < p * M ∧ 3 * p ≤ K),
    Real.log (p : ℝ) * (-(LpSharp s ν K N M p L : ℝ))

/-- Actual End2 integral on the fixed shape alpha=3/40. -/
def innerIntegral (s ν M : ℕ) : ℝ :=
  ∫ x in (3 : ℝ)..(M : ℝ),
    Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40) x / x ^ 3

/-! ## Outer range: allocation-independent, with both cost directions -/

/-- CONJECTURE: uniform O(1) local identification on the entire outer support.
The constant may depend on fixed s,nu; it is independent of n,p,M,L.
The max in the n threshold makes all small finite primes harmless without
assuming the desired OuterOK branch as a hypothesis. -/
def OuterLocalStatement : Prop :=
  ∀ (s ν : ℕ), ParameterScope s ν →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ), max 1 s ≤ n → ∀ (M : ℕ), 3 ≤ M →
        ∀ (L : Allocations) (p : ℕ), p.Prime →
          p ≤ primeBound s (40 * n) (3 * n) → 40 * n < 3 * p →
          |(-(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)) -
              ((40 * n : ℕ) : ℝ) *
                Mathathon.P108.Tout (s : ℝ) (ν : ℝ) (3 / 40)
                  ((p : ℝ) / ((40 * n : ℕ) : ℝ))| ≤ C

/-- CONJECTURE: the outer contribution converges to the actual Iout.
Both inequalities hold uniformly over every supplied allocation and M>=3.
This is a cost bound, not a statement about the actual determinant valuation. -/
def OuterLimitStatement : Prop :=
  ∀ (s ν : ℕ), ParameterScope s ν →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ (M : ℕ), 3 ≤ M → ∀ L : Allocations,
        Mathathon.P108.Iout (s : ℝ) (ν : ℝ) (3 / 40) - ε ≤
            outerPrimeLogContribution s ν (40 * n) (3 * n) M L /
              (((40 * n : ℕ) : ℝ) ^ 2) ∧
        outerPrimeLogContribution s ν (40 * n) (3 * n) M L /
              (((40 * n : ℕ) : ℝ) ^ 2) ≤
            Mathathon.P108.Iout (s : ℝ) (ν : ℝ) (3 / 40) + ε

/-- First statement to review/prove after the small-prime bridge. -/
def OuterBridgeStatement : Prop := OuterLocalStatement ∧ OuterLimitStatement

/-! ## Inner range: all-allocation lower bound; concrete-allocation upper bound -/

/-- Integer offsets of the actual ordinary row weights. This agrees with the
ordinary part of BseS-(s-1); its value at c=0 is unused by rowsK/allocK. -/
def beta (s ν K N p : ℕ) (c : Fin (p / 2 + 1)) : ℤ :=
  (ν : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) -
    (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) - ((s : ℤ) - 1)

/-- A concrete O_(s,nu,M)(1) zero-class reserve and search-window bound.
Its sufficiency is part of the unproved explicit-allocation target below. -/
def fillBudget (s ν M : ℕ) : ℕ := 4 * (s + ν + 1) * (M + 1)

/-- Fully specified bounded water filling, using upstream's actual kfSel/allocK.
There is no existential choice of an allocation satisfying a desired cost.
The large ordinary-class search window and zero reserve are held fixed as
n grows; the proposed n threshold is therefore only eventual. -/
def explicitAllocation (s ν K N M : ℕ) : Allocations :=
  fun p =>
    let β := beta s ν K N p
    let B := fillBudget s ν M
    let lo : ℤ := -(B : ℤ)
    let hi : ℤ := (B : ℤ) + 4 * (M : ℤ) + 4
    allocK β (K - N) (kfSel β (K - N) B lo hi)

/-- CONJECTURE: every allocation costs at least the actual innerR model,
up to one uniform O(1) local error. Invalid allocations select Lsmall;
the lower bound explicitly covers that fallback instead of assuming flags.
For a fixed cutoff M this error constant is independent of n,p,L. -/
def InnerAllAllocationsLocalLowerStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (L : Allocations) (p : ℕ), p.Prime →
        p ≤ primeBound s (40 * n) (3 * n) →
        40 * n < p * M → 3 * p ≤ 40 * n →
        (p : ℝ) * Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40)
              (((40 * n : ℕ) : ℝ) / (p : ℝ)) - C ≤
          -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)

/-- CONJECTURE: the specified water filling satisfies the actual InnerOK
predicate at every inner prime eventually, and its cost has the opposite
local bound. Flag validity is a conclusion, not a hypothesis hiding it. -/
def InnerExplicitLocalUpperStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (p : ℕ), p.Prime → p ≤ primeBound s (40 * n) (3 * n) →
        40 * n < p * M → 3 * p ≤ 40 * n →
        let L := explicitAllocation s ν (40 * n) (3 * n) M
        InnerOK s ν (40 * n) (3 * n) p L ∧
          -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ) ≤
            (p : ℝ) * Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40)
                (((40 * n : ℕ) : ℝ) / (p : ℝ)) + C

/-- CONJECTURE: the inner cost is bounded from below for every allocation,
and from above for the explicitly defined one. The one-sided formulation
does not incorrectly assert that bad allocations have the same limit. -/
def InnerLimitStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∀ L : Allocations,
        innerIntegral s ν M - ε ≤
          innerPrimeLogContribution s ν (40 * n) (3 * n) M L /
            (((40 * n : ℕ) : ℝ) ^ 2)) ∧
      innerPrimeLogContribution s ν (40 * n) (3 * n) M
            (explicitAllocation s ν (40 * n) (3 * n) M) /
          (((40 * n : ℕ) : ℝ) ^ 2) ≤ innerIntegral s ν M + ε

/-- Second review target; it includes the concrete allocation definition and
its eventual branch validity, not merely a scalar comparison assumption. -/
def InnerBridgeStatement : Prop :=
  InnerAllAllocationsLocalLowerStatement ∧
    InnerExplicitLocalUpperStatement ∧ InnerLimitStatement

#print OuterBridgeStatement
#print OuterLocalStatement
#print OuterLimitStatement
#print explicitAllocation
#print InnerBridgeStatement
#print InnerAllAllocationsLocalLowerStatement
#print InnerExplicitLocalUpperStatement
#print InnerLimitStatement

end
end Mathathon.P108.RangeBridgeTarget
