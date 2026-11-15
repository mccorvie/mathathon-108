import RangeTargets
import Mathathon.P108.SStep

/-!
E420, native Codex inner_explicit, lane B, 2026-11-14.
CONJECTURE TARGETS ONLY, approved C4 same-allocation scope.
The E405 source module RangeTargets is copied unchanged. No allocation,
selected exponent, root model or finite support has been replaced.
-/

open Filter Finset

namespace Mathathon.P108.InnerExplicitTarget

noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget

/-- CONJECTURE: matching lower bound for E405's literal explicit allocation.
This quantifies over no other allocation and asserts no optimization. -/
def InnerExplicitLocalLowerStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (p : ℕ), p.Prime → p ≤ primeBound s (40 * n) (3 * n) →
        40 * n < p * M → 3 * p ≤ 40 * n →
        let L := explicitAllocation s ν (40 * n) (3 * n) M
        (p : ℝ) * Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40)
              (((40 * n : ℕ) : ℝ) / (p : ℝ)) - C ≤
          -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)

/-- CONJECTURE: complete local two-sided identification, with InnerOK proved
eventually as a conclusion. C depends on fixed s,nu,M and not n,p. -/
def InnerExplicitLocalStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (p : ℕ), p.Prime → p ≤ primeBound s (40 * n) (3 * n) →
        40 * n < p * M → 3 * p ≤ 40 * n →
        let L := explicitAllocation s ν (40 * n) (3 * n) M
        InnerOK s ν (40 * n) (3 * n) p L ∧
          |(-(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)) -
              (p : ℝ) * Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40)
                (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤ C

/-- CONJECTURE: same explicit allocation, both aggregate cost directions. -/
def InnerExplicitLimitStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |innerPrimeLogContribution s ν (40 * n) (3 * n) M
            (explicitAllocation s ν (40 * n) (3 * n) M) /
          (((40 * n : ℕ) : ℝ) ^ 2) - innerIntegral s ν M| ≤ ε

/-- The arithmetic term of the actual thetaPkg, with its energy input zero. -/
def arithmeticPackage (s ν M : ℕ) : ℝ :=
  Mathathon.P108.thetaPkg (s : ℝ) (ν : ℝ) (3 / 40) (M : ℝ) 0

/-- CONJECTURE capstone: exact cost limit of the actual sharp normalizer
for the stated explicit allocation. No actual determinant valuation equality
or optimality among other allocations is asserted. -/
def ExplicitNormalizerLimitStatement : Prop :=
  ∀ (s ν M : ℕ), ParameterScope s ν → 40 ≤ M →
    Tendsto (fun n : ℕ =>
      Real.log ((normalizerSharp s ν (40 * n) (3 * n) M
        (explicitAllocation s ν (40 * n) (3 * n) M) : ℚ) : ℝ) /
          (((40 * n : ℕ) : ℝ) ^ 2)) atTop (nhds (arithmeticPackage s ν M))

/-- CONJECTURE corollary target: importing a proved scalar E213 margin later
would make this a certificate-family failure, not irrationality of zeta7.
The arithmetic limit itself remains an explicit named target. -/
def ZetaSevenExplicitMarginLimitStatement : Prop :=
  ∀ M : ℕ, 40 ≤ M → ∀ U : ℝ,
    Tendsto (fun n : ℕ => U +
      Real.log ((normalizerSharp 7 6 (40 * n) (3 * n) M
        (explicitAllocation 7 6 (40 * n) (3 * n) M) : ℚ) : ℝ) /
          (((40 * n : ℕ) : ℝ) ^ 2)) atTop
      (nhds (Mathathon.P108.thetaPkg 7 6 (3 / 40) (M : ℝ) U))

/-- CONJECTURE E213 corollary target: literal selected certificate margin
eventually exceeds9/10 for every fixed natural cutoffM>=40 and inputU>-139/100.
This combines the limit target with U18.theta_allM_gt; that scalar theorem is
not assumed as a proof of the unproved normalizer limit. -/
def ZetaSevenExplicitMarginPositiveStatement : Prop :=
  ∀ M : ℕ, 40 ≤ M → ∀ U : ℝ, (-139 : ℝ) / 100 < U →
    ∀ᶠ n : ℕ in atTop,
      (9 : ℝ) / 10 < U +
        Real.log ((normalizerSharp 7 6 (40 * n) (3 * n) M
          (explicitAllocation 7 6 (40 * n) (3 * n) M) : ℚ) : ℝ) /
            (((40 * n : ℕ) : ℝ) ^ 2)

#check InnerExplicitLocalLowerStatement
#check InnerExplicitLocalStatement
#check InnerExplicitLimitStatement
#check ExplicitNormalizerLimitStatement
#check ZetaSevenExplicitMarginLimitStatement
#check ZetaSevenExplicitMarginPositiveStatement

end
end Mathathon.P108.InnerExplicitTarget
