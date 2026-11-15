import Functional
import Zeta5S.BasisChange

/-! B11/E413: actual Gram/positivity interface targets, Codex lane B.
CONJECTURE target definitions until proofs are supplied; no abstract matrix premise.
-/
open MeasureTheory Set Polynomial
namespace BAnalyticGram

noncomputable def gramWeight (s ν K N : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (AperyS.D N) ^ ν / aeval (y ^ 2) (AperyS.D K) * BAnalyticMoments.w s y

/-- Actual GS entries at the actual zeta sum are integrable monomial Gram entries. -/
def GramEntryStatement : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (ν K N h : ℕ) (i j : Fin h),
    IntegrableOn (fun y : ℝ => (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * gramWeight s ν K N y) (Ioi 0) ∧
      aeval (BAnalyticPoles.zetaS s) (AperyS.GS s ν K N h i j) =
        ∫ y in Ioi 0, (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * gramWeight s ν K N y

/-- The actual determinant is positive for all sizes, including the empty determinant. -/
def GramPositiveStatement : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (ν K N h : ℕ),
    0 < aeval (BAnalyticPoles.zetaS s) (AperyS.ΔS s ν K N h)

#print BAnalyticGram.GramEntryStatement
#print BAnalyticGram.GramPositiveStatement
end BAnalyticGram
