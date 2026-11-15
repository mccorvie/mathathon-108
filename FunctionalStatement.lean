import Finish

/-! B9/E411 interface target, Codex lane B. CONJECTURE until a proof is provided.
Actual definitions are imported unchanged from the byte-copied frozen B8/L closure.
-/
open MeasureTheory Set Polynomial
namespace BAnalyticFunctional

/-- The literal rational-function density integrand, without an abstract measure replacement. -/
noncomputable def integrand (s K : ℕ) (P : ℚ[X]) (y : ℝ) : ℝ :=
  aeval (y ^ 2) P / aeval (y ^ 2) (AperyS.D K) * BAnalyticMoments.w s y

/-- Exact functional-interface target: all natural s>=2, arbitrary K and P. -/
def FunctionalStatement : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (K : ℕ) (P : ℚ[X]),
    IntegrableOn (integrand s K P) (Ioi 0) ∧
      aeval (BAnalyticPoles.zetaS s) (AperyS.μXS s K P) = ∫ y in Ioi 0, integrand s K P y

#print BAnalyticFunctional.FunctionalStatement
end BAnalyticFunctional
