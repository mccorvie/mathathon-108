import LogPositivePart
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FunProp
/-! E233/U38, Codex. Every mathematical claim has status CONJECTURE pending
parent gate and human statement comparison. Optional real positive-part corollary. -/
set_option autoImplicit false
noncomputable section
namespace U38
open MeasureTheory Set Real

/-- CONJECTURE: ordinary real positive-log integrability under the same two hypotheses. -/
theorem positiveLog_integrable (mu : Measure ℝ) [IsFiniteMeasure mu] {R : ℝ}
    (hR : ∀ᵐ y ∂mu, |y|≤R) (t : ℝ) :
    Integrable (fun y => max (Real.log |t-y|) 0) mu := by
  have hm : AEStronglyMeasurable (fun y => max (Real.log |t-y|) 0) mu := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine Integrable.mono' (integrable_const (|t|+max R 0)) hm ?_
  filter_upwards [hR] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (log_le_envelope hy) (add_nonneg (abs_nonneg t) (le_max_right R 0))


end U38
#print axioms U38.positiveLog_integrable
