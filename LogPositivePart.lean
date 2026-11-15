import ExtendedPotential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
/-! E233/U38, Codex, lane U. Every mathematical claim in this file has status
CONJECTURE pending parent gate and human statement comparison. The exact shared
U37.logPlus declaration is copied from U-extended-potential/brief.md.
This file proves only positive-part finiteness, without EReal/logMinus bridges,
atomlessness, self-energy, numerical or field-majorant assumptions. -/
set_option autoImplicit false
noncomputable section
namespace U38
open MeasureTheory Set Real
open scoped ENNReal

/-- CONJECTURE: a pointwise real upper envelope, including t=y. -/
lemma log_le_envelope {t y R : ℝ} (hy : |y|≤R) :
    Real.log |t-y| ≤ |t|+max R 0 := by
  calc
    Real.log |t-y| ≤ |t-y| := Real.log_le_self (abs_nonneg _)
    _ ≤ |t|+|y| := abs_sub t y
    _ ≤ |t|+max R 0 := add_le_add le_rfl (hy.trans (le_max_left R 0))

/-- CONJECTURE: the exact shared positive kernel is bounded pointwise on a bounded carrier. -/
lemma logPlus_le_envelope {t y R : ℝ} (hy : |y|≤R) :
    U37.logPlus t y ≤ ENNReal.ofReal (|t|+max R 0) := by
  unfold U37.logPlus
  exact ENNReal.ofReal_le_ofReal (log_le_envelope hy)

/-- CONJECTURE: an explicit positive-part integral bound; finiteness is not assumed here. -/
theorem logPlus_lintegral_le (mu : Measure ℝ) {R : ℝ}
    (hR : ∀ᵐ y ∂mu, |y|≤R) (t : ℝ) :
    (∫⁻ y,U37.logPlus t y ∂mu) ≤
      ENNReal.ofReal (|t|+max R 0)*mu Set.univ := by
  calc
    (∫⁻ y,U37.logPlus t y ∂mu) ≤
        ∫⁻ _y,ENNReal.ofReal (|t|+max R 0) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hR] with y hy
      exact logPlus_le_envelope hy
    _ = _ := lintegral_const _

/-- CONJECTURE: positive-part finiteness for every t under only finite mass and ae boundedness. -/
theorem logPlus_lintegral_ne_top (mu : Measure ℝ) [IsFiniteMeasure mu] {R : ℝ}
    (hR : ∀ᵐ y ∂mu, |y|≤R) (t : ℝ) :
    (∫⁻ y,U37.logPlus t y ∂mu) ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top mu Set.univ))
    (logPlus_lintegral_le mu hR t)


end U38
#print axioms U38.log_le_envelope
#print axioms U38.logPlus_le_envelope
#print axioms U38.logPlus_lintegral_le
#print axioms U38.logPlus_lintegral_ne_top
#print U37.logPlus
