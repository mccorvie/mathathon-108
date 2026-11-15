/-
E232/U37, lane U. Author: Kimi (Moonshot AI); driver: Codex for Ryan.
All mathematical declarations have status PROOF-DRAFT pending the local gate
and human statement comparison. The worker source follows byte for byte after
this attribution header. Whole E201/I4 remain CONJECTURE; no novelty claim.
Original received source and compiler log remain in ../worker/.
-/
import Mathlib

noncomputable section
namespace U37
open MeasureTheory Set Real
open scoped ENNReal NNReal

def logPlus (t y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.log |t-y|)
def logMinus (t y : ℝ) : ℝ≥0∞ :=
  if t=y then ⊤ else ENNReal.ofReal (-Real.log |t-y|)
def extendedPotential (mu : Measure ℝ) (t : ℝ) : EReal :=
  ENNReal.toEReal (∫⁻ y, logPlus t y ∂mu) -
    ENNReal.toEReal (∫⁻ y, logMinus t y ∂mu)

lemma lintegral_logMinus_eq (mu : Measure ℝ) [NullSingletonClass mu] (t : ℝ) :
    (∫⁻ y, logMinus t y ∂mu) = ∫⁻ y, ENNReal.ofReal (-Real.log |t-y|) ∂mu := by
  apply lintegral_congr_ae
  filter_upwards [mu.ae_ne t] with y hy
  simp [logMinus, Ne.symm hy]

lemma lintegral_logPlus_ne_top {mu : Measure ℝ} {t : ℝ}
    (hf : Integrable (fun y => Real.log |t-y|) mu) :
    (∫⁻ y, logPlus t y ∂mu) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hf.hasFiniteIntegral.ne
  exact lintegral_ofReal_le_lintegral_enorm _

lemma lintegral_logMinus_ne_top {mu : Measure ℝ} [NullSingletonClass mu] {t : ℝ}
    (hf : Integrable (fun y => Real.log |t-y|) mu) :
    (∫⁻ y, logMinus t y ∂mu) ≠ ⊤ := by
  rw [lintegral_logMinus_eq]
  apply ne_top_of_le_ne_top hf.neg.hasFiniteIntegral.ne
  exact lintegral_ofReal_le_lintegral_enorm _

/-- PROOF-DRAFT: at an ordinarily integrable point, the extended potential is
exactly the coercion of the ordinary real logarithmic integral. -/
theorem extendedPotential_eq_integral {mu : Measure ℝ} [IsFiniteMeasure mu]
    [NullSingletonClass mu] (t : ℝ)
    (hf : Integrable (fun y => Real.log |t-y|) mu) :
    extendedPotential mu t = (((∫ y, Real.log |t-y| ∂mu) : ℝ) : EReal) := by
  let A : ℝ≥0∞ := ∫⁻ y, logPlus t y ∂mu
  let B : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (-Real.log |t-y|) ∂mu
  have hA : A ≠ ⊤ := lintegral_logPlus_ne_top hf
  have hB : B ≠ ⊤ := by
    have hm := lintegral_logMinus_ne_top (mu := mu) (t := t) hf
    rw [lintegral_logMinus_eq] at hm
    exact hm
  have hAB : ENNReal.toEReal A - ENNReal.toEReal B =
      ((A.toReal - B.toReal : ℝ) : EReal) := by
    calc
      ENNReal.toEReal A - ENNReal.toEReal B =
          (A.toReal : EReal) - (B.toReal : EReal) := by
        rw [EReal.coe_ennreal_toReal hA, EReal.coe_ennreal_toReal hB]
      _ = ((A.toReal - B.toReal : ℝ) : EReal) := (EReal.coe_sub _ _).symm
  rw [extendedPotential, lintegral_logMinus_eq]
  change ENNReal.toEReal A - ENNReal.toEReal B = _
  rw [hAB, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  rfl

/-- PROOF-DRAFT: qualified transfer of an extended-real majorant to the
ordinary real integral, only at points satisfying ordinary integrability. -/
theorem real_majorant_of_extendedPotential_le {mu : Measure ℝ} [IsFiniteMeasure mu]
    [NullSingletonClass mu] (V : ℝ → ℝ) (H : ℝ)
    (h : ∀ t, 0 ≤ t →
      (2 : EReal) * extendedPotential mu t - (V t : EReal) ≤ (H : EReal)) :
    ∀ t, 0 ≤ t → Integrable (fun y => Real.log |t-y|) mu →
      2 * (∫ y, Real.log |t-y| ∂mu) - V t ≤ H := by
  intro t ht hf
  have h' := h t ht
  rw [extendedPotential_eq_integral t hf] at h'
  apply EReal.coe_le_coe_iff.mp
  change (2 : EReal) * (((∫ y, Real.log |t-y| ∂mu) : ℝ) : EReal) - (V t : EReal) ≤ (H : EReal)
  exact h'

#print axioms lintegral_logMinus_eq
#print axioms lintegral_logPlus_ne_top
#print axioms lintegral_logMinus_ne_top
#print axioms extendedPotential_eq_integral
#print axioms real_majorant_of_extendedPotential_le

end U37
