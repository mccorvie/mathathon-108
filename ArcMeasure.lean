import ArcBridge.Identification

/-!
E212 / U17. Author: Codex driver for Ryan, lane U, event work 2026-11-14.
All mathematical declarations in this file carry status PROOF-DRAFT pending
parent gate and human statement comparison. Whole E200/E201 remain CONJECTURE.
This defines the measure by angular pushforward; no density identity is claimed.
The imported angular-potential proof is attributed prior work; see E209 maps.
-/

noncomputable section
namespace Mathathon.P108.ArcMeasure
open MeasureTheory Real Set

/-- Normalized Lebesgue measure on the angular interval. -/
def angleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

instance angleMeasure_probability : IsProbabilityMeasure angleMeasure where
  measure_univ := by
    simp only [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

/-- Real-axis arcsine parametrization. -/
def realCurve (a b theta : ℝ) : ℝ := (a + b) / 2 + (b - a) / 2 * Real.cos theta

lemma realCurve_continuous (a b : ℝ) : Continuous (realCurve a b) := by
  unfold realCurve
  fun_prop

lemma realCurve_mem {a b : ℝ} (hab : a ≤ b) (theta : ℝ) :
    realCurve a b theta ∈ Icc a b := by
  have hr : 0 ≤ (b-a)/2 := by linarith
  have hlo := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos theta) hr
  have hhi := mul_le_mul_of_nonneg_left (Real.cos_le_one theta) hr
  dsimp [realCurve]
  constructor <;> nlinarith

/-- Probability measure defined by angular pushforward, not by a density formula. -/
def arcsineMeasure (a b : ℝ) : Measure ℝ := Measure.map (realCurve a b) angleMeasure

instance arcsineMeasure_probability (a b : ℝ) : IsProbabilityMeasure (arcsineMeasure a b) :=
  (Measure.isProbabilityMeasure_map_iff (realCurve_continuous a b).measurable.aemeasurable).2 inferInstance

lemma arcsineMeasure_ae_mem {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ t ∂arcsineMeasure a b, t ∈ Icc a b := by
  change ∀ᵐ t ∂Measure.map (realCurve a b) angleMeasure, t ∈ Icc a b
  exact (ae_map_iff (p := fun t => t ∈ Icc a b)
    (realCurve_continuous a b).measurable.aemeasurable measurableSet_Icc).mpr
    (Filter.Eventually.of_forall (realCurve_mem hab))

lemma arcsineMeasure_translate (a b e : ℝ) :
    Measure.map (fun t => t+e) (arcsineMeasure a b) =
      arcsineMeasure (a+e) (b+e) := by
  unfold arcsineMeasure
  rw [Measure.map_map (by fun_prop) (realCurve_continuous a b).measurable]
  congr 1
  funext theta
  dsimp [Function.comp_def, realCurve]
  ring

lemma angle_integral (f : ℝ → ℝ) :
    (∫ theta, f theta ∂angleMeasure) =
      (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..2 * Real.pi, f theta := by
  rw [angleMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity)]

lemma integral_arcsineMeasure (a b : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂arcsineMeasure a b) =
      (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..2 * Real.pi, f (realCurve a b theta) := by
  rw [arcsineMeasure, integral_map (realCurve_continuous a b).measurable.aemeasurable
    hf.aestronglyMeasurable, angle_integral]

lemma log_integrable {a b : ℝ} (hab : a < b) (x : ℝ) :
    Integrable (fun t => Real.log |x-t|) (arcsineMeasure a b) := by
  have hr : 0 < (b-a)/2 := by linarith
  have hi : IntervalIntegrable (fun theta => Real.log |x - realCurve a b theta|)
      volume 0 (2*Real.pi) := by
    simpa only [realCurve, Apery.arcCurve, ←Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using
      (Apery.arc_log_integrable (z := (x : ℂ)) (m := (a+b)/2) hr)
  have hj := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0:ℝ) ≤ 2*Real.pi)).mp hi
  have hs : Integrable (fun theta => Real.log |x-realCurve a b theta|) angleMeasure :=
    hj.smul_measure (ENNReal.inv_ne_top.mpr (by positivity))
  have hm : Measurable (fun t : ℝ => Real.log |x-t|) :=
    Real.measurable_log.comp (measurable_const.sub measurable_id).abs
  apply (integrable_map_measure hm.aestronglyMeasurable
    (realCurve_continuous a b).measurable.aemeasurable).mpr
  exact hs

lemma log_potential_eq_closed {a b : ℝ} (hab : a < b) (x : ℝ) :
    (∫ t, Real.log |x - t| ∂arcsineMeasure a b) =
      Mathathon.P108.UTranslation.closedPotential a b x := by
  rw [integral_arcsineMeasure a b _ (by fun_prop)]
  exact U14.angular_mean_closed hab x

lemma log_potential_translation {a b e : ℝ} (hab : a < b) (he : 0 ≤ e) (x : ℝ) :
    |(∫ t, Real.log |x + e - t| ∂arcsineMeasure a b) -
      (∫ t, Real.log |x - t| ∂arcsineMeasure a b)| ≤
      2 * Real.sqrt (e / (b - a)) := by
  rw [log_potential_eq_closed hab, log_potential_eq_closed hab]
  exact Mathathon.P108.UTranslation.closedPotential_translation hab he x

end Mathathon.P108.ArcMeasure

#print axioms Mathathon.P108.ArcMeasure.log_potential_eq_closed
#print axioms Mathathon.P108.ArcMeasure.log_potential_translation
#print axioms Mathathon.P108.ArcMeasure.log_integrable
#print axioms Mathathon.P108.ArcMeasure.arcsineMeasure_probability
#print axioms Mathathon.P108.ArcMeasure.arcsineMeasure_ae_mem
