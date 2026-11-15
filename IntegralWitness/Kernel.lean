import IntegralWitness.Field
import IntegralWitness.PairBound

/-! E215/U20. Every new mathematical declaration has status PROOF-DRAFT. -/
noncomputable section
namespace U20
open MeasureTheory Set Real
open Mathathon.P108.ArcMeasure

def kernel (b d : ℝ) : ℝ :=
  ∫ x,∫ y,Real.log |x-y| ∂arcsineMeasure 0 d ∂arcsineMeasure 0 b

lemma pair_integrable {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|)
      ((arcsineMeasure 0 b).prod (arcsineMeasure 0 d)) := by
  obtain ⟨C,hC⟩ := Mathathon.P108.ArcPairs.arc_point_abs_log_le
    (m:=d/2) (r:=d/2) (R:=b) (by linarith)
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|)
      ((arcsineMeasure 0 b).prod (arcsineMeasure 0 d)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards [] with x
    exact log_integrable hd x
  · refine Integrable.mono' (integrable_const (C/(2*π))) hm.norm.integral_prod_right' ?_
    filter_upwards [arcsineMeasure_ae_mem hb.le] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
    simp only [Real.norm_eq_abs]
    rw [integral_arcsineMeasure 0 d _ (by fun_prop)]
    have hn : ‖(x:ℂ)‖≤b := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
    have hc := hC (x:ℂ) hn
    have he : (∫ θ in (0:ℝ)..2*π,|Real.log (|x-realCurve 0 d θ|)|)≤C := by
      simpa only [realCurve,Apery.arcCurve,zero_add,sub_zero,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hc
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0≤(2*π)⁻¹)
    simpa only [div_eq_mul_inv,mul_comm] using hmul

lemma kernel_symm {b d : ℝ} (hb : 0<b) (hd : 0<d) : kernel b d=kernel d b := by
  unfold kernel
  rw [MeasureTheory.integral_integral_swap (pair_integrable hb hd)]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  rw [abs_sub_comm]

lemma kernel_of_le {b d : ℝ} (hb : 0<b) (hd : 0<d) (hbd : b≤d) :
    kernel b d=Real.log (d/4) := by
  unfold kernel
  have he : (fun x=>∫ y,Real.log |x-y| ∂arcsineMeasure 0 d)=ᵐ[arcsineMeasure 0 b]
      (fun _=>Real.log (d/4)) := by
    filter_upwards [arcsineMeasure_ae_mem hb.le] with x hx
    rw [log_potential_eq_closed hd,
      Mathathon.P108.UTranslation.closedPotential_of_mem hx.1 (hx.2.trans hbd)]
    simp
  rw [integral_congr_ae he]
  simp

/-- PROOF-DRAFT: nested actual pushforward mutual energy. -/
theorem kernel_eq {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    kernel b d=Real.log (max b d/4) := by
  rcases le_total b d with h | h
  · rw [max_eq_right h,kernel_of_le hb hd h]
  · rw [max_eq_left h,kernel_symm hb hd,kernel_of_le hd hb h]

end U20
#check U20.kernel_eq
#print axioms U20.kernel_eq
#print axioms U20.pair_integrable
