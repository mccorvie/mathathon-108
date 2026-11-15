import ArcMeasure
import FieldAverage.Field
import Witness.Sign

/-! E215/U20, Codex. Every new mathematical declaration carries status PROOF-DRAFT.
Whole E201 and universal U*(6) remain CONJECTURE. Measures are angular pushforwards. -/
noncomputable section
namespace U20
open MeasureTheory Set Real
open Mathathon.P108.ArcMeasure

lemma realCurve_zero (b θ : ℝ) : realCurve 0 b θ=U16.node b θ := by
  unfold realCurve U16.node
  ring

lemma J_measurable {a : ℝ} (ha : 0≤a) : Measurable (U16.J a) := by
  have h : Measurable (fun p : ℝ×ℝ=>Real.log (p.1+p.2^2)) := by fun_prop
  have hi := h.stronglyMeasurable.integral_prod_right'
    (ν:=volume.restrict (Ioc (0:ℝ) a))
  change Measurable (fun t : ℝ=>∫ u in (0:ℝ)..a,Real.log (t+u^2))
  simpa only [intervalIntegral.integral_of_le ha] using hi.measurable

lemma V6_measurable : Measurable U16.V6 := by
  unfold U16.V6
  have hs : Measurable (fun t : ℝ=>Real.sqrt t) := by fun_prop
  exact ((hs.const_mul _).add (J_measurable (by norm_num))).sub
    ((J_measurable (by norm_num)).const_mul _)

lemma integrable_arcsine_of_interval (a b : ℝ) (f : ℝ→ℝ) (hf : Measurable f)
    (hi : IntervalIntegrable (fun θ=>f (realCurve a b θ)) volume 0 (2*π)) :
    Integrable f (arcsineMeasure a b) := by
  have hj := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0:ℝ)≤2*π)).mp hi
  have hs : Integrable (fun θ=>f (realCurve a b θ)) angleMeasure :=
    hj.smul_measure (ENNReal.inv_ne_top.mpr (by positivity))
  exact (integrable_map_measure hf.aestronglyMeasurable
    (realCurve_continuous a b).measurable.aemeasurable).mpr hs

lemma V6_integrable {b : ℝ} (hb : 0<b) : Integrable U16.V6 (arcsineMeasure 0 b) := by
  apply integrable_arcsine_of_interval 0 b U16.V6 V6_measurable
  simp_rw [realCurve_zero]
  have hs : IntervalIntegrable (fun θ=>Real.sqrt (U16.node b θ)) volume 0 (2*π) :=
    (by unfold U16.node; fun_prop : Continuous (fun θ : ℝ=>Real.sqrt (U16.node b θ))).intervalIntegrable _ _
  exact ((hs.const_mul _).add (U16.J_curve_intervalIntegrable (by norm_num) hb)).sub
    ((U16.J_curve_intervalIntegrable (by norm_num) hb).const_mul _)

/-- PROOF-DRAFT: the actual pushforward field integral equals the finite closed expression. -/
theorem field_integral {b : ℝ} (hb : 0<b) :
    (∫ t,U16.V6 t ∂arcsineMeasure 0 b)=U16.W b := by
  rw [integral_arcsineMeasure 0 b U16.V6 V6_measurable]
  simp_rw [realCurve_zero]
  exact U16.V6_angular_mean hb

lemma W_eq_U11 (b : ℝ) : U16.W b=U11.W b := by
  rfl

end U20
#check U20.field_integral
#print axioms U20.field_integral
#print axioms U20.V6_integrable
