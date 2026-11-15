import IntegralWitness
import UArcsinePairs

/-! E220/U25, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
Whole E201 remains CONJECTURE. These are angular-pushforward measures, not a density identity. -/
noncomputable section
namespace U25
open MeasureTheory Set Real Finset
open Mathathon.P108.ArcMeasure
open Mathathon.P108.FiniteDuality

def mutualEnergy (a b c d : ℝ) : ℝ :=
  ∫ x,∫ y,Real.log |x-y| ∂arcsineMeasure c d ∂arcsineMeasure a b

lemma potential_measurable {a b : ℝ} (hab : a<b) :
    Measurable (fun x=>∫ y,Real.log |x-y| ∂arcsineMeasure a b) := by
  simp_rw [log_potential_eq_closed hab]
  unfold Mathathon.P108.UTranslation.closedPotential Mathathon.P108.UTranslation.intervalDistance
  have hd : Continuous (fun x : ℝ=>Real.sqrt (max (a-x) (max 0 (x-b))/(b-a))) := by fun_prop
  exact (continuous_const.add ((Real.continuous_arsinh.comp hd).const_mul 2)).measurable

lemma pair_integrable {a b c d : ℝ} (hab : a<b) (hcd : c<d) :
    Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|)
      ((arcsineMeasure a b).prod (arcsineMeasure c d)) := by
  obtain ⟨C,hC⟩ := Mathathon.P108.ArcPairs.arc_point_abs_log_le
    (m:=(c+d)/2) (r:=(d-c)/2) (R:=|a|+|b|) (by linarith)
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|)
      ((arcsineMeasure a b).prod (arcsineMeasure c d)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards [] with x
    exact log_integrable hcd x
  · refine Integrable.mono' (integrable_const (C/(2*π))) hm.norm.integral_prod_right' ?_
    filter_upwards [arcsineMeasure_ae_mem hab.le] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
    simp only [Real.norm_eq_abs]
    rw [integral_arcsineMeasure c d _ (by fun_prop)]
    have hn : ‖(x:ℂ)‖≤|a|+|b| := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
      constructor <;> linarith [hx.1,hx.2,le_abs_self a,le_abs_self b,neg_abs_le a,neg_abs_le b]
    have hc := hC (x:ℂ) hn
    have he : (∫ θ in (0:ℝ)..2*π,|Real.log (|x-realCurve c d θ|)|)≤C := by
      simpa only [realCurve,Apery.arcCurve,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hc
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0≤(2*π)⁻¹)
    simpa only [div_eq_mul_inv,mul_comm] using hmul

variable {ι : Type*} [Fintype ι]

def curves (a b : ι→ℝ) :=
  Mathathon.P108.ArcPairs.family (fun i=>(a i+b i)/2) (fun i=>(b i-a i)/2)

def K (a b : ι→ℝ) : ι→ι→ℝ := curveKernel (curves a b)

lemma kernel_eq (a b : ι→ℝ) (hab : ∀ i,a i<b i) (i j : ι) :
    mutualEnergy (a i) (b i) (a j) (b j)=K a b i j := by
  unfold mutualEnergy
  rw [integral_arcsineMeasure _ _ _ (potential_measurable (hab j))]
  have hin (x : ℝ) : (∫ y,Real.log |x-y| ∂arcsineMeasure (a j) (b j))=
      (2*π)⁻¹*∫ θ in (0:ℝ)..2*π,Real.log |x-realCurve (a j) (b j) θ| :=
    integral_arcsineMeasure (a j) (b j) _ (by fun_prop)
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul]
  unfold K curveKernel Apery.pairInt curves Mathathon.P108.ArcPairs.family
  simp only [Apery.arcCurve,realCurve,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hp : (2*π:ℝ)≠0 := by positivity
  field_simp
  <;> ring

end U25
#print axioms U25.pair_integrable
#print axioms U25.kernel_eq
