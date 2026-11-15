import FiniteComparison
import DensityTransport
/-! E225/U30, Codex. Every new mathematical claim in this file has status
CONJECTURE pending parent gate and human statement comparison. This proves
regularity/averaging for the fixed square15 trial against a bounded finite
Borel measure. It assumes no desired zero-mass energy inequality. -/
set_option autoImplicit false
noncomputable section
namespace U30
open MeasureTheory Set Real
open Mathathon.P108.ArcMeasure

/-- CONJECTURE: every nondegenerate arcsine component is atomless by its density. -/
theorem arcsine_noAtoms {a b : ℝ} (hab : a<b) :
    NullSingletonClass (arcsineMeasure a b) := by
  rw [U27.arcsineMeasure_eq_density hab]
  infer_instance

/-- CONJECTURE: the actual fixed square15 trial has no atoms. -/
theorem sigma_noAtoms : NullSingletonClass U20.sigma := by
  refine ⟨fun x => ?_⟩
  have hz (j : Fin 15) : U20.atom j {x}=0 := by
    unfold U20.atom
    haveI := arcsine_noAtoms (U20.width_pos j)
    exact measure_singleton x
  simp only [U20.sigma,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    hz,mul_zero,Finset.sum_const_zero]

/-- CONJECTURE: the fixed trial is almost everywhere nonnegative. -/
lemma sigma_ae_nonnegative : ∀ᵐ x ∂U20.sigma, 0≤x := by
  rw [U20.sigma,←Measure.sum_fintype,Measure.ae_sum_iff]
  intro j
  apply Measure.ae_smul_measure
  change ∀ᵐ x ∂arcsineMeasure 0 (U11.width j), 0≤x
  filter_upwards [arcsineMeasure_ae_mem (U20.width_pos j).le] with x hx
  exact hx.1

variable (mu : Measure ℝ) [IsFiniteMeasure mu]

/-- CONJECTURE: bounded outer finite measures have an integrable mixed log kernel.
Adapted from E220 U25.pair_integrable: replace its outer arc support by hR. -/
theorem mixed_arc_integrable {a b R : ℝ} (hab : a<b)
    (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun p : ℝ×ℝ => Real.log |p.1-p.2|)
      (mu.prod (arcsineMeasure a b)) := by
  obtain ⟨C,hC⟩ := Mathathon.P108.ArcPairs.arc_point_abs_log_le
    (m:=(a+b)/2) (r:=(b-a)/2) (R:=R) (by linarith)
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => Real.log |p.1-p.2|)
      (mu.prod (arcsineMeasure a b)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards [] with x
    exact log_integrable hab x
  · refine Integrable.mono' (integrable_const (C/(2*Real.pi))) hm.norm.integral_prod_right' ?_
    filter_upwards [hR] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Real.norm_eq_abs]
    rw [integral_arcsineMeasure a b _ (by fun_prop)]
    have hn : ‖(x:ℂ)‖≤R := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx
    have hc := hC (x:ℂ) hn
    have he : (∫ theta in (0:ℝ)..2*Real.pi,
        |Real.log (|x-realCurve a b theta|)|)≤C := by
      simpa only [realCurve,Apery.arcCurve,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hc
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0≤(2*Real.pi)⁻¹)
    simpa only [div_eq_mul_inv,mul_comm] using hmul

/-- CONJECTURE: the mixed log kernel is integrable against mu times the actual trial. -/
theorem mixed_sigma_integrable {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun p : ℝ×ℝ => Real.log |p.1-p.2|) (mu.prod U20.sigma) := by
  rw [U20.sigma,←Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro j _
  rw [Measure.prod_smul_right]
  exact (mixed_arc_integrable mu (U20.width_pos j) hR).smul_measure ENNReal.ofReal_ne_top

/-- CONJECTURE: the actual trial times mu has an integrable mixed log kernel. -/
theorem sigma_prod_mu_integrable {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun p : ℝ×ℝ => Real.log |p.1-p.2|) (U20.sigma.prod mu) := by
  simpa only [Function.comp_def,Prod.fst_swap,Prod.snd_swap,abs_sub_comm] using (mixed_sigma_integrable mu hR).swap

/-- CONJECTURE: absolute-log integrability in the first mixed orientation. -/
theorem mixed_sigma_abs_integrable {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun p : ℝ×ℝ => |Real.log (|p.1-p.2|)|) (mu.prod U20.sigma) := by
  simpa only [Real.norm_eq_abs] using (mixed_sigma_integrable mu hR).norm

/-- CONJECTURE: absolute-log integrability in the reverse mixed orientation. -/
theorem sigma_prod_mu_abs_integrable {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun p : ℝ×ℝ => |Real.log (|p.1-p.2|)|) (U20.sigma.prod mu) := by
  simpa only [Real.norm_eq_abs] using (sigma_prod_mu_integrable mu hR).norm

/-- CONJECTURE: the arbitrary finite comparison potential is integrable over the trial. -/
theorem potential_mu_integrable_sigma {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R) :
    Integrable (fun x => ∫ y,Real.log |x-y| ∂mu) U20.sigma :=
  (sigma_prod_mu_integrable mu hR).integral_prod_left

/-- CONJECTURE: the actual pointwise field majorant averages over the square15 trial. -/
theorem averaged_field_bound {R : ℝ} (hR : ∀ᵐ x ∂mu, |x|≤R)
    (H : ℝ) (hfield : ∀ t,0≤t → 2*(∫ y,Real.log |t-y| ∂mu)-U16.V6 t≤H) :
    2*(∫ x,∫ y,Real.log |x-y| ∂mu ∂U20.sigma) -
      (∫ x,U16.V6 x ∂U20.sigma) ≤ U11.lam*H := by
  have hp := potential_mu_integrable_sigma mu hR
  have hm : (∫ x,2*(∫ y,Real.log |x-y| ∂mu)-U16.V6 x ∂U20.sigma) ≤
      ∫ x,H ∂U20.sigma := by
    apply integral_mono_ae ((hp.const_mul 2).sub U20.sigma_field_integrable) (integrable_const H)
    filter_upwards [sigma_ae_nonnegative] with x hx
    exact hfield x hx
  have hmass : U20.sigma.real Set.univ=U11.lam := by
    change (U20.sigma Set.univ).toReal=U11.lam
    rw [U20.sigma_mass,ENNReal.toReal_ofReal (by norm_num [U11.lam])]
  rw [integral_sub (hp.const_mul 2) U20.sigma_field_integrable,
    integral_const_mul,integral_const,hmass,smul_eq_mul] at hm
  exact hm

end U30
#print axioms U30.arcsine_noAtoms
#print axioms U30.sigma_noAtoms
#print axioms U30.sigma_ae_nonnegative
#print axioms U30.mixed_arc_integrable
#print axioms U30.mixed_sigma_integrable
#print axioms U30.sigma_prod_mu_integrable
#print axioms U30.mixed_sigma_abs_integrable
#print axioms U30.sigma_prod_mu_abs_integrable
#print axioms U30.potential_mu_integrable_sigma
#print axioms U30.averaged_field_bound
#print axioms U27.arcsineMeasure_eq_density
