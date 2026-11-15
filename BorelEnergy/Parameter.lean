import BorelEnergy.LogLimit

/-! E223/U28, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
General finite-measure adaptation of prior Apery/ZeroMass.lean:228-281 (original numbering).
This is a Fubini bridge, not a zero-mass energy inequality. Whole E201 remains CONJECTURE. -/
noncomputable section
namespace U28
open MeasureTheory Set Real

lemma parameter_joint_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0<a) :
    Integrable (fun q : (ℝ×ℝ)×ℝ=>(Real.exp (-q.2)-gauss q.2 q.1.1 q.1.2)/q.2)
      ((μ.prod ν).prod (volume.restrict (Ioc a b))) := by
  have hS : ∀ᵐ q ∂((μ.prod ν).prod (volume.restrict (Ioc a b))),q.2∈Ioc a b :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall (fun _=>ae_restrict_mem measurableSet_Ioc))
  refine (integrable_const (2/a)).mono' (by apply Measurable.aestronglyMeasurable;unfold gauss;fun_prop) ?_
  filter_upwards [hS] with q hq
  have hs : 0<q.2 := ha.trans hq.1
  have hg := gauss_le_one hs.le q.1.1 q.1.2
  have he : Real.exp (-q.2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hn : |Real.exp (-q.2)-gauss q.2 q.1.1 q.1.2|≤2 := by
    have hn := abs_sub (Real.exp (-q.2)) (gauss q.2 q.1.1 q.1.2)
    rw [abs_of_pos (Real.exp_pos _),abs_of_pos (show 0<gauss q.2 q.1.1 q.1.2 by unfold gauss;positivity)] at hn
    linarith
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hs]
  calc
    _≤2/q.2 := div_le_div_of_nonneg_right hn hs.le
    _≤2/a := (div_le_div_iff₀ hs ha).mpr (by linarith [hq.1])

/-- PROOF-DRAFT: the parameter integral is genuinely integrable, without compact support. -/
theorem parameter_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun s=>∫ p : ℝ×ℝ,(Real.exp (-s)-gauss s p.1 p.2)/s ∂μ.prod ν) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (parameter_joint_integrable μ ν ha).integral_prod_right

/-- PROOF-DRAFT: arbitrary finite-measure truncated-kernel/Gaussian Fubini identity. -/
theorem truncated_swap (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p : ℝ×ℝ,Apery.Ltr a b |p.1-p.2| ∂μ.prod ν)=
      (1/2)*∫ s in a..b,∫ p : ℝ×ℝ,(Real.exp (-s)-gauss s p.1 p.2)/s ∂μ.prod ν := by
  have h := integral_integral_swap (μ:=μ.prod ν) (ν:=volume.restrict (Ioc a b))
    (f:=fun (p : ℝ×ℝ) (s : ℝ)=>(Real.exp (-s)-gauss s p.1 p.2)/s)
    (parameter_joint_integrable μ ν ha)
  unfold Apery.Ltr
  simp_rw [sq_abs,intervalIntegral.integral_of_le hab]
  rw [integral_const_mul]
  exact congrArg (fun v : ℝ=>(1/2)*v) h

end U28
#print axioms U28.parameter_joint_integrable
#print axioms U28.truncated_swap
