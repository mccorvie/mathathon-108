import FieldAverage.Fubini

/-! E211/U16. Every new mathematical declaration has status PROOF-DRAFT.
This discharges the actual product-integrability input used by the field Fubini step. -/
noncomputable section
namespace U16
open Real Set MeasureTheory

lemma log_node_intervalIntegrable {b : ℝ} (hb : 0<b) :
    IntervalIntegrable (fun θ=>Real.log (node b θ)) volume 0 (2*π) := by
  have h := Apery.arc_log_integrable (z:=(0:ℂ)) (m:=b/2) (r:=b/2) (by linarith)
  have he : (fun θ=>Real.log ‖(0:ℂ)-Apery.arcCurve (b/2) (b/2) θ‖)=
      (fun θ=>Real.log (node b θ)) := by
    funext θ
    simp only [zero_sub,norm_neg,Apery.arcCurve,Complex.norm_real,Real.norm_eq_abs]
    rw [←show node b θ=b/2+b/2*Real.cos θ by unfold node; ring,
      abs_of_nonneg (node_nonneg hb.le θ)]
  rwa [he] at h

lemma node_pos_ae {b : ℝ} (hb : 0<b) :
    ∀ᵐ θ ∂(volume:Measure ℝ),0<node b θ := by
  have hz := (Apery.cos_preimage_countable (-1)).measure_zero (volume:Measure ℝ)
  filter_upwards [compl_mem_ae_iff.mpr hz] with θ hθ
  have hn : Real.cos θ≠-1 := by simpa using hθ
  have hc : -1<Real.cos θ := lt_of_le_of_ne (Real.neg_one_le_cos θ) (Ne.symm hn)
  unfold node
  exact div_pos (mul_pos hb (by linarith)) (by norm_num)

lemma log_pair_bound {a b θ u : ℝ} (ha : 0≤a) (hb : 0<b)
    (hn : 0<node b θ) (hu : u∈Ioc (0:ℝ) a) :
    |Real.log (node b θ+u^2)|≤|Real.log (node b θ)|+|Real.log (b+a^2)| := by
  have hnhi : node b θ≤b := by
    unfold node
    nlinarith [Real.cos_le_one θ]
  have hq : 0<node b θ+u^2 := by positivity
  have hqhi : node b θ+u^2≤b+a^2 := by nlinarith [hu.1,hu.2]
  have hlo := Real.log_le_log hn (show node b θ≤node b θ+u^2 by nlinarith)
  have hhi := Real.log_le_log hq hqhi
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (node b θ)),
    neg_abs_le (Real.log (node b θ)),le_abs_self (Real.log (b+a^2)),neg_abs_le (Real.log (b+a^2))]

/-- PROOF-DRAFT: the logarithmic endpoint is harmless for the two-variable field integral. -/
theorem joint_integrable {a b : ℝ} (ha : 0≤a) (hb : 0<b) : jointIntegrable a b := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*π))
  let ν : Measure ℝ := volume.restrict (Ioc (0:ℝ) a)
  have hlog : Integrable (fun θ=>Real.log (node b θ)) μ := (log_node_intervalIntegrable hb).1
  have hg : Integrable (fun θ=>|Real.log (node b θ)|+|Real.log (b+a^2)|) μ :=
    hlog.abs.add (integrable_const _)
  have hG := hg.comp_fst ν
  have hf : AEStronglyMeasurable (fun p : ℝ×ℝ=>Real.log (node b p.1+p.2^2)) (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    unfold node
    fun_prop
  have hm : MeasurableSet {p : ℝ×ℝ | ‖Real.log (node b p.1+p.2^2)‖≤
      |Real.log (node b p.1)|+|Real.log (b+a^2)|} := by
    unfold node
    measurability
  have hbound : ∀ᵐ p ∂μ.prod ν, ‖Real.log (node b p.1+p.2^2)‖≤
      |Real.log (node b p.1)|+|Real.log (b+a^2)| := by
    apply (Measure.ae_prod_iff_ae_ae hm).2
    filter_upwards [ae_restrict_of_ae (node_pos_ae hb)] with θ hθ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa only [Real.norm_eq_abs] using log_pair_bound ha hb hθ hu
  have hi := hG.mono' hf hbound
  unfold jointIntegrable IntegrableOn
  rw [uIoc_of_le (by positivity : (0:ℝ)≤2*π),uIoc_of_le ha]
  rw [Measure.volume_eq_prod,←Measure.prod_restrict]
  exact hi

/-- PROOF-DRAFT: the complete angular average of the original J integral. -/
theorem J_angular_mean {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    angularAverage b (J a)=T a b :=
  J_angular_mean_of_integrable ha hb (joint_integrable ha hb)

end U16
#check U16.joint_integrable
#print axioms U16.joint_integrable
#check U16.J_angular_mean
#print axioms U16.J_angular_mean
