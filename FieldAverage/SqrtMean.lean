import FieldAverage.Primitive

/-! E211/U16. Every new mathematical declaration has status PROOF-DRAFT. -/
noncomputable section
namespace U16
open Real Set MeasureTheory

lemma integral_cos_half (a c : ℝ) :
    (∫ θ in a..c,Real.cos (θ/2))=2*Real.sin (c/2)-2*Real.sin (a/2) := by
  have hd : ∀ x : ℝ,HasDerivAt (fun y : ℝ=>2*Real.sin (y/2)) (Real.cos (x/2)) x := by
    intro x
    have h := (((hasDerivAt_id x).div_const (2:ℝ)).sin).const_mul (2:ℝ)
    apply h.congr_deriv
    dsimp
    ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hd x)
    ((by fun_prop : Continuous (fun θ : ℝ=>Real.cos (θ/2))).intervalIntegrable _ _)

lemma integral_abs_cos_half : (∫ θ in (0:ℝ)..2*π,|Real.cos (θ/2)|)=4 := by
  have hc : Continuous (fun θ : ℝ=>|Real.cos (θ/2)|) := by fun_prop
  rw [←intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 π)
    (hc.intervalIntegrable π (2*π))]
  have hl : (∫ θ in (0:ℝ)..π,|Real.cos (θ/2)|)=∫ θ in (0:ℝ)..π,Real.cos (θ/2) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by positivity : (0:ℝ)≤π)] at hθ
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2]⟩)
  have hr : (∫ θ in π..2*π,|Real.cos (θ/2)|)=∫ θ in π..2*π,-Real.cos (θ/2) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by linarith [Real.pi_pos] : π≤2*π)] at hθ
    exact abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2,Real.pi_pos]))
  rw [hl,hr,intervalIntegral.integral_neg,integral_cos_half,integral_cos_half]
  norm_num

lemma sqrt_node {b : ℝ} (hb : 0≤b) (θ : ℝ) :
    Real.sqrt (node b θ)=Real.sqrt b*|Real.cos (θ/2)| := by
  have hc := Real.cos_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc
  have hn : node b θ=b*(Real.cos (θ/2))^2 := by unfold node; nlinarith
  rw [hn,Real.sqrt_mul hb,Real.sqrt_sq_eq_abs]

/-- PROOF-DRAFT: the square-root angular mean, with exact normalization. -/
theorem sqrt_angular_mean {b : ℝ} (hb : 0<b) :
    (2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,Real.sqrt (node b θ))=2*Real.sqrt b/π := by
  simp_rw [sqrt_node hb.le]
  rw [intervalIntegral.integral_const_mul,integral_abs_cos_half]
  field_simp
  ring

end U16
#check U16.sqrt_angular_mean
#print axioms U16.sqrt_angular_mean
