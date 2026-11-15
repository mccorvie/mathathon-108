import Bounds

/- E426 Codex inner_regularity. PROOF-DRAFT genuine actual-model integrals.
Global measurability follows the proved finite-cell expression, and finite
interval integrability follows the actual compact bounds. -/
open MeasureTheory Set Filter Topology Finset
namespace BInnerLimit
noncomputable section
open Mathathon.P108

theorem measurable_modelVector (ν α : ℝ) : Measurable (modelVector ν α) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp only [modelVector, Tc, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ] <;> fun_prop

theorem measurable_innerR (s ν α : ℝ) : Measurable (innerR s ν α) := by
  have heq : innerR s ν α = fun x => rCell s ν α (modelVector ν α x) := by
    funext x
    exact innerR_eq_rCell s ν α x
  rw [heq]
  exact (continuous_rCell s ν α).measurable.comp (measurable_modelVector ν α)

theorem measurable_innerWeight (s ν : ℝ) : Measurable (innerWeight s ν) :=
  measurable_id.mul ((measurable_innerR s ν (3 / 40)).comp measurable_inv)

theorem intervalIntegrable_innerWeight (s ν : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    IntervalIntegrable (innerWeight s ν) volume (1 / (M : ℝ)) (1 / 3) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hab : 1 / (M : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)
  obtain ⟨C, hC⟩ := innerWeight_bounded s ν hM
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply IntegrableOn.of_bound (measure_Ioc_lt_top.ne.lt_top)
    (measurable_innerWeight s ν).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  rw [Real.norm_eq_abs]
  exact hC y ⟨hy.1.le, hy.2⟩

theorem intervalIntegrable_innerR_div_cube (s ν : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    IntervalIntegrable (fun x => innerR s ν (3 / 40) x / x ^ 3) volume 3 M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨C, hC⟩ := innerR_bounded s ν (3 / 40) (M : ℝ) hMR.le
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hM : (3 : ℝ) ≤ M)]
  have hm : Measurable (fun x => innerR s ν (3 / 40) x / x ^ 3) :=
    (measurable_innerR s ν (3 / 40)).div (measurable_id.pow_const 3)
  apply IntegrableOn.of_bound (measure_Ioc_lt_top.ne.lt_top) hm.aestronglyMeasurable (max C 0)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hc := hC x (by rw [abs_of_pos hx0]; exact hx.2)
  have hc' : |innerR s ν (3 / 40) x| ≤ max C 0 := hc.trans (le_max_left _ _)
  have hpow : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ (by linarith [hx.1])
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx0 3)]
  apply (div_le_iff₀ (pow_pos hx0 3)).mpr
  calc
    _ ≤ max C 0 := hc'
    _ = max C 0 * 1 := (mul_one _).symm
    _ ≤ max C 0 * x ^ 3 := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

#print axioms intervalIntegrable_innerWeight
#print axioms intervalIntegrable_innerR_div_cube
end
end BInnerLimit
