import InnerModelTargets
/- E426 Codex inner_regularity, lane B. PROOF-DRAFT until parent gate.
CITED proof pattern: PRIOR Deicyde/zeta7-irrational@be55b3a4,
PrimeSumBound.lean593-632. Parameterized against the actual rootinnerR.
No regularity, integrability or desired limiting bound is a premise. -/
open MeasureTheory Set Filter Topology
namespace BInnerLimit
noncomputable section
open Mathathon.P108

theorem inner_weight_identity (s ν : ℝ) {y : ℝ} (hy : y ≠ 0) :
    innerR s ν (3 / 40) y⁻¹ / y⁻¹ ^ 3 * -(y ^ 2)⁻¹ = -(y * innerR s ν (3 / 40) y⁻¹) := by
  have h : y ^ 3 * (y ^ 2)⁻¹ = y := by
    rw [← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hy)]
    ring
  rw [inv_pow, div_inv_eq_mul]
  linear_combination (-(innerR s ν (3 / 40) y⁻¹)) * h

/-- The change of variables `x = 1/y`: `∫_{1/M}^{1/3} y R(1/y) dy = ∫_3^M R(x)/x³ dx`. -/
theorem integral_inner_weight (s ν : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    ∫ y in (1 / (M : ℝ))..(1 / 3), innerWeight s ν y = ∫ x in (3 : ℝ)..M, innerR s ν (3 / 40) x / x ^ 3 := by
  unfold innerWeight
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ha : (0 : ℝ) < 1 / M := one_div_pos.mpr hM0
  have hab : 1 / (M : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)
  have hpos : ∀ y ∈ Set.uIcc (1 / (M : ℝ)) (1 / 3), 0 < y := fun y hy => by
    rw [Set.uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  have hpos' : ∀ y ∈ Set.Ioo (min (1 / (M : ℝ)) (1 / 3)) (max (1 / (M : ℝ)) (1 / 3)),
      0 < y := fun y hy => by
    rw [min_eq_left hab] at hy
    exact lt_trans ha hy.1
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := 1 / (M : ℝ)) (b := 1 / 3) (f := fun y : ℝ => y⁻¹) (f' := fun y : ℝ => -(y ^ 2)⁻¹)
    (g := fun x : ℝ => innerR s ν (3 / 40) x / x ^ 3)
    (fun y hy => (continuousAt_inv₀ (hpos y hy).ne').continuousWithinAt)
    (fun y hy => hasDerivAt_inv (hpos' y hy).ne')
    (fun y _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg y)))
  simp only [Function.comp_apply] at key
  have e1 : (1 / (M : ℝ))⁻¹ = M := by rw [inv_div, div_one]
  have e2 : (1 / (3 : ℝ))⁻¹ = 3 := by norm_num
  have hcongr : ∫ x in (1 / (M : ℝ))..(1 / 3), innerR s ν (3 / 40) x⁻¹ / x⁻¹ ^ 3 * -(x ^ 2)⁻¹
      = ∫ x in (1 / (M : ℝ))..(1 / 3), -(x * innerR s ν (3 / 40) x⁻¹) :=
    intervalIntegral.integral_congr fun y hy => inner_weight_identity s ν (hpos y hy).ne'
  rw [e1, e2, hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_symm 3 (M : ℝ)]
    at key
  linarith

theorem inversion_statement : InversionStatement := by
  intro s ν M hM
  exact integral_inner_weight s ν hM
#print axioms integral_inner_weight
#print axioms inversion_statement
end
end BInnerLimit
