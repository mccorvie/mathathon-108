import Zeta5S.Base

/-!
B9/E411: real partial fractions on the actual lane-L D/res definitions.
Verbatim from mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/PartialFractions.lean:85-116, Firsching/Paul-Lez, Apache-2.0.
Only enclosing namespace changes Apery -> AperyS. PROOF-DRAFT until gate.
-/
open Polynomial Finset
namespace AperyS
lemma aeval_D_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < aeval t (D m) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.prod_pos fun j hj => ?_
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  positivity

/-- **Partial fractions** as real functions, for `t ≥ 0`. -/
theorem partial_fractions (K : ℕ) (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    aeval t P / aeval t (D K) =
      aeval t (P /ₘ D K) + ∑ j ∈ Icc 1 K, (res K P j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hD : 0 < aeval t (D K) := aeval_D_pos K ht
  have hsplit : aeval t P = aeval t (P %ₘ D K) + aeval t (D K) * aeval t (P /ₘ D K) := by
    conv_lhs => rw [← modByMonic_add_div P (D K)]
    rw [map_add, map_mul]
  rw [hsplit, add_div, mul_div_cancel_left₀ _ hD.ne', add_comm]
  congr 1
  rw [modByMonic_eq_sum_res, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, aeval_C, map_prod]
  simp only [map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  have hj2 : 0 < t + (j : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    positivity
  have hDt : aeval t (D K) = (t + (j : ℝ) ^ 2) * ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) := by
    simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
    rw [← Finset.mul_prod_erase _ _ hj]
  rw [hDt]
  have hprod : 0 < ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) :=
    Finset.prod_pos fun i hi => by
      have : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      positivity
  field_simp
end AperyS
