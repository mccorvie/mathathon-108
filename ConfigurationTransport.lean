import PriorRegularization
import CompactTransports
/-! PROOF-DRAFT threshold parameterization by Codex, lane U51/E246. Adapted from Moritz Firsching, mo271/Zeta5@be1c0d82 Apery/EnergyFinal.lean157-214: only M0->T and pointwise_bound->explicit enhanced premise. Overall CONJECTURE; no human comparison. -/
open MeasureTheory Set Real Filter Topology Finset
namespace Apery
theorem energy_ineq_threshold (T : ℝ) (hEnhanced : U48.EnhancedFieldStatement T) (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Kr n * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (lam * T - Irho) * Kr n ^ 2 + 5 * (37 * n) + 6 * (37 * n) * Real.log (Kr n) := by
  have hK : 40 ≤ Kr n := by
    simp only [Kr]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : 0 < Kr n := by linarith
  set K := Kr n with hKdef
  set ε : ℝ := K ^ (-6 : ℤ) with hε_def
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε_def, zpow_neg, inv_le_one_iff₀]
    right; exact one_le_zpow₀ (by linarith) (by norm_num)
  have hsqrtε : Real.sqrt ε = K ^ (-3 : ℤ) := by
    have e : (K ^ (-3 : ℤ)) ^ 2 = ε := by
      rw [hε_def, ← zpow_natCast, ← zpow_mul]; norm_num
    rw [← e, Real.sqrt_sq (by positivity)]
  have hlogε : Real.log ε = -6 * Real.log K := by
    rw [hε_def, Real.log_zpow]; push_cast; ring
  have hraw := energy_raw n hn t hinj hε
  rw [← hKdef, U51.Prior.sum_pairs_eq, hlogε] at hraw
  -- bound the error terms
  have hErr : ∀ i, Err ε (t i) ≤ 1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348) := fun i => by
    have := U51.Prior.Err_le hε hε1 (ht i)
    rw [hsqrtε, zpow_neg, zpow_ofNat] at this
    rw [one_div]; exact this
  have hK2 : 1 / K ^ 2 ≤ 1 / 1600 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  -- pointwise
  have hpt : ∀ i, 2 * K * (Uρ (t i) + Err ε (t i)) - K * Vfield (t i) + Real.sqrt (t i) ≤
      K * T + 5 := by
    intro i
    have h1 := hEnhanced K (t i) hK (ht i)
    have h2 := hErr i
    have hs := Real.sqrt_nonneg (t i)
    have e1 : 2 * K * (1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348)) =
        1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) := by field_simp; ring
    have e2 : 1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) ≤
        1 / 1600 * (1180 * Real.sqrt (t i) + 2696) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have e3 : K * (2 / K * Real.sqrt (t i)) = 2 * Real.sqrt (t i) := by field_simp
    have e4 : K * (3 / K) = 3 := by field_simp
    have h1' := mul_le_mul_of_nonneg_left h1 hK0.le
    rw [mul_add, mul_add, mul_sub, e3, e4] at h1'
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * K)
    rw [e1] at h2'
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hraw
  have hlam : ((37 * n : ℕ) : ℝ) * (K * T) = lam * T * K ^ 2 := by
    rw [hKdef]; simp only [Kr, lam]; push_cast; ring
  rw [hlam] at hsum
  push_cast at hraw hsum ⊢
  linarith [hraw, hsum]

end Apery
namespace U51
/-- PROOF-DRAFT: exact parameterized configuration transport; no numerical certificate is a hidden premise. -/
theorem configuration_of_enhanced (T : ℝ) : U48.ConfigurationTransportGoal T := by
  intro hEnhanced n hn t ht hinj
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (Apery.energy_ineq_threshold T hEnhanced n (by omega) t ht hinj)

/-- PROOF-DRAFT: only the compact local-field leaf remains as a premise. -/
theorem configuration_tau_of_local : U48.LocalFieldStatement ((-1323:ℝ)/200) →
    U48.ConfigurationStatement ((-1323:ℝ)/200) := by
  intro hLocal
  exact configuration_of_enhanced _ (local_tau_to_enhanced hLocal)
end U51

#print axioms U51.Prior.sqrt_add_le'
#print axioms U51.Prior.errj_le
#print axioms U51.Prior.sum_cρ_fin
#print axioms U51.Prior.Err_le
#print axioms U51.Prior.sum_pairs_eq
#print axioms Apery.energy_ineq_threshold
#print axioms U51.configuration_of_enhanced
#print axioms U51.configuration_tau_of_local
#print axioms U51.local_to_enhanced
#print axioms U51.scalar_budget_literal
