import BAnalyticIntegral

/-!
E409 auxiliary Bose/Gamma identity, Codex lane B driver, event work.
PROOF-DRAFT until repository gate. Classical geometric-series and Gamma
argument; no novelty claimed. The Gamma helpers are imported from the
attributed B5 adaptation of Firsching/Paul-Lez mo271/Zeta5@be1c0d82.
-/
open MeasureTheory Set Filter Topology

namespace BAnalyticPoles

noncomputable def boseTerm (m n : ℕ) (a t : ℝ) : ℝ :=
  t ^ m * Real.exp (-((a + ((n : ℝ) + 1)) * t))

noncomputable def bose (m : ℕ) (a t : ℝ) : ℝ :=
  t ^ m * Real.exp (-(a * t)) / (Real.exp t - 1)

lemma bose_eq_tsum (m : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    bose m a t = ∑' n : ℕ, boseTerm m n a t := by
  have hr : |Real.exp (-t)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ n : ℕ, boseTerm m n a t =
      (t ^ m * Real.exp (-((a + 1) * t))) * Real.exp (-t) ^ n := by
    intro n
    unfold boseTerm
    rw [show -((a + ((n : ℝ) + 1)) * t) = -((a + 1) * t) + (n : ℝ) * (-t) by ring,
      Real.exp_add, Real.exp_nat_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr]
  have hexp : Real.exp (-((a + 1) * t)) = Real.exp (-(a * t)) * Real.exp (-t) := by
    rw [show -((a + 1) * t) = -(a * t) + -t by ring, Real.exp_add]
  rw [hexp]
  have he : Real.exp t ≠ 1 := ne_of_gt (Real.one_lt_exp_iff.mpr ht)
  have hratio : Real.exp (-t) * (1 - Real.exp (-t))⁻¹ = 1 / (Real.exp t - 1) := by
    rw [Real.exp_neg]
    field_simp
  unfold bose
  rw [show t ^ m * (Real.exp (-(a * t)) * Real.exp (-t)) * (1 - Real.exp (-t))⁻¹ =
    t ^ m * Real.exp (-(a * t)) * (Real.exp (-t) * (1 - Real.exp (-t))⁻¹) by ring,
    hratio]
  ring

lemma integrableOn_boseTerm (m n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (boseTerm m n a) (Ioi 0) := by
  exact BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul m (by positivity)

lemma integral_boseTerm (m n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, boseTerm m n a t) =
      (m.factorial : ℝ) / (a + ((n : ℝ) + 1)) ^ (m + 1) := by
  exact BAnalyticIntegral.integral_pow_mul_exp_neg_mul m (by positivity)

lemma summable_bose_integrals (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / (a + ((n : ℝ) + 1)) ^ (m + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (m + 1)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < m + 1))
    exact h.congr (fun n => by push_cast; ring)
  refine hbase.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) _

lemma summable_bose_integral_norm (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ∫ t in Ioi 0, ‖boseTerm m n a t‖) := by
  have hnorm : ∀ n : ℕ, (∫ t in Ioi 0, ‖boseTerm m n a t‖) =
      (∫ t in Ioi 0, boseTerm m n a t) := by
    intro n
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _))
  simp_rw [hnorm, integral_boseTerm m _ ha]
  simpa only [div_eq_mul_inv, one_mul] using
    (summable_bose_integrals m hm ha).mul_left (m.factorial : ℝ)

theorem integral_bose (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, bose m a t) =
      (m.factorial : ℝ) * ∑' n : ℕ, 1 / (a + ((n : ℝ) + 1)) ^ (m + 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => bose_eq_tsum m a ht),
    ← integral_tsum_of_summable_integral_norm (fun n => integrableOn_boseTerm m n ha)
      (summable_bose_integral_norm m hm ha)]
  simp_rw [integral_boseTerm m _ ha]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem integrableOn_bose (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (bose m a) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_bose m hm ha]
  apply ne_of_gt
  have hsum := (summable_bose_integrals m hm ha).tsum_pos
    (fun n => by positivity) 0 (by positivity)
  positivity

#print axioms integral_bose
#print axioms integrableOn_bose
end BAnalyticPoles
