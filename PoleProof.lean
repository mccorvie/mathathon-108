import Kernel
import Statement

/-! B8/E409 proof continuation, Codex lane B. PROOF-DRAFT until gate.
Classical Gamma/Mittag-Leffler route. Source and license: NOTICE.
-/
open MeasureTheory Set Filter Topology Polynomial
namespace BAnalyticPoles

noncomputable def mlTerm (s : ℕ) (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * t ^ s * Real.exp (-(a * t)) / (t ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2)

lemma mlTerm_nonneg (s : ℕ) (a : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mlTerm s a n t := by unfold mlTerm; positivity

lemma mlTerm_le (s : ℕ) (a : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    mlTerm s a n t ≤ (2 / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) *
      (t ^ s * Real.exp (-(a * t))) := by
  have hc : 0 < (2 * Real.pi * ((n : ℝ) + 1)) ^ 2 := by positivity
  unfold mlTerm
  calc 2 * t ^ s * Real.exp (-(a * t)) / (t ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2)
      ≤ 2 * t ^ s * Real.exp (-(a * t)) / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hc (by nlinarith [sq_nonneg t])
    _ = _ := by ring

lemma integrableOn_mlTerm (s : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (mlTerm s a n) (Ioi 0) := by
  have hdom := (BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul s ha).const_mul
    (2 / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2)
  have hm : Measurable (mlTerm s a n) := by unfold mlTerm; fun_prop
  refine hdom.mono' hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_of_nonneg (mlTerm_nonneg s a n (le_of_lt ht))]
  exact mlTerm_le s a n (le_of_lt ht)

lemma integral_norm_mlTerm_le (s : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ t in Ioi 0, ‖mlTerm s a n t‖) ≤
      ((2 / (2 * Real.pi) ^ 2) * ((s.factorial : ℝ) / a ^ (s + 1))) *
        (1 / ((n : ℝ) + 1) ^ 2) := by
  have hdom := (BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul s ha).const_mul
    (2 / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2)
  calc (∫ t in Ioi 0, ‖mlTerm s a n t‖)
      ≤ ∫ t in Ioi 0, (2 / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) *
          (t ^ s * Real.exp (-(a * t))) := by
        refine integral_mono_ae (integrableOn_mlTerm s ha n).norm hdom ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
        dsimp only
        rw [Real.norm_of_nonneg (mlTerm_nonneg s a n (le_of_lt ht))]
        exact mlTerm_le s a n (le_of_lt ht)
    _ = (2 / (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) * ((s.factorial : ℝ) / a ^ (s + 1)) := by
        rw [integral_const_mul, BAnalyticIntegral.integral_pow_mul_exp_neg_mul s ha]
    _ = _ := by
        have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp

lemma summable_integral_norm_mlTerm (s : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable fun n => ∫ t in Ioi 0, ‖mlTerm s a n t‖ := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact h.congr (fun n => by push_cast; ring)
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
    (fun n => integral_norm_mlTerm_le s ha n)
    (hp.mul_left ((2 / (2 * Real.pi) ^ 2) * ((s.factorial : ℝ) / a ^ (s + 1))))

/-- The weighted Bose remainder is the sum of positive scaled pole kernels. -/
lemma weighted_remainder_eq_tsum (s : ℕ) (hs : 2 ≤ s) {a t : ℝ} (ht : 0 < t) :
    t ^ (s - 1) * Real.exp (-(a * t)) * ML.remainder t = ∑' n, mlTerm s a n t := by
  rw [ML.remainder_eq_tsum ht, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold mlTerm
  have hp : t ^ s = t ^ (s - 1) * t := by
    have h := pow_add t (s - 1) 1
    simpa only [show s - 1 + 1 = s by omega, pow_one] using h
  rw [hp]
  ring

lemma integral_weighted_remainder_eq_tsum (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-(a * t)) * ML.remainder t) =
      ∑' n, ∫ t in Ioi 0, mlTerm s a n t := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => weighted_remainder_eq_tsum s hs ht)]
  exact (integral_tsum_of_summable_integral_norm
    (fun n => integrableOn_mlTerm s ha n) (summable_integral_norm_mlTerm s ha)).symm

end BAnalyticPoles
