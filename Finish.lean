import Scaling
import Bose

/-! B8/E409 final assembly, Codex lane B. PROOF-DRAFT until repository gate.
Classical Gamma/Mittag-Leffler method; copied source attribution in NOTICE.
-/
open MeasureTheory Set Filter Topology Polynomial Finset
namespace BAnalyticPoles

lemma integral_remainder_evaluated (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-(a * t)) * ML.remainder t) =
      ((s - 1).factorial : ℝ) * zetaTail s a -
        ((s - 2).factorial : ℝ) / a ^ (s - 1) +
        (1 / 2) * (((s - 1).factorial : ℝ) / a ^ s) := by
  have hm : 1 ≤ s - 1 := by omega
  have hB := integrableOn_bose (s - 1) hm ha
  have hG0 := BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul (s - 2) ha
  have hG1 := BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul (s - 1) ha
  have hpt : ∀ t : ℝ, 0 < t →
      t ^ (s - 1) * Real.exp (-(a * t)) * ML.remainder t =
        (bose (s - 1) a t - t ^ (s - 2) * Real.exp (-(a * t))) +
          (1 / 2) * (t ^ (s - 1) * Real.exp (-(a * t))) := by
    intro t ht
    have hp : t ^ (s - 1) = t ^ (s - 2) * t := by
      have h := pow_add t (s - 2) 1
      simpa only [show s - 2 + 1 = s - 1 by omega, pow_one] using h
    have he : Real.exp t - 1 ≠ 0 := by linarith [Real.one_lt_exp_iff.mpr ht]
    unfold ML.remainder bose
    rw [hp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
  rw [integral_add (f := fun t : ℝ => bose (s - 1) a t - t ^ (s - 2) * Real.exp (-(a * t)))
    (g := fun t : ℝ => (1 / 2 : ℝ) * (t ^ (s - 1) * Real.exp (-(a * t))))
    (hB.sub hG0) (hG1.const_mul (1 / 2 : ℝ)), integral_sub hB hG0,
    integral_const_mul, integral_bose (s - 1) hm ha,
    BAnalyticIntegral.integral_pow_mul_exp_neg_mul (s - 2) ha,
    BAnalyticIntegral.integral_pow_mul_exp_neg_mul (s - 1) ha]
  simp only [zetaTail, show s - 2 + 1 = s - 1 by omega, show s - 1 + 1 = s by omega]

/-- The real-parameter pole identity for the actual density; no analytic premises. -/
theorem real_pole_identity (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) =
      a ^ (s - 1) * zetaTail s a - 1 / ((s : ℝ) - 1) + 1 / (2 * a) := by
  have h := integral_remainder_eq_pole s hs ha
  rw [integral_remainder_evaluated s hs ha] at h
  have hD : (((s - 1).factorial : ℝ) / a ^ (s - 1)) ≠ 0 := by positivity
  have hI : (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) =
      (((s - 1).factorial : ℝ) * zetaTail s a -
        ((s - 2).factorial : ℝ) / a ^ (s - 1) +
        (1 / 2) * (((s - 1).factorial : ℝ) / a ^ s)) /
          (((s - 1).factorial : ℝ) / a ^ (s - 1)) := by
    apply (eq_div_iff hD).2
    simpa only [mul_comm] using h.symm
  rw [hI]
  have hnat : (s - 1).factorial = (s - 1) * (s - 2).factorial := by
    rw [show s - 1 = (s - 2) + 1 by omega, Nat.factorial_succ]
  have hfac : ((s - 1).factorial : ℝ) = ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := by
    have hh : ((s - 1).factorial : ℝ) = ((s - 1 : ℕ) : ℝ) * ((s - 2).factorial : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one] using hh
  have hp : a ^ s = a ^ (s - 1) * a := by
    have hh := pow_add a (s - 1) 1
    simpa only [show s - 1 + 1 = s by omega, pow_one] using hh
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
  have hf : (0 : ℝ) < ((s - 2).factorial : ℝ) := by positivity
  rw [hfac, hp]
  field_simp

/-- Generalizes Apery/HermiteFormula.lean:76-95 from exponent5 to any natural s>=2. -/
lemma zetaTail_nat_eq (s : ℕ) (hs : 2 ≤ s) (j : ℕ) :
    zetaTail s j = zetaS s - (AperyS.Hs s j : ℝ) := by
  have hz : Summable (fun m : ℕ => 1 / (m : ℝ) ^ s) := Real.summable_one_div_nat_pow.mpr (by omega)
  have h := hz.sum_add_tsum_nat_add (j + 1)
  have hH : ∑ i ∈ range (j + 1), 1 / ((i : ℝ)) ^ s = (AperyS.Hs s j : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (by omega : s ≠ 0), div_zero, add_zero]
    unfold AperyS.Hs
    push_cast
    have e1 : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, Finset.sum_Ico_eq_sum_range, show j + 1 - 1 = j by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  have htail : zetaTail s j = ∑' n : ℕ, 1 / ((n + (j + 1) : ℕ) : ℝ) ^ s := by
    unfold zetaTail
    refine tsum_congr fun n => ?_
    push_cast; ring_nf
  rw [htail, ← hH]
  unfold zetaS
  linarith

/-- The actual-density pole moment equals the actual lane-L polynomial at the zeta sum. -/
theorem pole_identity (s : ℕ) (hs : 2 ≤ s) (j : ℕ) (hj : 1 ≤ j) :
    (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2)) =
      aeval (zetaS s) (AperyS.poleValueS s j) := by
  rw [real_pole_identity s hs (by exact_mod_cast hj : (0 : ℝ) < j),
    zetaTail_nat_eq s hs j, aeval_poleValueS]

/-- The exact target posted in Statement.lean, now with a proof. -/
theorem general_pole_statement : GeneralPoleStatement := by
  intro s _ hs j hj
  exact ⟨integrableOn_pole s (by omega) (by exact_mod_cast hj : (0 : ℝ) < j),
    pole_identity s (by omega) j hj⟩

theorem real_pole_statement : RealPoleStatement := by
  intro s hs a ha
  exact real_pole_identity s hs ha

#print axioms BAnalyticPoles.real_pole_identity
#print axioms BAnalyticPoles.pole_identity
#print axioms BAnalyticPoles.general_pole_statement
#print axioms BAnalyticPoles.real_pole_statement
end BAnalyticPoles
