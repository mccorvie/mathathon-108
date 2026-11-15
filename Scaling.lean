import PoleProof

/-! B8/E409: density-summand scaling, Codex lane B. PROOF-DRAFT until gate. -/
open MeasureTheory Set Filter Topology Polynomial
namespace BAnalyticPoles

noncomputable def deltaTerm (s : ℕ) (a : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  BAnalyticMoments.momTerm s 0 n y / (y ^ 2 + a ^ 2)

lemma deltaTerm_nonneg (s : ℕ) (a : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ deltaTerm s a n y := by
  unfold deltaTerm
  exact div_nonneg (BAnalyticMoments.momTerm_nonneg s 0 n hy) (by positivity)

lemma integrableOn_deltaTerm (s : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (deltaTerm s a n) (Ioi 0) := by
  have hm := BAnalyticMoments.integrableOn_momTerm s 0 n
  have hdom := hm.const_mul (1 / a ^ 2)
  have hmeas : Measurable (deltaTerm s a n) := by
    unfold deltaTerm BAnalyticMoments.momTerm; fun_prop
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_of_nonneg (deltaTerm_nonneg s a n hy)]
  have hpos := BAnalyticMoments.momTerm_nonneg s 0 n hy
  unfold deltaTerm
  calc BAnalyticMoments.momTerm s 0 n y / (y ^ 2 + a ^ 2)
      ≤ BAnalyticMoments.momTerm s 0 n y / a ^ 2 :=
        div_le_div_of_nonneg_left hpos (sq_pos_of_pos ha) (by nlinarith [sq_nonneg y])
    _ = _ := by ring

lemma integral_norm_deltaTerm_le (s : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ y in Ioi 0, ‖deltaTerm s a n y‖) ≤
      (1 / a ^ 2) * (∫ y in Ioi 0, ‖BAnalyticMoments.momTerm s 0 n y‖) := by
  rw [← integral_const_mul]
  refine integral_mono_ae (integrableOn_deltaTerm s ha n).norm
    ((BAnalyticMoments.integrableOn_momTerm s 0 n).norm.const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (deltaTerm_nonneg s a n hy),
    Real.norm_of_nonneg (BAnalyticMoments.momTerm_nonneg s 0 n hy)]
  have hpos := BAnalyticMoments.momTerm_nonneg s 0 n hy
  unfold deltaTerm
  calc BAnalyticMoments.momTerm s 0 n y / (y ^ 2 + a ^ 2)
      ≤ BAnalyticMoments.momTerm s 0 n y / a ^ 2 :=
        div_le_div_of_nonneg_left hpos (sq_pos_of_pos ha) (by nlinarith [sq_nonneg y])
    _ = _ := by ring

lemma summable_integral_norm_deltaTerm (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    Summable fun n => ∫ y in Ioi 0, ‖deltaTerm s a n y‖ :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => integral_norm_deltaTerm_le s ha n)
    ((BAnalyticMoments.summable_integral_norm s hs 0).mul_left (1 / a ^ 2))

lemma pole_eq_tsum (s : ℕ) (a y : ℝ) :
    BAnalyticMoments.w s y / (y ^ 2 + a ^ 2) = ∑' n, deltaTerm s a n y := by
  have h := BAnalyticMoments.monomial_eq_tsum s 0 y
  simp only [mul_zero, pow_zero, one_mul] at h
  rw [h, ← tsum_div_const]
  rfl

lemma integral_pole_eq_tsum (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) =
      ∑' n, ∫ y in Ioi 0, deltaTerm s a n y := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => pole_eq_tsum s a y)]
  exact (integral_tsum_of_summable_integral_norm (fun n => integrableOn_deltaTerm s ha n)
    (summable_integral_norm_deltaTerm s hs ha)).symm

lemma scaled_mlTerm (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) (n : ℕ) (y : ℝ) :
    (2 * Real.pi * ((n : ℝ) + 1) / a) *
      mlTerm s a n ((2 * Real.pi * ((n : ℝ) + 1) / a) * y) =
      (((s - 1).factorial : ℝ) / a ^ (s - 1)) * deltaTerm s a n y := by
  have hc : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
  have hf : 0 < ((s - 1).factorial : ℝ) := by positivity
  have he : a * ((2 * Real.pi * ((n : ℝ) + 1) / a) * y) =
      2 * Real.pi * ((n : ℝ) + 1) * y := by field_simp
  have hd : ((2 * Real.pi * ((n : ℝ) + 1) / a) * y) ^ 2 +
      (2 * Real.pi * ((n : ℝ) + 1)) ^ 2 =
      (2 * Real.pi * ((n : ℝ) + 1) / a) ^ 2 * (y ^ 2 + a ^ 2) := by field_simp
  have hp (b : ℝ) : b ^ s = b ^ (s - 1) * b := by
    have h := pow_add b (s - 1) 1
    simpa only [show s - 1 + 1 = s by omega, pow_one] using h
  unfold mlTerm deltaTerm BAnalyticMoments.momTerm
  simp only [mul_zero, zero_add]
  rw [he, hd, mul_pow, hp (2 * Real.pi * ((n : ℝ) + 1) / a)]
  simp only [mul_pow, div_pow]
  have hden : 0 < y ^ 2 + a ^ 2 := by positivity
  field_simp

lemma integral_mlTerm_scaled (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ t in Ioi 0, mlTerm s a n t) =
      (((s - 1).factorial : ℝ) / a ^ (s - 1)) * (∫ y in Ioi 0, deltaTerm s a n y) := by
  have hb : 0 < 2 * Real.pi * ((n : ℝ) + 1) / a := by positivity
  have hc := integral_comp_mul_left_Ioi' (mlTerm s a n) 0 hb
  simp only [mul_zero, smul_eq_mul] at hc
  calc (∫ t in Ioi 0, mlTerm s a n t)
      = (2 * Real.pi * ((n : ℝ) + 1) / a) *
          (∫ y in Ioi 0, mlTerm s a n ((2 * Real.pi * ((n : ℝ) + 1) / a) * y)) := hc.symm
    _ = ∫ y in Ioi 0, (2 * Real.pi * ((n : ℝ) + 1) / a) *
          mlTerm s a n ((2 * Real.pi * ((n : ℝ) + 1) / a) * y) := (integral_const_mul _ _).symm
    _ = ∫ y in Ioi 0, (((s - 1).factorial : ℝ) / a ^ (s - 1)) * deltaTerm s a n y :=
        setIntegral_congr_fun measurableSet_Ioi (fun y _ => scaled_mlTerm s hs ha n y)
    _ = _ := integral_const_mul _ _

/-- The exact bridge between the weighted Bose remainder and actual-density poles. -/
lemma integral_remainder_eq_pole (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-(a * t)) * ML.remainder t) =
      (((s - 1).factorial : ℝ) / a ^ (s - 1)) *
        (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) := by
  rw [integral_weighted_remainder_eq_tsum s hs ha]
  simp_rw [integral_mlTerm_scaled s hs ha]
  rw [tsum_mul_left, integral_pole_eq_tsum s hs ha]
end BAnalyticPoles
