import Mathlib

/-!
B5/E403 by Codex, lane B. PROOF-DRAFT: builds; repository gate pending.
No density, pole-moment or zeta identification claimed.
Adapted from mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Moritz Firsching and Paul-Lez, Apache-2.0 (LICENSE and NOTICE).
-/

open MeasureTheory Set Filter Topology
namespace BAnalyticIntegral

-- Verbatim helpers from Apery/Moments.lean:18-45; namespace changed.
lemma integral_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) = (m.factorial : ℝ) / r ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  have hL : ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) =
      ∫ t in Ioi 0, t ^ (m : ℝ) * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [Real.rpow_natCast]
  rw [hL, h]
  have : (1 / r) ^ ((m : ℝ) + 1) = (1 / r) ^ (m + 1) := by
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [this, one_div_pow, div_mul_eq_mul_div, one_mul]

lemma integrableOn_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ m * Real.exp (-(r * y))) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity)
  rw [add_sub_cancel_right] at h
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ (m : ℝ)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ (m : ℝ)) 0 hr).mpr
      (by simpa using h)
    simpa using this
  have h3 : IntegrableOn (fun x : ℝ => (1 / r ^ m) * (Real.exp (-(r * x)) * (r * x) ^ (m : ℝ)))
      (Ioi 0) := h2.const_mul _
  refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  simp only
  rw [Real.rpow_natCast, mul_pow]
  field_simp

/-- Natural-degree version of the split used in upstream Energy.lean:182-189. -/
lemma one_add_pow_le (s : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ s ≤ 2 ^ s * (1 + y ^ s) := by
  rcases le_or_gt y 1 with h | h
  · have hpow : (1 + y) ^ s ≤ 2 ^ s :=
      pow_le_pow_left₀ (by positivity) (by linarith) s
    exact hpow.trans (le_mul_of_one_le_right (by positivity) (by
      have := pow_nonneg hy s; linarith))
  · calc (1 + y) ^ s ≤ (2 * y) ^ s :=
          pow_le_pow_left₀ (by positivity) (by linarith) s
      _ = 2 ^ s * y ^ s := mul_pow _ _ _
      _ ≤ 2 ^ s * (1 + y ^ s) := by gcongr; linarith

noncomputable def g (s : ℕ) (a K y : ℝ) : ℝ :=
  (1 + a * y) ^ s * Real.exp (-(1 / K * y))

noncomputable def C (s : ℕ) (a : ℝ) : ℝ :=
  a ^ s * 2 ^ s * (1 + (s.factorial : ℝ))

/-- Generalizes upstream Energy.lean:175-195. -/
lemma g_le_dom (s : ℕ) {a K y : ℝ} (ha : 1 ≤ a) (hy : 0 ≤ y) :
    g s a K y ≤
      a ^ s * 2 ^ s * (y ^ 0 * Real.exp (-(1 / K * y))) +
      a ^ s * 2 ^ s * (y ^ s * Real.exp (-(1 / K * y))) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : (1 + a * y) ^ s ≤ a ^ s * (1 + y) ^ s := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) s
  have h2 := one_add_pow_le s hy
  unfold g
  calc (1 + a * y) ^ s * Real.exp (-(1 / K * y))
      ≤ a ^ s * (2 ^ s * (1 + y ^ s)) * Real.exp (-(1 / K * y)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg ha0 _))
    _ = _ := by simp only [pow_zero, one_mul]; ring

/-- Integrability is discharged rather than left as a premise. -/
lemma integrableOn_g (s : ℕ) {a K : ℝ} (ha : 1 ≤ a) (hK : 1 ≤ K) :
    IntegrableOn (g s a K) (Ioi 0) := by
  have ha0 : 0 ≤ a := by linarith
  have hK0 : 0 < K := by linarith
  have hr : 0 < 1 / K := by positivity
  have hdom : IntegrableOn (fun y : ℝ =>
      a ^ s * 2 ^ s * (y ^ 0 * Real.exp (-(1 / K * y))) +
      a ^ s * 2 ^ s * (y ^ s * Real.exp (-(1 / K * y)))) (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _).add
      ((integrableOn_pow_mul_exp_neg_mul s hr).const_mul _)
  have hcont : Continuous (g s a K) := by unfold g; fun_prop
  refine hdom.mono' hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 ≤ y := le_of_lt hy
  rw [Real.norm_of_nonneg (by unfold g; positivity)]
  exact g_le_dom s ha hy0

/-- Generalizes upstream Energy.lean:165-222 from degree5 to every natural degree,
with arbitrary coefficient a>=1. The constant and power remain explicit. -/
theorem integral_g_le (s : ℕ) {a K : ℝ} (ha : 1 ≤ a) (hK : 1 ≤ K) :
    ∫ y in Ioi 0, g s a K y ≤ C s a * K ^ (s + 1) := by
  have ha0 : 0 ≤ a := by linarith
  have hK0 : 0 < K := by linarith
  have hr : 0 < 1 / K := by positivity
  have hdom : IntegrableOn (fun y : ℝ =>
      a ^ s * 2 ^ s * (y ^ 0 * Real.exp (-(1 / K * y))) +
      a ^ s * 2 ^ s * (y ^ s * Real.exp (-(1 / K * y)))) (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _).add
      ((integrableOn_pow_mul_exp_neg_mul s hr).const_mul _)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] g s a K :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => by
      have hy0 : 0 ≤ y := le_of_lt hy
      unfold g; positivity)
  have hmono : ∀ᵐ y ∂(volume.restrict (Ioi 0)), g s a K y ≤
      a ^ s * 2 ^ s * (y ^ 0 * Real.exp (-(1 / K * y))) +
      a ^ s * 2 ^ s * (y ^ s * Real.exp (-(1 / K * y))) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => g_le_dom s ha (le_of_lt hy))
  calc ∫ y in Ioi 0, g s a K y
      ≤ ∫ y in Ioi 0,
          (a ^ s * 2 ^ s * (y ^ 0 * Real.exp (-(1 / K * y))) +
            a ^ s * 2 ^ s * (y ^ s * Real.exp (-(1 / K * y)))) :=
        integral_mono_of_nonneg hnn hdom hmono
    _ = a ^ s * 2 ^ s * (K + (s.factorial : ℝ) * K ^ (s + 1)) := by
      rw [integral_add ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _)
        ((integrableOn_pow_mul_exp_neg_mul s hr).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_pow_mul_exp_neg_mul 0 hr, integral_pow_mul_exp_neg_mul s hr]
      simp only [Nat.factorial_zero, zero_add, pow_one, div_eq_mul_inv, inv_pow, inv_inv, one_mul]
      ring
    _ ≤ C s a * K ^ (s + 1) := by
      have hKpow : K ≤ K ^ (s + 1) := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ (s + 1) := pow_le_pow_right₀ hK (by omega)
      unfold C
      calc a ^ s * 2 ^ s * (K + (s.factorial : ℝ) * K ^ (s + 1))
          ≤ a ^ s * 2 ^ s * (K ^ (s + 1) + (s.factorial : ℝ) * K ^ (s + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring

/-- The requested arbitrary-degree polynomial-exponential integral.
Includes every natural s, thus in particular s>=1. -/
theorem integral_pi_g_le (s : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    ∫ y in Ioi 0, (1 + 2 * Real.pi * y) ^ s * Real.exp (-(1 / K * y)) ≤
      (2 * Real.pi) ^ s * 2 ^ s * (1 + (s.factorial : ℝ)) * K ^ (s + 1) := by
  simpa only [g, C] using integral_g_le s (by linarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi) hK

/-- The original upstream s=5 constant and power are recovered literally. -/
theorem integral_pi_five {K : ℝ} (hK : 1 ≤ K) :
    ∫ y in Ioi 0, (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
      (2 * Real.pi) ^ 5 * 32 * 121 * K ^ 6 := by
  have h := integral_pi_g_le 5 hK
  norm_num [Nat.factorial] at h
  simpa only [one_div] using h

#print axioms BAnalyticIntegral.integrableOn_g
#print axioms BAnalyticIntegral.integral_g_le
#print axioms BAnalyticIntegral.integral_pi_g_le
#print axioms BAnalyticIntegral.integral_pi_five
end BAnalyticIntegral
