import FieldAverage.Field
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-
Author: Codex (GPT-6), lane U, task U43/E238.
Status: PROOF-DRAFT. Actual interval-integral model U16.J and U16.V6
is imported unchanged from the frozen UBorelAEField dependency.
Mathlib supplies log integrability, its integral, and pi > 3.
-/

set_option autoImplicit false

open Real Set MeasureTheory

namespace U43

/-- PROOF-DRAFT: integrability includes the logarithmic endpoint t=0. -/
theorem J_intervalIntegrable (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u : ℝ => Real.log (t + u ^ 2)) volume 0 a := by
  by_cases hz : t = 0
  · subst t
    simpa only [zero_add, Real.log_pow, Nat.cast_ofNat] using
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := a)).const_mul (2 : ℝ)
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hc : Continuous (fun u : ℝ => Real.log (t + u ^ 2)) := by
      apply Continuous.log
      · fun_prop
      · intro u
        exact ne_of_gt (by nlinarith [sq_nonneg u] : 0 < t + u ^ 2)
    exact hc.intervalIntegrable 0 a

/-- PROOF-DRAFT: exact value of the actual integral. -/
theorem J_one_zero : U16.J 1 0 = -2 := by
  unfold U16.J
  simp only [zero_add, Real.log_pow, Nat.cast_ofNat]
  rw [intervalIntegral.integral_const_mul]
  simp

/-- PROOF-DRAFT: the lower comparison excludes the single endpoint u=0. -/
theorem J_one_lower {t : ℝ} (ht : 0 ≤ t) : -2 ≤ U16.J 1 t := by
  rw [← J_one_zero]
  unfold U16.J
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (J_intervalIntegrable 1 (by norm_num)) (J_intervalIntegrable 1 ht)
  intro u hu
  apply Real.log_le_log
  · nlinarith [hu.1]
  · linarith

/-- PROOF-DRAFT: a global upper bound valid also at zero. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_self (Real.sqrt_nonneg x)
  rw [Real.log_sqrt hx] at h
  linarith

/-- PROOF-DRAFT: bound for the actual short-interval integral. -/
theorem J_alpha_upper {t : ℝ} (ht : 0 ≤ t) :
    U16.J (3 / 40) t ≤ (3 / 20 : ℝ) * Real.sqrt (t + 1) := by
  have hm : (∫ u in (0 : ℝ)..(3 / 40 : ℝ), Real.log (t + u ^ 2)) ≤
      ∫ _u in (0 : ℝ)..(3 / 40 : ℝ), 2 * Real.sqrt (t + 1) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (J_intervalIntegrable (3 / 40) ht) intervalIntegrable_const
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := by linarith [hu.2]
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    calc
      Real.log (t + u ^ 2) ≤ 2 * Real.sqrt (t + u ^ 2) :=
        log_le_two_sqrt (by positivity)
      _ ≤ 2 * Real.sqrt (t + 1) := by
        gcongr
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  change (∫ u in (0 : ℝ)..(3 / 40 : ℝ), Real.log (t + u ^ 2)) ≤ _
  nlinarith [hm]

/-- PROOF-DRAFT: elementary square-root comparison. -/
lemma sqrt_add_one_le {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (t + 1) ≤ Real.sqrt t + 1 := by
  apply (Real.sqrt_le_left (by positivity : 0 ≤ Real.sqrt t + 1)).2
  nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]

/-- PROOF-DRAFT: explicit coercivity of the actual field, with no growth premise. -/
theorem V6_coercive {t : ℝ} (ht : 0 ≤ t) :
    5 * Real.sqrt t - 3 ≤ U16.V6 t := by
  have hl := J_one_lower ht
  have hu := J_alpha_upper ht
  have hs := sqrt_add_one_le ht
  have hp : 3 * Real.sqrt t ≤ Real.pi * Real.sqrt t :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg t)
  unfold U16.V6
  nlinarith [Real.sqrt_nonneg t]

end U43

#print axioms U43.J_intervalIntegrable
#print axioms U43.J_one_zero
#print axioms U43.J_one_lower
#print axioms U43.log_le_two_sqrt
#print axioms U43.J_alpha_upper
#print axioms U43.sqrt_add_one_le
#print axioms U43.V6_coercive
