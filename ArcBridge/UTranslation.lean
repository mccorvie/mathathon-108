/- Event-work dependency copied byte-for-byte below from E207 U12 Codex.
Status remains CONJECTURE pending human statement comparison. -/
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
E207 / lane U12. Author: Codex, event work 2026-11-14.
CONJECTURE in the report pending the parent gate and human statement comparison.
This file defines an explicit real function, not a measure integral.
-/

noncomputable section

namespace Mathathon.P108.UTranslation

open Real Set

/-- Explicit max function used as interval distance; no measure appears here. -/
def intervalDistance (a b x : ℝ) : ℝ := max (a - x) (max 0 (x - b))

-- CONJECTURE (parent gate and human comparison pending): nonnegativity of the explicit max function.
theorem intervalDistance_nonneg (a b x : ℝ) : 0 ≤ intervalDistance a b x := by
  exact le_trans (le_max_left 0 (x - b)) (le_max_right (a - x) (max 0 (x - b)))

-- CONJECTURE (parent gate and human comparison pending): one-sided translation estimate for the max function.
theorem intervalDistance_upper (a b x y : ℝ) :
    intervalDistance a b y ≤ intervalDistance a b x + |y - x| := by
  have h₁ : a - x ≤ intervalDistance a b x := le_max_left _ _
  have h₂ : 0 ≤ intervalDistance a b x := intervalDistance_nonneg _ _ _
  have h₃ : x - b ≤ intervalDistance a b x :=
    le_trans (le_max_right 0 (x - b)) (le_max_right _ _)
  have h₄ : y - x ≤ |y - x| := le_abs_self _
  have h₅ : -(y - x) ≤ |y - x| := neg_le_abs _
  have h₆ : 0 ≤ |y - x| := abs_nonneg _
  unfold intervalDistance at *
  refine max_le ?_ (max_le ?_ ?_) <;> linarith

-- CONJECTURE (parent gate and human comparison pending): the explicit max function is 1-Lipschitz.
theorem intervalDistance_abs_sub_le (a b x y : ℝ) :
    |intervalDistance a b y - intervalDistance a b x| ≤ |y - x| := by
  apply abs_le.mpr
  constructor
  · have h := intervalDistance_upper a b y x
    rw [abs_sub_comm x y] at h
    linarith
  · have h := intervalDistance_upper a b x y
    linarith

-- CONJECTURE (parent gate and human comparison pending): arsinh is 1-Lipschitz on the reals.
theorem arsinh_abs_sub_le (u v : ℝ) :
    |Real.arsinh u - Real.arsinh v| ≤ |u - v| := by
  have bound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv Real.arsinh z‖ ≤ (1 : ℝ) := by
    intro z _
    rw [(Real.hasDerivAt_arsinh z).deriv, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have h : (1 : ℝ) ≤ Real.sqrt (1 + z ^ 2) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith [sq_nonneg z]
    simpa only [one_div, inv_one] using (one_div_le_one_div_of_le (by norm_num) h)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (f := Real.arsinh) (s := Set.univ) (x := v) (y := u)
    (fun z _ => Real.differentiable_arsinh z) bound convex_univ (by trivial) (by trivial)
  simpa only [Real.norm_eq_abs, one_mul] using h

-- CONJECTURE (parent gate and human comparison pending): square-root Holder estimate on nonnegative inputs.
theorem sqrt_abs_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.sqrt u - Real.sqrt v| ≤ Real.sqrt |u - v| := by
  apply Real.abs_le_sqrt
  have su := Real.sq_sqrt hu
  have sv := Real.sq_sqrt hv
  have pu := Real.sqrt_nonneg u
  have pv := Real.sqrt_nonneg v
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hs := Real.sqrt_le_sqrt h
    have hm := mul_le_mul_of_nonneg_right hs pv
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hs := Real.sqrt_le_sqrt h
    have hm := mul_le_mul_of_nonneg_right hs pu
    nlinarith

-- CONJECTURE (parent gate and human comparison pending): equivalence of the arcosh and arsinh expressions.
theorem arcosh_one_add_two_mul {u : ℝ} (hu : 0 ≤ u) :
    Real.arcosh (1 + 2 * u) = 2 * Real.arsinh (Real.sqrt u) := by
  have hc : Real.cosh (2 * Real.arsinh (Real.sqrt u)) = 1 + 2 * u := by
    rw [Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh,
      Real.sq_sqrt (by positivity), Real.sq_sqrt hu]
    ring
  rw [← hc, Real.arcosh_cosh]
  exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg u))

/-- An explicit elementary real function; it is not defined as a logarithmic integral. -/
def closedPotential (a b x : ℝ) : ℝ :=
  Real.log ((b - a) / 4) +
    2 * Real.arsinh (Real.sqrt (intervalDistance a b x / (b - a)))

-- CONJECTURE (parent gate and human comparison pending): the two explicit potential expressions agree.
theorem closedPotential_eq_arcosh {a b : ℝ} (hab : a < b) (x : ℝ) :
    closedPotential a b x = Real.log ((b - a) / 4) +
      Real.arcosh (1 + 2 * intervalDistance a b x / (b - a)) := by
  have hd : 0 ≤ intervalDistance a b x / (b - a) :=
    div_nonneg (intervalDistance_nonneg _ _ _) (sub_pos.mpr hab).le
  unfold closedPotential
  congr 1
  rw [show 2 * intervalDistance a b x / (b - a) =
    2 * (intervalDistance a b x / (b - a)) by ring]
  exact (arcosh_one_add_two_mul hd).symm

/-- The same function written using only real logarithms, square roots, and arithmetic. -/
-- CONJECTURE (parent gate and human comparison pending): equivalence with an explicit real logarithm expression.
theorem closedPotential_eq_log {a b : ℝ} (hab : a < b) (x : ℝ) :
    closedPotential a b x = Real.log ((b - a) / 4) +
      2 * Real.log (Real.sqrt (intervalDistance a b x / (b - a)) +
        Real.sqrt (1 + intervalDistance a b x / (b - a))) := by
  have hd : 0 ≤ intervalDistance a b x / (b - a) :=
    div_nonneg (intervalDistance_nonneg _ _ _) (sub_pos.mpr hab).le
  simp only [closedPotential, Real.arsinh, Real.sq_sqrt hd]

-- CONJECTURE (parent gate and human comparison pending): the explicit function is constant between the endpoints.
theorem closedPotential_of_mem {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    closedPotential a b x = Real.log ((b - a) / 4) := by
  have hd : intervalDistance a b x = 0 := by
    unfold intervalDistance
    rw [max_eq_left (sub_nonpos.mpr hxb), max_eq_right (sub_nonpos.mpr hax)]
  simp only [closedPotential, hd, zero_div, Real.sqrt_zero, Real.arsinh_zero,
    mul_zero, add_zero]

-- CONJECTURE (parent gate and human comparison pending): global two-point modulus for the explicit function.
theorem closedPotential_abs_sub_le {a b : ℝ} (hab : a < b) (x y : ℝ) :
    |closedPotential a b y - closedPotential a b x| ≤
      2 * Real.sqrt (|y - x| / (b - a)) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hx : 0 ≤ intervalDistance a b x / (b - a) :=
    div_nonneg (intervalDistance_nonneg _ _ _) hL.le
  have hy : 0 ≤ intervalDistance a b y / (b - a) :=
    div_nonneg (intervalDistance_nonneg _ _ _) hL.le
  have hd : |intervalDistance a b y / (b - a) - intervalDistance a b x / (b - a)| ≤
      |y - x| / (b - a) := by
    rw [← sub_div, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (intervalDistance_abs_sub_le a b x y) hL.le
  have hs := (sqrt_abs_sub_le hy hx).trans (Real.sqrt_le_sqrt hd)
  have ha := (arsinh_abs_sub_le
    (Real.sqrt (intervalDistance a b y / (b - a)))
    (Real.sqrt (intervalDistance a b x / (b - a)))).trans hs
  have heq : closedPotential a b y - closedPotential a b x =
      2 * (Real.arsinh (Real.sqrt (intervalDistance a b y / (b - a))) -
        Real.arsinh (Real.sqrt (intervalDistance a b x / (b - a)))) := by
    unfold closedPotential
    ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left ha (by norm_num)

-- CONJECTURE (parent gate and human comparison pending): nonnegative translation modulus for the explicit function.
theorem closedPotential_translation {a b e : ℝ} (hab : a < b) (he : 0 ≤ e) (x : ℝ) :
    |closedPotential a b (x + e) - closedPotential a b x| ≤
      2 * Real.sqrt (e / (b - a)) := by
  simpa only [add_sub_cancel_left, abs_of_nonneg he] using
    closedPotential_abs_sub_le hab x (x + e)

/-- The canonical arcosh closed form, defined without a logarithmic integral. -/
def arcoshPotential (a b x : ℝ) : ℝ :=
  Real.log ((b - a) / 4) +
    Real.arcosh (1 + 2 * intervalDistance a b x / (b - a))

-- CONJECTURE (parent gate and human comparison pending): the requested arcosh-form translation theorem.
theorem arcoshPotential_translation {a b e : ℝ} (hab : a < b) (he : 0 ≤ e) (x : ℝ) :
    |arcoshPotential a b (x + e) - arcoshPotential a b x| ≤
      2 * Real.sqrt (e / (b - a)) := by
  unfold arcoshPotential
  simpa only [closedPotential_eq_arcosh hab] using closedPotential_translation hab he x

end Mathathon.P108.UTranslation

#print axioms Mathathon.P108.UTranslation.closedPotential_translation
#print axioms Mathathon.P108.UTranslation.closedPotential_eq_arcosh
#print axioms Mathathon.P108.UTranslation.closedPotential_eq_log
#print axioms Mathathon.P108.UTranslation.closedPotential_of_mem
#print axioms Mathathon.P108.UTranslation.arcoshPotential_translation
