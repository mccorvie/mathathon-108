import Mathathon.P108.SStep
import Mathlib.Tactic

/- E213 / U18, Codex. CONJECTURE: parent gate and human comparison pending.
Exact copies of the root package definitions are imported unchanged.
-/
noncomputable section
open MeasureTheory Set

namespace MarginPieces

theorem const_piece_open (f : ℝ → ℝ) (l r c : ℝ) (hlr : l ≤ r)
    (h : ∀ x ∈ Ioo l r, f x = c) :
    IntervalIntegrable f volume l r ∧ ∫ x in l..r, f x = c * (r - l) := by
  have he : EqOn (fun _ : ℝ => c) f (uIoo l r) := by
    rw [uIoo_of_le hlr]
    intro x hx
    exact (h x hx).symm
  have hi : IntervalIntegrable f volume l r := intervalIntegrable_const.congr_uIoo he
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_congr_Ioo_of_le hlr h, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem affine_cube_piece (f : ℝ → ℝ) (l r a b : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (h : ∀ x ∈ Ioo l r, f x = a + b * x) :
    IntervalIntegrable (fun x => f x / x^3) volume l r ∧
    ∫ x in l..r, f x / x^3 = b * (1/l - 1/r) + a/2 * (1/l^2 - 1/r^2) := by
  have ha : EqOn (fun x => f x / x^3)
      (fun x : ℝ => a * x^(-3 : ℤ) + b * x^(-2 : ℤ)) (uIoo l r) := by
    rw [uIoo_of_le hlr]
    intro x hx
    have hx0 : x ≠ 0 := (hl.trans hx.1).ne'
    dsimp
    rw [h x hx, zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
    field_simp
    <;> ring
  have hnot : (0 : ℝ) ∉ uIcc l r := by
    rw [uIcc_of_le hlr]
    intro h0
    linarith [h0.1]
  have hc (n : ℤ) : IntervalIntegrable (fun x : ℝ => x ^ n) volume l r := by
    have hcon : ContinuousOn (fun x : ℝ => x ^ n) (uIcc l r) := by
      apply ContinuousOn.zpow₀ continuousOn_id
      intro x hx
      left
      rw [uIcc_of_le hlr] at hx
      exact (hl.trans_le hx.1).ne'
    exact hcon.intervalIntegrable
  have hi := ((hc (-3)).const_mul a).add ((hc (-2)).const_mul b)
  have hif : IntervalIntegrable (fun x => f x / x^3) volume l r :=
    hi.congr_uIoo (fun x hx => (ha hx).symm)
  refine ⟨hif, ?_⟩
  rw [intervalIntegral.integral_congr_uIoo ha,
    intervalIntegral.integral_add ((hc (-3)).const_mul a) ((hc (-2)).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, hnot⟩),
    integral_zpow (Or.inr ⟨by norm_num, hnot⟩)]
  have hr0 : r ≠ 0 := (hl.trans_le hlr).ne'
  norm_num
  field_simp
  ring

end MarginPieces
