import Mathathon.P108.InnerShift
import Mathathon.P108.Integrable

/-!
# #108: the inner-offset gap between `s` and Lai's `ν − 1` (EVENT WORK)

Formalizer (Claude Opus 5.5), Fri Nov 13 2026. For every pair of offsets `c, c'` (the constant in
`Γ`), `∫_3^M R_(c,ν)/x³ − ∫_3^M R_(c',ν)/x³ = (c − c') λ (1/3 − 1/M)`. With `c = s = 7` and Lai's
`c' = ν − 1 = 1` at `ν = 2`, `α = 3/40`, `M = 200`, the gap is `21867/12000 = 1.82225`: exactly the
difference between the ν = 2 audit's A_200 with constant 7 (3.6428078823, C7) and with Lai's constant 1
(1.8205578823, C3d), `evidence/lai-nu2-audit/README.md`, E10, E12.

Difference from the claim: `innerR 1 2 (3/40)` is this file's general formula with offset 1; that it is
the inner function of Lai's Programs 06/08 (constant `nu-1`, N-coefficient `2ν`) is the audit's reading of
his code (C3d), not checked in Lean.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-- **Offset gap, general:** for all real `c, c', ν, α` and `M ≥ 3`,
`∫_3^M R_(c,ν)(x)/x³ dx − ∫_3^M R_(c',ν)(x)/x³ dx = (c − c') λ (1/3 − 1/M)`, `λ = 1 − α`. -/
theorem inner_integral_shift (c c' ν α M : ℝ) (hM : 3 ≤ M) :
    (∫ x in (3:ℝ)..M, innerR c ν α x / x ^ 3) - (∫ x in (3:ℝ)..M, innerR c' ν α x / x ^ 3)
      = (c - c') * (1 - α) * (1 / 3 - 1 / M) := by
  rw [← intervalIntegral.integral_sub (innerR_div_intervalIntegrable c ν α M hM)
    (innerR_div_intervalIntegrable c' ν α M hM)]
  have h : EqOn (fun x : ℝ => innerR c ν α x / x ^ 3 - innerR c' ν α x / x ^ 3)
      (fun x : ℝ => (c - c') * (1 - α) * x ^ (-2 : ℤ)) (uIcc (3:ℝ) M) := by
    intro x hx
    rw [uIcc_of_le hM] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simp only
    rw [← sub_div, innerR_shift, zpow_neg, zpow_ofNat]
    field_simp
  have hint2 : ∫ x in (3:ℝ)..M, x ^ (-2 : ℤ) = 1 / 3 - 1 / M := by
    rw [integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
    · have hM0 : M ≠ 0 := by linarith
      rw [show ((-2 : ℤ) + 1) = -1 by norm_num, zpow_neg_one, zpow_neg_one]
      push_cast
      field_simp
      ring
    · rw [uIcc_of_le hM]
      intro h0
      linarith [h0.1]
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, hint2]

/-- **E10's located term, exact:** at `ν = 2`, `α = 3/40`, `M = 200`, replacing Lai's inner offset
`ν − 1 = 1` by `s = 7` raises `∫_3^200 R/x³` by exactly `21867/12000` (`= 6 · (37/40) · (197/600)`). -/
theorem lai_offset_gap_7_2 :
    (∫ x in (3:ℝ)..200, innerR 7 2 (3/40) x / x ^ 3)
      - (∫ x in (3:ℝ)..200, innerR 1 2 (3/40) x / x ^ 3) = 21867 / 12000 := by
  rw [inner_integral_shift 7 1 2 (3/40) 200 (by norm_num)]
  norm_num

end

end Mathathon.P108
