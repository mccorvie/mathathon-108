import BAnalyticMoments

/-!
PROOF-DRAFT: exact upstream density core and generic-density bridge.
Codex a8_tieband, Lane B. Definitions copied from Firsching/Paul-Lez,
mo271/Zeta5@be1c0d82, Apery/Weight.lean:15-20, Apache-2.0.
The general density and its proof are attributed in BAnalyticMoments.lean.
-/
namespace Apery

noncomputable def wS (y : ℝ) : ℝ :=
  ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))

noncomputable def w (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y

lemma w_eq_general_five (y : ℝ) : w y = BAnalyticMoments.w 5 y := by
  have hfac : (((5 - 1).factorial : ℕ) : ℝ) = 24 := by norm_num
  unfold BAnalyticMoments.w
  rw [hfac]
  change (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y =
    2 * (2 * Real.pi) ^ 4 * y ^ 5 / 24 * wS y
  ring

end Apery
