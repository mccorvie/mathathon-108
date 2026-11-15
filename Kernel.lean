import Mathlib

/-!
B8/E409 support, lane B Codex. PROOF-DRAFT until gate.
Minimal Mittag-Leffler dependency closure copied from mo271/Zeta5@be1c0d82,
Apery/Hermite.lean:72-76,86,309-389. Firsching/Paul-Lez, Apache-2.0.
No higher derivative or integration-by-parts chain is imported.
-/
open Filter Topology Finset MeasureTheory Set
namespace BAnalyticPoles.ML
noncomputable def qe (y : ℝ) : ℝ := Real.exp (2 * Real.pi * y)

lemma qe_pos (y : ℝ) : 0 < qe y := Real.exp_pos _
lemma qe_gt_one {y : ℝ} (hy : 0 < y) : 1 < qe y := by
  unfold qe; rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by positivity)
noncomputable def F0 (y : ℝ) : ℝ := 1 / (qe y - 1)
open Complex in
/-- The Mittag-Leffler expansion of `F(y) = 1/(e^{2πy} - 1)`:
`F(y) = -1/2 + 1/(2πy) + (1/π) ∑_{n ≥ 1} y/(y² + n²)`, from Mathlib's `cot_series_rep`. -/
lemma F0_series {y : ℝ} (hy : 0 < y) :
    F0 y = -1 / 2 + 1 / (2 * Real.pi * y) +
      (1 / Real.pi) * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hx : (I * (y : ℂ)) ∈ integerComplement := by
    rw [integerComplement_eq]
    rintro ⟨n, hn⟩
    have h := congrArg Complex.im hn
    simp at h
    linarith
  have h := cot_series_rep hx
  -- the left-hand side
  have hs : Real.sinh (Real.pi * y) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hL : (Real.pi : ℂ) * cot (Real.pi * (I * y)) =
      -I * ((Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) : ℝ) : ℂ) := by
    rw [cot_eq_cos_div_sin, show (Real.pi : ℂ) * (I * y) = ((Real.pi * y : ℝ) : ℂ) * I by
      push_cast; ring, cos_mul_I, sin_mul_I, ← ofReal_cosh, ← ofReal_sinh]
    have hs' : (Real.sinh (Real.pi * y) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  -- the right-hand side
  have hR : (1 / (I * (y : ℂ)) + ∑' n : ℕ+, (1 / (I * y - n) + 1 / (I * y + n))) =
      -I * ((1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    have hterm : ∀ n : ℕ+, (1 / (I * (y : ℂ) - n) + 1 / (I * y + n)) =
        -I * ((2 * y / (y ^ 2 + ((n : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
      intro n
      have h1 : I * (y : ℂ) - n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      have h2 : I * (y : ℂ) + n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      have h3 : ((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) ≠ 0 := by
        have : (0 : ℝ) < y ^ 2 + ((n : ℕ) : ℝ) ^ 2 := by positivity
        exact_mod_cast this.ne'
      push_cast
      rw [div_add_div _ _ h1 h2, div_eq_iff (mul_ne_zero h1 h2)]
      have hIy : (I * (y : ℂ) - n) * (I * y + n) = -((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) := by
        ring_nf; rw [I_sq]; ring
      rw [hIy]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => ((2 * y / (y ^ 2 + (m : ℝ) ^ 2) : ℝ) : ℂ))]
    push_cast
    rw [one_div, mul_inv, Complex.inv_I]
    ring
  rw [hL, hR] at h
  have hI : (-I : ℂ) ≠ 0 := by simp
  have h' := mul_left_cancel₀ hI h
  have hreal : Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) =
      1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by exact_mod_cast h'
  -- `cosh/sinh = 1 + 2 F₀`
  have hcoth : Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) = 1 + 2 * F0 y := by
    rw [Real.cosh_eq, Real.sinh_eq, F0, qe]
    have hq : Real.exp (2 * Real.pi * y) = Real.exp (Real.pi * y) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hq1 : Real.exp (2 * Real.pi * y) - 1 ≠ 0 := by
      have := qe_gt_one hy; unfold qe at this; linarith
    have he : Real.exp (-(Real.pi * y)) = 1 / Real.exp (Real.pi * y) := by
      rw [Real.exp_neg, one_div]
    rw [he]
    have hpos : Real.exp (Real.pi * y) ≠ 0 := (Real.exp_pos _).ne'
    rw [hq] at hq1 ⊢
    field_simp
    ring
  rw [hcoth] at hreal
  have hsum : ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) =
      2 * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    rw [← tsum_mul_left]; congr 1; funext n; ring
  rw [hsum] at hreal
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set S := ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) with hS
  have h2 : F0 y = (1 / y + 2 * S) / (2 * Real.pi) - 1 / 2 := by
    field_simp at hreal ⊢
    linear_combination hreal
  rw [h2]
  field_simp
  ring

/-- The classical Bose remainder at the unscaled variable. -/
noncomputable def remainder (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t + 1 / 2

/-- The scaled Mittag-Leffler expansion, with a positive summand. -/
lemma remainder_eq_tsum {t : ℝ} (ht : 0 < t) :
    remainder t = ∑' n : ℕ, 2 * t / (t ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := F0_series (y := t / (2 * Real.pi)) (by positivity)
  have he : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  simp only [F0, qe, he] at h
  have hs : (1 / Real.pi) * (∑' n : ℕ,
      (t / (2 * Real.pi)) / ((t / (2 * Real.pi)) ^ 2 + ((n : ℝ) + 1) ^ 2)) =
      ∑' n : ℕ, 2 * t / (t ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
  rw [hs] at h
  unfold remainder
  rw [h]
  field_simp
  ring
end BAnalyticPoles.ML
