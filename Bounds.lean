import Continuity

/- E426 Codex inner_regularity. PROOF-DRAFT boundedness of the ACTUALmodel.
The auxiliary continuous finite-dimensional expression is proved equal to
actualrootinnerR, and its input vector is bounded explicitly. -/
open MeasureTheory Set Filter Topology Finset
namespace BInnerLimit
noncomputable section
open Mathathon.P108 BInnerExplicit.ClassSums

def rCell (s ν α : ℝ) (w : Fin 8 → ℝ) : ℝ :=
  -(gammaCells s ν (w 3) (w 2) (w 1) (w 4) (w 5) +
      (Hc ν α * w 0 - w 3 / 2) * (2 * w 3 - w 6 - s) +
      max (Hc ν α * w 0 - w 3 / 2 - (2 * w 0 - w 6) / 2) 0) -
    (2 * (1 - α) * w 0 * w 1 - 2 * ν * (1 - α) * w 0 * w 2 -
      2 * (w 7 * ((1 - α) * w 0) - w 7 * (w 7 + 1) / 4))

def modelVector (ν α x : ℝ) : Fin 8 → ℝ :=
  ![x, (⌊x⌋ : ℝ), (⌊α * x⌋ : ℝ), Tc ν α x,
    Int.fract (α * x), Int.fract x, (⌊2 * x⌋ : ℝ),
    (⌊2 * ((1 - α) * x)⌋ : ℝ)]

theorem innerR_eq_rCell (s ν α x : ℝ) :
    innerR s ν α x = rCell s ν α (modelVector ν α x) := by
  unfold innerR innerGamma innerN sigmaC nplus Jfun
  rw [integral_gamma_cells]
  rfl

theorem continuous_rCell (s ν α : ℝ) : Continuous (rCell s ν α) := by
  have hCells : Continuous (fun w : Fin 8 → ℝ =>
      gammaCells s ν (w 3) (w 2) (w 1) (w 4) (w 5)) := by
    unfold gammaCells
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    fin_cases i <;> fin_cases j <;>
      dsimp [bcoef, gammaTable, ccount, cvLo, cvHi] <;> fun_prop
  unfold rCell
  fun_prop

theorem abs_floor_le (x : ℝ) : |(⌊x⌋ : ℝ)| ≤ |x| + 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x]

theorem modelVector_bounded (ν α M : ℝ) (hM : 0 ≤ M) :
    ∃ A : ℝ, ∀ x : ℝ, |x| ≤ M → ∀ i : Fin 8, |modelVector ν α x i| ≤ A := by
  let A := 2 + M + |α| * M + |2 * Hc ν α| * M + 2 * M + |2 * (1 - α)| * M
  refine ⟨A, ?_⟩
  intro x hx i
  have ha := mul_nonneg (abs_nonneg α) hM
  have hH := mul_nonneg (abs_nonneg (2 * Hc ν α)) hM
  have hl := mul_nonneg (abs_nonneg (2 * (1 - α))) hM
  have hmul (c : ℝ) : |c * x| ≤ |c| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg c)
  have hfrac (u : ℝ) : |Int.fract u| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  fin_cases i <;> simp only [modelVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ, Tc]
  · dsimp [A]; nlinarith
  · dsimp [A]; nlinarith [abs_floor_le x]
  · dsimp [A]; nlinarith [abs_floor_le (α * x), hmul α]
  · dsimp [A]; nlinarith [abs_floor_le (2 * Hc ν α * x), hmul (2 * Hc ν α)]
  · dsimp [A]; nlinarith [hfrac (α * x)]
  · dsimp [A]; nlinarith [hfrac x]
  · have ht : |2 * x| ≤ 2 * M := by simpa using hmul 2
    dsimp [A]; nlinarith [abs_floor_le (2 * x)]
  · have ht : |2 * ((1 - α) * x)| ≤ |2 * (1 - α)| * M := by
      simpa only [mul_assoc] using hmul (2 * (1 - α))
    dsimp [A]; nlinarith [abs_floor_le (2 * ((1 - α) * x))]

theorem innerR_bounded (s ν α M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ≤ M → |innerR s ν α x| ≤ C := by
  obtain ⟨A, hA⟩ := modelVector_bounded ν α M hM
  have hcompact : IsCompact (Icc (fun _ : Fin 8 => -A) (fun _ => A)) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (continuous_rCell s ν α).abs.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  rw [innerR_eq_rCell]
  apply hC
  apply Set.mem_image_of_mem
  constructor
  · intro i
    exact (abs_le.mp (hA x hx i)).1
  · intro i
    exact (abs_le.mp (hA x hx i)).2

theorem innerWeight_bounded (s ν : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    ∃ C : ℝ, ∀ y ∈ Icc (1 / (M : ℝ)) (1 / 3), |innerWeight s ν y| ≤ C := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨C, hC⟩ := innerR_bounded s ν (3 / 40) (M : ℝ) hMR.le
  refine ⟨max C 0, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr hMR) hy.1
  have hxM : y⁻¹ ≤ M := by
    rw [← one_div, div_le_iff₀ hy0]
    have h := hy.1
    rw [div_le_iff₀ hMR] at h
    linarith
  have hc := hC y⁻¹ (by rw [abs_of_pos (inv_pos.mpr hy0)]; exact hxM)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hcc : |innerR s ν (3 / 40) y⁻¹| ≤ max C 0 := hc.trans (le_max_left _ _)
  unfold innerWeight
  rw [abs_mul, abs_of_pos hy0]
  calc
    _ ≤ y * max C 0 := mul_le_mul_of_nonneg_left hcc hy0.le
    _ ≤ 1 * max C 0 := mul_le_mul_of_nonneg_right (by linarith [hy.2]) hC0
    _ = _ := one_mul _

theorem bounded_statement : BoundedStatement := by
  intro s ν M hM
  exact innerWeight_bounded s ν hM

#print axioms innerWeight_bounded
#print axioms bounded_statement
end
end BInnerLimit
