import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathathon.P108.DetG0Poly

/-!
# #108 `det_G40_zero`, part 3: determinant through a checked `L D Lᵀ` certificate

EVENT WORK (#108, formalizer 4, Claude Opus 5.5, Sat Nov 14 2026, started 00:35 PT).

`det_eq_prod_of_ldl` (general, any `n`): if `M i j = ∑_k L i k · d k · L j k` for a unit lower
triangular `L`, then `det M = ∏ d`. The certificate `(L, d)` is produced by the unverified
elimination `ldlAux` (no correctness proof needed) and the identity is then checked entry by
entry by the kernel (`checkLDL`, `checkLDL_sound`). No `sorry`, no `native_decide`.
-/

namespace Mathathon.P108.Skip.DetG0

open Matrix

/-- The unit lower triangular matrix with strictly-lower entries `Lf i j`. -/
def ltri {n : ℕ} (Lf : Fin n → Fin n → ℚ) (i j : Fin n) : ℚ :=
  if j < i then Lf i j else if i = j then 1 else 0

/-- **`det M = ∏ d` from `M = L · diag d · Lᵀ`** (`L` unit lower triangular). -/
theorem det_eq_prod_of_ldl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (Lf : Fin n → Fin n → ℚ)
    (d : Fin n → ℚ) (h : ∀ i j, M i j = ∑ k, ltri Lf i k * d k * ltri Lf j k) :
    M.det = ∏ i, d i := by
  set L : Matrix (Fin n) (Fin n) ℚ := Matrix.of (ltri Lf) with hLdef
  have hM : M = L * diagonal d * Lᵀ := by
    ext i j
    rw [h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    rfl
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [hLdef, ltri]
    · intro i j hij
      have hij' : i < j := hij
      simp only [hLdef, Matrix.of_apply, ltri]
      rw [if_neg (not_lt.2 hij'.le), if_neg hij'.ne]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hL, Matrix.det_diagonal]
  ring

/-! ## The (unverified) elimination producing the certificate -/

/-- One elimination step: pivot, multipliers, and the reduced rows. -/
def elimStep : List (List ℚ) → ℚ × List ℚ × List (List ℚ)
  | [] => (0, [], [])
  | r :: rs =>
      (r.headD 0, rs.map (fun s => s.headD 0 / r.headD 0),
        rs.map (fun s => addL s.tail (smulL (-(s.headD 0 / r.headD 0)) r.tail)))

/-- Gaussian elimination without pivoting: `(pivots, columns of multipliers)`. -/
def ldlAux : ℕ → List (List ℚ) → List ℚ × List (List ℚ)
  | 0, _ => ([], [])
  | n + 1, rows =>
      let st := elimStep rows
      let rest := ldlAux n st.2.2
      (st.1 :: rest.1, st.2.1 :: rest.2)

/-- The strictly-lower entries read off the multiplier columns. -/
def ldlL {n : ℕ} (cols : List (List ℚ)) (i j : Fin n) : ℚ :=
  (cols.getD j.val []).getD (i.val - j.val - 1) 0

/-- Kernel check of `M = L diag(d) Lᵀ`, entry by entry. -/
def checkLDL {n : ℕ} (M : Fin n → Fin n → ℚ) (Lf : Fin n → Fin n → ℚ) (d : Fin n → ℚ) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (M i j = (List.ofFn fun k => ltri Lf i k * d k * ltri Lf j k).sum)

theorem checkLDL_sound {n : ℕ} (M : Fin n → Fin n → ℚ) (Lf : Fin n → Fin n → ℚ)
    (d : Fin n → ℚ) (h : checkLDL M Lf d = true) :
    (Matrix.of M).det = ∏ i, d i := by
  refine det_eq_prod_of_ldl _ Lf d fun i j => ?_
  simp only [checkLDL, List.all_eq_true, decide_eq_true_eq] at h
  rw [Matrix.of_apply, h i (List.mem_finRange i) j (List.mem_finRange j), List.sum_ofFn]

/-- Half the work for a symmetric `M`: check `M i j = ∑_k L j k d k L i k` for `j ≤ i` only
(the summand order makes the kernel multiply by `0` first when `k > j`). -/
def checkLDLsym {n : ℕ} (M : Fin n → Fin n → ℚ) (Lf : Fin n → Fin n → ℚ) (d : Fin n → ℚ) :
    Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (j ≤ i → M i j = (List.ofFn fun k => ltri Lf j k * d k * ltri Lf i k).sum)

theorem checkLDLsym_sound {n : ℕ} (M : Fin n → Fin n → ℚ) (hM : ∀ i j, M i j = M j i)
    (Lf : Fin n → Fin n → ℚ) (d : Fin n → ℚ) (h : checkLDLsym M Lf d = true) :
    (Matrix.of M).det = ∏ i, d i := by
  refine det_eq_prod_of_ldl _ Lf d fun i j => ?_
  simp only [checkLDLsym, List.all_eq_true, decide_eq_true_eq] at h
  rw [Matrix.of_apply]
  rcases le_total j i with hji | hij
  · rw [h i (List.mem_finRange i) j (List.mem_finRange j) hji, List.sum_ofFn]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [hM, h j (List.mem_finRange j) i (List.mem_finRange i) hij, List.sum_ofFn]

end Mathathon.P108.Skip.DetG0
