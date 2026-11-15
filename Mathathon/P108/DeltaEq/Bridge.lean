import Mathathon.P108.DetG0
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic.NormNum
import Mathathon.P108.DeltaEq.Hankel
import Mathathon.P108.DeltaEq.HankelData

/-!
# #108 L4: from `det G_40(X)` to point checks and a degree bound

EVENT WORK (#108, lane L task L4, Claude Opus 5.5, Sat Nov 14 2026, started 15:33 PT).

`Mathathon/P108/LaiSkip.lean` must be able to import this development (to replace its
`sorry`), so, as in `DetG0.lean`, nothing here imports `LaiSkip`: we work with `DetG0`'s verbatim
copies `DetG0.G`, `DetG0.coefQ`, and `DeltaLit'` below is a verbatim copy of `Skip.DeltaLit`
(with `coefQ` read as `DetG0.coefQ`). `Main.lean` checks that the kernel accepts the transfer.

1. *Affine entries* (`g1C`, `entry_eq_at`, `entry_affine`): taken from lane L's E306
   `../L-delta-equality/AffineProbe.lean` (Codex driver), renamespaced: the Hankel entry
   `μ_X(D_3^2 t^m / D_40)` is `g0C m + X · g1C m`.
2. *Degree bound* (`Delta_natDegree_le`): `G_40 = X • A + B` entrywise, so
   `natDegree (det G_40) ≤ 37` (`Polynomial.natDegree_det_X_add_C_le`); `DeltaLit_natDegree_le`.
3. *Bridge* (`eval_Delta_of_check`): if `g0List = g0Q`, `g1List = g1Q` (`HankelCheck.lean`) and
   the boolean point certificate `ptCheck x` is `true`, then `det G_40(x) = DeltaLit(x)`
   (`G_40(x)` is the Hankel matrix of `hAt x`; `hankel_det_of_pass`; `eval_DeltaLit`).
No `sorry`, no `native_decide`, no axiom.
-/

namespace Mathathon.P108.Skip.DeltaEq

open Polynomial

/-! ## Affine entries (E306) -/

/-- The `X` coefficient of the `m`-th Hankel entry, by simple-pole residues (E306). -/
def g1C (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) 40,
    (∏ j ∈ Finset.Icc (1 : ℕ) 3, (-((k : ℚ) ^ 2) + (j : ℚ) ^ 2)) ^ 2 /
      DetG0.dD 40 k * (k : ℚ) ^ 10 * (-((k : ℚ) ^ 2)) ^ m

theorem eval_muPole_at (x : ℚ) (k : ℕ) :
    eval x (DetG0.muPole 11 k) = DetG0.poleVal k + (k : ℚ) ^ 10 * x := by
  simp only [DetG0.muPole, DetG0.poleVal, eval_add, eval_mul, eval_C, eval_sub, eval_X]
  norm_num
  ring

theorem entry_eq_at (x : ℚ) (m : ℕ) :
    eval x (DetG0.muX 11 40 (DetG0.D 3 ^ 2 * X ^ m)) = DetG0.g0C m + x * g1C m := by
  rw [DetG0.muX, DetG0.div_eq m, eval_add, eval_C, eval_finsetSum, DetG0.g0C, DetG0.g0Val, g1C,
    add_assoc]
  congr 1
  · rw [DetG0.sum_range_natDegree _ _ _ (DetG0.natDegree_q_lt m)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [DetG0.coeff_ofL, DetG0.muMono_eq]
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_muPole_at, DetG0.eval_f, DetG0.wK]
    ring

theorem entry_affine (m : ℕ) :
    DetG0.muX 11 40 (DetG0.D 3 ^ 2 * X ^ m) = C (DetG0.g0C m) + C (g1C m) * X := by
  apply Polynomial.funext
  intro x
  rw [entry_eq_at]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

/-! ## The degree bound -/

/-- Copy of `Skip.DeltaLit` (`DeltaLit(X) = ∑_{i<38} coefQ i · X^i`). -/
noncomputable def DeltaLit' : ℚ[X] := ∑ i ∈ Finset.range 38, C (DetG0.coefQ i) * X ^ i

theorem G_eq_affine : DetG0.G 11 2 1 =
    (X : ℚ[X]) • (Matrix.of fun i j : Fin (37 * 1) => g1C (i.val + j.val)).map C +
      (Matrix.of fun i j : Fin (37 * 1) => DetG0.g0C (i.val + j.val)).map C := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.of_apply, smul_eq_mul]
  show DetG0.muX 11 40 (DetG0.D 3 ^ 2 * X ^ (i.val + j.val)) = _
  rw [entry_affine]
  ring

/-- **Degree bound.** `natDegree Δ_40 ≤ 37`: a `37 × 37` determinant with entries affine in `X`. -/
theorem Delta_natDegree_le : (DetG0.G 11 2 1).det.natDegree ≤ 37 := by
  rw [G_eq_affine]
  exact (natDegree_det_X_add_C_le _ _).trans (by simp)

theorem DeltaLit_natDegree_le : DeltaLit'.natDegree ≤ 37 := by
  rw [DeltaLit']
  exact natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.1 hi; omega)

/-! ## The point certificate -/

/-- The `X` coefficients `g1C m`, `m < 73`. -/
def g1List : List ℚ := (List.range 73).map g1C

theorem g1List_getD (m : ℕ) (hm : m < 73) : g1List.getD m 0 = g1C m := by
  rw [g1List, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

/-- The 73 Hankel values of `G_40(x)`, from the literal lists. -/
def hAt (x : ℚ) : List ℚ := List.ofFn fun m : Fin 73 => g0Q.getD m.val 0 + x * g1Q.getD m.val 0

theorem hAt_length (x : ℚ) : (hAt x).length = 73 := List.length_ofFn

theorem hAt_getD (x : ℚ) (m : ℕ) (hm : m < 73) :
    (hAt x).getD m 0 = g0Q.getD m 0 + x * g1Q.getD m 0 := by
  rw [hAt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hm]

/-- `DeltaLit(x)`, computably. -/
def dataEval (x : ℚ) : ℚ := ∑ i ∈ Finset.range 38, DetG0.coefQ i * x ^ i

theorem eval_DeltaLit (x : ℚ) : DeltaLit'.eval x = dataEval x := by
  rw [DeltaLit', eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- **The point certificate at `x`**: Chebyshev's modified-moment pass on the Hankel values of
`G_40(x)` succeeds and its pivot product is `DeltaLit(x)`. -/
def ptCheck (x : ℚ) : Bool :=
  let r := chebPass 37 0 (rows (hAt x) 0)
  r.1 && decide (r.2 = dataEval x)

theorem map_G_eq_lit (hl : DetG0.g0List = g0Q ∧ g1List = g1Q) (x : ℚ) :
    (DetG0.G 11 2 1).map (eval x) =
      Matrix.of fun i j : Fin (37 * 1) => (hAt x).getD (i.val + j.val) 0 := by
  ext i j
  have hij : i.val + j.val < 73 := by have := i.isLt; have := j.isLt; omega
  rw [Matrix.map_apply, Matrix.of_apply, hAt_getD _ _ hij, ← hl.1, ← hl.2,
    DetG0.g0List_getD _ hij, g1List_getD _ hij]
  exact entry_eq_at x _

/-- **Bridge.** A `true` point certificate gives `det G_40(x) = DeltaLit(x)`. -/
theorem eval_Delta_of_check (hl : DetG0.g0List = g0Q ∧ g1List = g1Q) (x : ℚ)
    (hc : ptCheck x = true) : (DetG0.G 11 2 1).det.eval x = DeltaLit'.eval x := by
  simp only [ptCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hev : (DetG0.G 11 2 1).det.eval x = ((DetG0.G 11 2 1).map (eval x)).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    rfl
  rw [hev, map_G_eq_lit hl, eval_DeltaLit, ← hc.2]
  exact hankel_det_of_pass (hAt x) 37 (by rw [hAt_length]) hc.1

end Mathathon.P108.Skip.DeltaEq
