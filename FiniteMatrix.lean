import Mathlib

/-!
E208 / U13, Codex, 2026-11-14.
CONJECTURE: complete candidate proofs, parent gate and human comparison pending.
This file is event work. The finite-matrix reduction is proved from explicit premises.
-/

noncomputable section

namespace Mathathon.P108.FiniteDuality

open Finset

variable {ι : Type*} [Fintype ι]

def bilinear (K : ι → ι → ℝ) (a b : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * b j * K i j

def quadratic (K : ι → ι → ℝ) (a : ι → ℝ) : ℝ := bilinear K a a

-- CONJECTURE (parent gate and human comparison pending): symmetry of the finite bilinear form.
theorem bilinear_symm (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i) (a b : ι → ℝ) :
    bilinear K a b = bilinear K b a := by
  classical
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hK j i]
  ring

-- CONJECTURE (parent gate and human comparison pending): exact quadratic expansion.
theorem quadratic_sub (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i) (a b : ι → ℝ) :
    quadratic K (fun i => a i - b i) =
      quadratic K a + quadratic K b - 2 * bilinear K a b := by
  classical
  have h : quadratic K (fun i => a i - b i) =
      quadratic K a + quadratic K b - bilinear K a b - bilinear K b a := by
    unfold quadratic bilinear
    calc
      _ = ∑ i, ∑ j, (a i * a j * K i j + b i * b j * K i j -
          a i * b j * K i j - b i * a j * K i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h, bilinear_symm K hK b a]
  ring

-- CONJECTURE (parent gate and human comparison pending): finite summation identity.
theorem potential_sum (K : ι → ι → ℝ) (a b : ι → ℝ) :
    (∑ i, a i * (∑ j, b j * K i j)) = bilinear K a b := by
  classical
  unfold bilinear
  simp_rw [Finset.mul_sum, mul_assoc]

-- CONJECTURE (parent gate and human comparison pending): finite-matrix weak duality.
theorem matrix_weak_duality (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i)
    (a b V : ι → ℝ) (lam M : ℝ) (ha : ∀ i, 0 ≤ a i) (hmass : ∑ i, a i = lam)
    (hzero : quadratic K (fun i => a i - b i) ≤ 0)
    (hpot : ∀ i, 2 * (∑ j, b j * K i j) - V i ≤ M) :
    quadratic K a - (∑ i, a i * V i) ≤ lam * M - quadratic K b := by
  classical
  have hw : (∑ i, a i * (2 * (∑ j, b j * K i j) - V i)) ≤ ∑ i, a i * M :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpot i) (ha i)
  have heq : (∑ i, a i * (2 * (∑ j, b j * K i j) - V i)) =
      2 * bilinear K a b - ∑ i, a i * V i := by
    calc
      _ = ∑ i, (2 * (a i * (∑ j, b j * K i j)) - a i * V i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * (∑ i, a i * (∑ j, b j * K i j)) - ∑ i, a i * V i := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [potential_sum]
  rw [heq, ← Finset.sum_mul, hmass] at hw
  rw [quadratic_sub K hK a b] at hzero
  linarith

end Mathathon.P108.FiniteDuality

#print axioms Mathathon.P108.FiniteDuality.matrix_weak_duality
