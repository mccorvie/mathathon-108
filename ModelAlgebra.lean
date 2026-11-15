import CostBounds

/- E420 Codex inner_explicit. PROOF-DRAFT algebra underlying the literal
rootGamma matching. This module does not assert the full local cost bound.
The two adjacent-level interpretation is the same water-filling calculation
as credited E13 and prior Deicyde fixeds7/nu8 InnerLimiting alloc_arith, but
these proofs are written here against the actual imported AperyS.lrow/psiR.
-/

open Finset
namespace BInnerExplicit
noncomputable section
open AperyS

/-- PROOF-DRAFT: base ordinary row count at the exact model balancing level. -/
theorem lrow_model_level (T b q s ellK : ℤ) (hTb : b ≤ T)
    (hEll : ellK = q ∨ ellK = q + 1) :
    lrow (2 * T - q - s) (2 * b - ellK - s + 1) = (T - b).toNat := by
  unfold lrow
  rcases hEll with rfl | rfl <;> omega

/-- PROOF-DRAFT: the next layer fills precisely the classes with ellK=q+1. -/
theorem lrow_next_model_level (T b q s ellK : ℤ) (hTb : b ≤ T)
    (hEll : ellK = q ∨ ellK = q + 1) :
    lrow (2 * T - q - s + 1) (2 * b - ellK - s + 1) =
      (T - b).toNat + if ellK = q + 1 then 1 else 0 := by
  unfold lrow
  rcases hEll with rfl | rfl
  · rw [if_neg (by omega)]
    omega
  · rw [if_pos rfl]
    omega

/-- PROOF-DRAFT: exact arithmetic progression for the actual discrete deficit. -/
theorem two_mul_psiR (k beta : ℤ) :
    2 * psiR k beta = (lrow k beta : ℚ) *
      ((k : ℚ) - beta - ((lrow k beta : ℚ) - 1)) := by
  have hsum (L : ℕ) : 2 * (∑ i ∈ range L, (i : ℚ)) = (L : ℚ) * ((L : ℚ) - 1) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  unfold psiR
  calc
    2 * ∑ i ∈ range (lrow k beta), ((k : ℚ) - 2 * i - beta) / 2 =
        ∑ i ∈ range (lrow k beta), ((k : ℚ) - 2 * i - beta) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      ring
    _ = (lrow k beta : ℚ) * k -
        2 * (∑ i ∈ range (lrow k beta), (i : ℚ)) - (lrow k beta : ℚ) * beta := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    _ = _ := by nlinarith [hsum (lrow k beta)]

/-- PROOF-DRAFT: exact row deficit in the two-value ellK class model. -/
theorem psiR_model_level (T b q s ellK : ℤ) (hTb : b ≤ T)
    (hEll : ellK = q ∨ ellK = q + 1) :
    2 * psiR (2 * T - q - s) (2 * b - ellK - s + 1) =
      ((T : ℚ) - b) * ((T : ℚ) - b + ((ellK : ℚ) - q)) := by
  rw [two_mul_psiR, lrow_model_level T b q s ellK hTb hEll]
  have hcast : ((T - b).toNat : ℚ) = (T : ℚ) - b := by
    have hInt : ((T - b).toNat : ℤ) = T - b := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hInt
  rw [hcast]
  push_cast
  ring

/-- PROOF-DRAFT: finite base-layer Phi is exactly the ordinary model row sum
plus its zero-class row remainder. No limiting/Riemann assertion is assumed. -/
theorem PhiK_model_level {m : ℕ} (beta b ellK : Fin (m + 1) → ℤ)
    (h : ℕ) (T q s : ℤ)
    (hBeta : ∀ c ∈ (univ : Finset (Fin (m + 1))).erase 0,
      beta c = 2 * b c - ellK c - s + 1)
    (hTb : ∀ c ∈ (univ : Finset (Fin (m + 1))).erase 0, b c ≤ T)
    (hEll : ∀ c ∈ (univ : Finset (Fin (m + 1))).erase 0, ellK c = q ∨ ellK c = q + 1) :
    2 * PhiK beta h (2 * T - q - s) =
      (∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0,
        ((T : ℚ) - b c) * ((T : ℚ) + b c - ellK c - s)) +
      ((2 * T - q - s : ℤ) : ℚ) * ((h : ℚ) -
        ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, ((T : ℚ) - b c)) := by
  have hsum :
      (∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0,
        ((T : ℚ) - b c) * ((T : ℚ) + b c - ellK c - s)) =
      ((2 * T - q - s : ℤ) : ℚ) *
        (∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, ((T : ℚ) - b c)) -
      2 * ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, psiR (2 * T - q - s) (beta c) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hBeta c hc, psiR_model_level T (b c) q s (ellK c) (hTb c hc) (hEll c hc)]
    push_cast
    ring
  unfold PhiK
  nlinarith

end
end BInnerExplicit
