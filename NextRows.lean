import ClassRows

/- E420 native Codex inner_explicit. PROOF-DRAFT exact next-layer row count.
This is the actual kf comparison model, not an allocation optimum theorem. -/
open Finset
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108.RangeBridgeTarget
variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: the next model layer adds the exact upper-count class mass. -/
theorem rowsK_model_plus_one (s r K N : ℕ) (T : ℤ)
    (hodd : 2 * (p / 2) + 1 = p)
    (hTb : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ T) :
    (rowsK (beta s (2 * r) K N p) (2 * T - ⌊2 * ((K : ℝ) / p)⌋ - s + 1) : ℚ) =
      (rowsK (beta s (2 * r) K N p) (2 * T - ⌊2 * ((K : ℝ) / p)⌋ - s) : ℚ) +
        ((K - K / p : ℕ) : ℚ) - ((p / 2 : ℕ) : ℚ) * (⌊2 * ((K : ℝ) / p)⌋ : ℚ) := by
  let q : ℤ := ⌊2 * ((K : ℝ) / p)⌋
  have hrow (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
      (lrow (2 * T - q - s + 1) (beta s (2 * r) K N p c) : ℚ) =
        (lrow (2 * T - q - s) (beta s (2 * r) K N p c) : ℚ) +
          (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ) - q := by
    have hβ : beta s (2 * r) K N p c =
        2 * ((r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ)) -
          (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) - s + 1 := by
      unfold beta
      push_cast
      ring
    have hEll := SX_two_values K hodd c hc
    rw [hβ, lrow_next_model_level T _ q s _ (hTb c hc) hEll,
      lrow_model_level T _ q s _ (hTb c hc) hEll]
    have hδ : (if (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) = q + 1 then (1 : ℚ) else 0) =
        (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ) - q := by
      rcases hEll with h0 | h1
      · have h0Q : (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ) = q := by exact_mod_cast h0
        have hne : (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≠ q + 1 := by rw [h0]; omega
        rw [if_neg hne, h0Q]
        ring
      · have h1Q : (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ) = (q : ℚ) + 1 := by exact_mod_cast h1
        rw [if_pos h1, h1Q]
        ring
    push_cast
    push_cast at hδ
    rw [hδ]
    ring
  unfold rowsK
  rw [Nat.cast_sum, Nat.cast_sum]
  calc
    _ = ∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
        ((lrow (2 * T - q - s) (beta s (2 * r) K N p c) : ℚ) +
          (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ) - q) := by
      exact Finset.sum_congr rfl fun c hc => hrow c (Finset.mem_erase.mp hc).1
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const]
      have hcard : ((univ : Finset (Fin (p / 2 + 1))).erase 0).card = p / 2 := by simp
      have hSXsumQ : (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
          (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℚ)) = ((K - K / p : ℕ) : ℚ) := by
        exact_mod_cast sum_SX_ordinary K hodd
      rw [hcard, hSXsumQ]
      simp only [nsmul_eq_mul]
      rfl

end
end BInnerExplicit
