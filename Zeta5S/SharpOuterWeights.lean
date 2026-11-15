import Zeta5S.SharpOuterFrame
import Zeta5S.SmallFiniteStep

/-!
L11/E310, Codex lane L. Status: PROOF-DRAFT pending repository gate.
Exact half-integral gap and zero count of the unchanged upstream outer weights.
-/
open Finset Polynomial
namespace AperyS

lemma min_zero_half_integer (t : ℚ) (z : ℤ) (hz : 2 * t = (z : ℚ)) :
    min 0 t = 0 ∨ min 0 t ≤ -1 / 2 := by
  by_cases ht : 0 ≤ t
  · exact Or.inl (min_eq_left ht)
  · right
    have ht' : t < 0 := lt_of_not_ge ht
    have hz' : z < 0 := by exact_mod_cast (show (z : ℚ) < 0 by linarith)
    have hz1 : z ≤ -1 := by omega
    have hzq : (z : ℚ) ≤ -1 := by exact_mod_cast hz1
    rw [min_eq_right (le_of_lt ht')]
    linarith

variable {p m : ℕ} [Fact p.Prime]

theorem wO_gap (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ) :
    wO hm s ν N K c i = 0 ∨ wO hm s ν N K c i ≤ -1 / 2 := by
  by_cases hc : c = 0
  · subst c
    simp only [wO, if_pos rfl]
    split_ifs <;> norm_num
  · by_cases hi : i < nbC hm N K c
    · rw [wO_eq_min hm s ν N K c i hc hi]
      apply min_zero_half_integer _ (2 * (i : ℤ) + (ν : ℤ) * delC N c -
        ((ellC hm K c : ℤ) + (s : ℤ) - 1))
      unfold outerArg
      push_cast
      ring
    · left
      simp [wO, hc, hi]

noncomputable def outerZeroCount (hm : 2 * m + 1 = p) (s ν N K : ℕ) : ℕ :=
  ∑ c, ((range (LoC hm N K c)).filter fun i => wO hm s ν N K c i = 0).card

theorem zeroWeightCount_outer_equiv {h : ℕ} (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (e : (Σ c : Fin (m + 1), Fin (LoC hm N K c)) ≃ Fin h) :
    zeroWeightCount (fun a => wO hm s ν N K (e.symm a).1 (e.symm a).2) =
      outerZeroCount hm s ν N K := by
  classical
  unfold zeroWeightCount outerZeroCount
  simp only [Finset.card_filter]
  rw [Equiv.sum_comp e.symm (fun u => if wO hm s ν N K u.1 u.2 = 0 then 1 else 0),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact Fin.sum_univ_eq_sum_range (fun i => if wO hm s ν N K c i = 0 then 1 else 0) _

end AperyS
