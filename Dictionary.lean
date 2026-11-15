import InnerModelTargets

/- E426 Codex inner_regularity. PROOF-DRAFT actual root floor dictionary.
The auxiliary aCount is the literal continuous-class count used by the E420
worker, a standard decomposition into two interval indicators. -/
open MeasureTheory Set Filter Topology
namespace BInnerLimit
noncomputable section
open Mathathon.P108

def aCount (f z : ℝ) : ℕ :=
  (if z ≤ f then 1 else 0) + (if 1 - f ≤ z then 1 else 0)

theorem floor_sub_half (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ⌊x - z⌋ = ⌊x⌋ - 1 + if z ≤ Int.fract x then 1 else 0 := by
  have hx := Int.floor_add_fract x
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  by_cases h : z ≤ Int.fract x
  · rw [if_pos h, sub_add_cancel]
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · rw [if_neg h, add_zero]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

theorem floor_add_half (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ⌊x + z⌋ = ⌊x⌋ + if 1 - Int.fract x ≤ z then 1 else 0 := by
  have hx := Int.floor_add_fract x
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  by_cases h : 1 - Int.fract x ≤ z
  · rw [if_pos h]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  · rw [if_neg h, add_zero]
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith

theorem ell_fract_dictionary (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ell x z = 2 * (⌊x⌋ : ℝ) + (aCount (Int.fract x) z : ℝ) := by
  unfold ell aCount
  rw [floor_sub_half x z hz0 hz1, floor_add_half x z hz0 hz1]
  by_cases h1 : z ≤ Int.fract x <;> by_cases h2 : 1 - Int.fract x ≤ z <;>
    simp [h1, h2] <;> push_cast <;> ring

#print axioms ell_fract_dictionary
end
end BInnerLimit
