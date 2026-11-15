import ContinuousClasses
import Dictionary

/- E420 Codex inner_explicit. PROOF-DRAFT exact mesh dictionary.
This links the actual imported SX counts to the continuous class indicators.
It uses only Mathlib floor/fract division identities and the credited Apache
ClassData SX_class proof, rather than a replaced finite exponent.
-/

namespace BInnerExplicit
noncomputable section
open AperyS ContinuousClasses

/-- PROOF-DRAFT: the continuous two-indicator count agrees exactly on the mesh. -/
lemma aCount_mesh {p r c : ℕ} (hp : 0 < p) (hr : r ≤ p) :
    aCount ((r : ℝ) / p) ((c : ℝ) / p) = ClassSums.aCnt p r c := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : (c : ℝ) / p ≤ (r : ℝ) / p ↔ c ≤ r := by
    rw [div_le_div_iff_of_pos_right hpR]
    exact Nat.cast_le
  have h2 : (1 : ℝ) - (r : ℝ) / p ≤ (c : ℝ) / p ↔ p - r ≤ c := by
    rw [le_div_iff₀ hpR, sub_mul, one_mul, div_mul_cancel₀ _ hpR.ne', ← Nat.cast_sub hr]
    exact Nat.cast_le
  simp only [aCount, ClassSums.aCnt, h1, h2]

/-- PROOF-DRAFT: standard Nat quotient is the real floor at every positive p. -/
lemma floor_nat_div (K p : ℕ) : ⌊(K : ℝ) / p⌋ = ((K / p : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_natCast]
  exact_mod_cast (rfl : K / p = K / p)

variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: actual ordinary SX count as the exact continuous mesh value. -/
lemma SX_mesh (K : ℕ) (hodd : 2 * (p / 2) + 1 = p)
    (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    SX p K (((c : ℕ) : ℤ) : ZMod p) = 2 * (K / p) +
      aCount (((K % p : ℕ) : ℝ) / p) ((c : ℕ) / (p : ℝ)) := by
  have hc1 : 1 ≤ (c : ℕ) := by
    have : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
    omega
  rw [SX_class hodd hc1 (by omega),
    aCount_mesh (p := p) (r := K % p) (c := (c : ℕ)) hp.out.pos (Nat.mod_lt K hp.out.pos).le]
  rfl

/-- PROOF-DRAFT: exact actual finite count equals the ACTUAL root ell at a mesh point. -/
lemma SX_eq_root_ell (K : ℕ) (hodd : 2 * (p / 2) + 1 = p)
    (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℝ) =
      Mathathon.P108.ell ((K : ℝ) / p) ((c : ℕ) / (p : ℝ)) := by
  have hc0 : 0 ≤ ((c : ℕ) : ℝ) / p := by positivity
  have hcHalf : ((c : ℕ) : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_iff₀ (by exact_mod_cast hp.out.pos : (0 : ℝ) < p)]
    have hcNat : 2 * (c : ℕ) ≤ p := by omega
    have hcReal : (2 : ℝ) * (c : ℕ) ≤ p := by exact_mod_cast hcNat
    linarith
  rw [BInnerLimit.ell_fract_dictionary _ _ hc0 hcHalf,
    floor_nat_div, Int.fract_div_natCast_eq_div_natCast_mod]
  change (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℝ) =
    2 * ((K / p : ℕ) : ℝ) +
      (ContinuousClasses.aCount (((K % p : ℕ) : ℝ) / p) ((c : ℕ) / (p : ℝ)) : ℝ)
  exact_mod_cast SX_mesh K hodd c hc

/-- PROOF-DRAFT: the generic floor sum takes exactly the two adjacent values. -/
lemma floor_sum_two_values (x z : ℝ) :
    ⌊x - z⌋ + ⌊x + z⌋ + 1 = ⌊2 * x⌋ ∨
      ⌊x - z⌋ + ⌊x + z⌋ + 1 = ⌊2 * x⌋ + 1 := by
  have hA := Int.floor_le (x - z)
  have hB := Int.floor_le (x + z)
  have hA' := Int.lt_floor_add_one (x - z)
  have hB' := Int.lt_floor_add_one (x + z)
  have hq := Int.floor_le (2 * x)
  have hlo : ⌊x - z⌋ + ⌊x + z⌋ ≤ ⌊2 * x⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith
  have hhiR : (⌊2 * x⌋ : ℝ) < (⌊x - z⌋ : ℝ) + (⌊x + z⌋ : ℝ) + 2 := by linarith
  have hhi : ⌊2 * x⌋ < ⌊x - z⌋ + ⌊x + z⌋ + 2 := by exact_mod_cast hhiR
  omega

/-- PROOF-DRAFT: actual ordinary counts satisfy the exact two-value model. -/
lemma SX_two_values (K : ℕ) (hodd : 2 * (p / 2) + 1 = p)
    (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) = ⌊2 * ((K : ℝ) / p)⌋ ∨
      (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) = ⌊2 * ((K : ℝ) / p)⌋ + 1 := by
  have hSX := SX_eq_root_ell K hodd c hc
  unfold Mathathon.P108.ell at hSX
  have hSXint : (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) =
      ⌊(K : ℝ) / p - ((c : ℕ) : ℝ) / p⌋ +
        ⌊(K : ℝ) / p + ((c : ℕ) : ℝ) / p⌋ + 1 := by exact_mod_cast hSX
  rw [hSXint]
  exact floor_sum_two_values _ _

end
end BInnerExplicit
