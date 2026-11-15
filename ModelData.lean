import GammaApprox

/- E420 native Codex inner_explicit. PROOF-DRAFT actual balancing-level data.
All auxiliary floors below are literally the floors in actual Tc/innerGamma.
-/
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108 Mathathon.P108.RangeBridgeTarget

def modelX (n p : ℕ) : ℝ := ((40 * n : ℕ) : ℝ) / p
def modelT (ν n p : ℕ) : ℤ := ⌊2 * Hc (ν : ℝ) (3 / 40) * modelX n p⌋
def modelQ (n p : ℕ) : ℤ := ⌊2 * modelX n p⌋
def modelKappa (s ν n p : ℕ) : ℤ := 2 * modelT ν n p - modelQ n p - s

lemma modelT_cast (ν n p : ℕ) :
    (modelT ν n p : ℝ) = Tc (ν : ℝ) (3 / 40) (modelX n p) := rfl

variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: every actual base-layer row count is nonnegative in scope. -/
theorem modelT_ge_class (r n : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hin : 3 * p ≤ 40 * n)
    (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    (r : ℤ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ modelT (2 * r) n p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hx3 : (3 : ℝ) ≤ modelX n p := by
    unfold modelX
    rw [le_div_iff₀ hpR]
    exact_mod_cast hin
  have hSX := SX_eq_root_ell (3 * n) hodd c hc
  have hS : (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) ≤
      2 * (((3 * n : ℕ) : ℝ) / p) + 1 := by
    rw [hSX]
    unfold ell
    linarith [Int.floor_le (((3 * n : ℕ) : ℝ) / p - ((c : ℕ) : ℝ) / p),
      Int.floor_le (((3 * n : ℕ) : ℝ) / p + ((c : ℕ) : ℝ) / p)]
  rw [← alpha_shape n p] at hS
  have hprod := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ r by positivity)
  have hrR : (r : ℝ) ≤ 5 := by exact_mod_cast hr
  unfold modelT
  apply Int.le_floor.mpr
  push_cast
  unfold Hc
  change _ ≤ 2 * (1 - 3 / 40 + (2 * (r : ℝ)) / 2 * (3 / 40)) * modelX n p
  change (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) ≤
      (r : ℝ) * (2 * ((3 / 40 : ℝ) * modelX n p) + 1) at hprod
  push_cast at hprod
  nlinarith

/-- PROOF-DRAFT: the actual floor level is uniformly bounded on the inner window. -/
theorem modelT_bounds (ν n M : ℕ) (hν : ν ≤ 10) (hKM : 40 * n < p * M) :
    0 ≤ (modelT ν n p : ℝ) ∧ (modelT ν n p : ℝ) ≤ 12 * M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hx0 : 0 ≤ modelX n p := by unfold modelX; positivity
  have hxM : modelX n p ≤ M := by
    unfold modelX
    rw [div_le_iff₀ hpR]
    exact_mod_cast (show 40 * n ≤ M * p by nlinarith)
  have hH0 : 0 ≤ Hc (ν : ℝ) (3 / 40) := by unfold Hc; positivity
  have hH : Hc (ν : ℝ) (3 / 40) ≤ 6 := by
    have hνR : (ν : ℝ) ≤ 10 := by exact_mod_cast hν
    unfold Hc
    linarith
  constructor
  · have : (0 : ℤ) ≤ modelT ν n p := Int.floor_nonneg.mpr (by positivity)
    exact_mod_cast this
  · have hfloor := Int.floor_le (2 * Hc (ν : ℝ) (3 / 40) * modelX n p)
    have hprod := mul_le_mul_of_nonneg_right hH hx0
    unfold modelT
    nlinarith

/-- PROOF-DRAFT: actual row counts bracket the near-maximizing model levels.
This is a finite calculation for beta at nu=2r, not an all-allocation theorem. -/
theorem rows_model_near_peak (s r n M : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℚ) ≤
        (37 * n : ℕ) + (6 * M + 1 : ℕ) ∧
      ((37 * n : ℕ) : ℚ) - ((6 * M + 1 : ℕ) : ℚ) ≤
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 2) : ℚ) := by
  have hTb := modelT_ge_class r n hr hodd hin
  have hbase := rowsK_model_base s r (40 * n) (3 * n) (modelT (2 * r) n p) hodd hTb
  have hplus := rowsK_model_plus_two s r (40 * n) (3 * n) (modelT (2 * r) n p) hodd hTb
  have hbaseR :
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) =
        ((p / 2 : ℕ) : ℝ) * (modelT (2 * r) n p : ℝ) - (r : ℝ) *
          (((3 * n : ℕ) : ℝ) - ((3 * n / p : ℕ) : ℝ)) := by
    have hbase' :
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) =
          ((p / 2 : ℕ) : ℝ) * (modelT (2 * r) n p : ℝ) - (r : ℝ) * ((3 * n - 3 * n / p : ℕ) : ℝ) := by
      have hLift := congrArg (fun z : ℚ => (z : ℝ)) hbase
      push_cast at hLift
      simpa only [modelKappa, modelQ, modelX, Nat.cast_mul, Nat.cast_ofNat] using hLift
    simpa only [Nat.cast_sub (Nat.div_le_self (3 * n) p)] using hbase'
  have hplusR :
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 2) : ℝ) =
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) + ((p / 2 : ℕ) : ℝ) := by
    exact_mod_cast hplus
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hmR : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
    have hoddR : 2 * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hodd
    linarith
  have hmT : ((p / 2 : ℕ) : ℝ) * (modelT (2 * r) n p : ℝ) =
      ((p : ℝ) * (modelT (2 * r) n p : ℝ) - (modelT (2 * r) n p : ℝ)) / 2 := by rw [hmR]; ring
  rw [hmT] at hbaseR
  have hpx : (p : ℝ) * modelX n p = ((40 * n : ℕ) : ℝ) := by
    unfold modelX
    exact mul_div_cancel₀ _ hpR.ne'
  have hHx : (p : ℝ) * Hc ((2 * r : ℕ) : ℝ) (3 / 40) * modelX n p =
      ((37 * n : ℕ) : ℝ) + (r : ℝ) * ((3 * n : ℕ) : ℝ) := by
    calc
      _ = Hc ((2 * r : ℕ) : ℝ) (3 / 40) * ((p : ℝ) * modelX n p) := by ring
      _ = _ := by rw [hpx]; unfold Hc; push_cast; ring
  have hfloor := Int.floor_le (2 * Hc ((2 * r : ℕ) : ℝ) (3 / 40) * modelX n p)
  have hfloor' := Int.lt_floor_add_one (2 * Hc ((2 * r : ℕ) : ℝ) (3 / 40) * modelX n p)
  change (modelT (2 * r) n p : ℝ) ≤ _ at hfloor
  change _ < (modelT (2 * r) n p : ℝ) + 1 at hfloor'
  have hpFloor := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hpFloor' := mul_lt_mul_of_pos_left hfloor' hpR
  have hT := modelT_bounds (2 * r) n M (by omega) hKM
  have hq : 3 * n / p ≤ M := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith) |>.le
  have hqR : ((3 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hq
  have hrR : (r : ℝ) ≤ 5 := by exact_mod_cast hr
  have hrq := mul_le_mul hrR hqR (by positivity : (0 : ℝ) ≤ (3 * n / p : ℕ)) (by norm_num : (0 : ℝ) ≤ 5)
  have hrq0 : (0 : ℝ) ≤ (r : ℝ) * ((3 * n / p : ℕ) : ℝ) := by positivity
  have hu :
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) ≤
        ((37 * n : ℕ) : ℝ) + (6 * (M : ℝ) + 1) := by nlinarith [hT.1, hT.2]
  have hl :
      ((37 * n : ℕ) : ℝ) - (6 * (M : ℝ) + 1) ≤
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 2) : ℝ) := by
    nlinarith [hT.1, hT.2]
  constructor
  · exact_mod_cast hu
  · exact_mod_cast hl

end
end BInnerExplicit
