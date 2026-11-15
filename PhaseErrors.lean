import ModelData
import NextRows

/- E420 native Codex inner_explicit. PROOF-DRAFT bounded phase remainders
for the literal actual Gamma model. No prime limit/optimization is claimed. -/
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108 Mathathon.P108.RangeBridgeTarget
variable {p : ℕ} [hp : Fact p.Prime]

theorem model_rows_base_real (s r n : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hin : 3 * p ≤ 40 * n) :
    (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) =
      ((p / 2 : ℕ) : ℝ) * (modelT (2 * r) n p : ℝ) - (r : ℝ) *
        (((3 * n : ℕ) : ℝ) - ((3 * n / p : ℕ) : ℝ)) := by
  have hbase := rowsK_model_base s r (40 * n) (3 * n) (modelT (2 * r) n p) hodd
    (modelT_ge_class r n hr hodd hin)
  have hLift := congrArg (fun z : ℚ => (z : ℝ)) hbase
  push_cast at hLift
  simpa only [modelKappa, modelQ, modelX, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.div_le_self (3 * n) p)] using hLift

lemma model_H_shape (r n : ℕ) :
    (p : ℝ) * Hc ((2 * r : ℕ) : ℝ) (3 / 40) * modelX n p =
      ((37 * n : ℕ) : ℝ) + (r : ℝ) * ((3 * n : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpx : (p : ℝ) * modelX n p = ((40 * n : ℕ) : ℝ) := by
    unfold modelX
    exact mul_div_cancel₀ _ hpR.ne'
  calc
    _ = Hc ((2 * r : ℕ) : ℝ) (3 / 40) * ((p : ℝ) * modelX n p) := by ring
    _ = _ := by rw [hpx]; unfold Hc; push_cast; ring

/-- PROOF-DRAFT: exact bounded residual left by the base ordinary layer. -/
theorem model_rows_remainder (s r n : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hin : 3 * p ≤ 40 * n) :
    ((37 * n : ℕ) : ℝ) -
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) -
        (p : ℝ) * sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) =
      (modelT (2 * r) n p : ℝ) / 2 - (r : ℝ) * ((3 * n / p : ℕ) : ℝ) := by
  have hbase := model_rows_base_real s r n hr hodd hin
  have hoddR : 2 * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hodd
  have hmR : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by linarith
  have hmT : ((p / 2 : ℕ) : ℝ) * (modelT (2 * r) n p : ℝ) =
      ((p : ℝ) * (modelT (2 * r) n p : ℝ) - (modelT (2 * r) n p : ℝ)) / 2 := by rw [hmR]; ring
  rw [hmT] at hbase
  have hHx := model_H_shape (p := p) r n
  have hSigma : (p : ℝ) * sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) =
      ((37 * n : ℕ) : ℝ) + (r : ℝ) * ((3 * n : ℕ) : ℝ) -
        (p : ℝ) * (modelT (2 * r) n p : ℝ) / 2 := by
    unfold sigmaC
    rw [← modelT_cast]
    nlinarith
  nlinarith

/-- PROOF-DRAFT: the base remainder is uniformly O(M), not O(p). -/
theorem model_rows_remainder_bound (s r n M : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    |((37 * n : ℕ) : ℝ) -
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) -
        (p : ℝ) * sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ 11 * M := by
  rw [model_rows_remainder s r n hr hodd hin]
  have hT := modelT_bounds (2 * r) n M (by omega) hKM
  have hq : 3 * n / p ≤ M := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith) |>.le
  have hqR : ((3 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hq
  have hrR : (r : ℝ) ≤ 5 := by exact_mod_cast hr
  have hrq := mul_le_mul hrR hqR (by positivity : (0 : ℝ) ≤ (3 * n / p : ℕ)) (by norm_num : (0 : ℝ) ≤ 5)
  have hrq0 : (0 : ℝ) ≤ (r : ℝ) * ((3 * n / p : ℕ) : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith [hT.1, hT.2]

lemma modelQ_bounds (n M : ℕ) (hKM : 40 * n < p * M) :
    0 ≤ (modelQ n p : ℝ) ∧ (modelQ n p : ℝ) ≤ 2 * M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hx0 : 0 ≤ modelX n p := by unfold modelX; positivity
  have hxM : modelX n p ≤ M := by
    unfold modelX
    rw [div_le_iff₀ hpR]
    exact_mod_cast (show 40 * n ≤ M * p by nlinarith)
  constructor
  · have : (0 : ℤ) ≤ modelQ n p := Int.floor_nonneg.mpr (by positivity)
    exact_mod_cast this
  · exact (Int.floor_le (2 * modelX n p)).trans (by linarith)

/-- PROOF-DRAFT: finite upper-count class mass versus the actual nplus phase. -/
theorem model_good_remainder (n : ℕ) (hodd : 2 * (p / 2) + 1 = p) :
    (((40 * n - 40 * n / p : ℕ) : ℝ) -
        ((p / 2 : ℕ) : ℝ) * (modelQ n p : ℝ)) - (p : ℝ) * nplus (modelX n p) =
      (modelQ n p : ℝ) / 2 - ((40 * n / p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hoddR : 2 * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hodd
  have hmR : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by linarith
  have hpx : (p : ℝ) * modelX n p = ((40 * n : ℕ) : ℝ) := by
    unfold modelX
    exact mul_div_cancel₀ _ hpR.ne'
  rw [Nat.cast_sub (Nat.div_le_self (40 * n) p), hmR]
  unfold nplus
  change _ - (p : ℝ) * ((2 * modelX n p - (modelQ n p : ℝ)) / 2) = _
  nlinarith

theorem model_good_remainder_bound (n M : ℕ) (hodd : 2 * (p / 2) + 1 = p)
    (hKM : 40 * n < p * M) :
    |(((40 * n - 40 * n / p : ℕ) : ℝ) -
        ((p / 2 : ℕ) : ℝ) * (modelQ n p : ℝ)) - (p : ℝ) * nplus (modelX n p)| ≤ 2 * M := by
  rw [model_good_remainder n hodd]
  have hQ := modelQ_bounds n M hKM
  have hq : 40 * n / p ≤ M := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith) |>.le
  have hqR : ((40 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (40 * n / p : ℕ) := by positivity
  rw [abs_le]
  constructor <;> linarith [hQ.1, hQ.2]

/-- PROOF-DRAFT: the next Phi slope differs from the actual fractional phase
by at most13M. This includes the finite ordinary-class count correction. -/
theorem model_next_remainder_bound (s r n M : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    |((37 * n : ℕ) : ℝ) -
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 1) : ℝ) -
        (p : ℝ) * (sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) - nplus (modelX n p))| ≤ 13 * M := by
  have hnext := rowsK_model_plus_one s r (40 * n) (3 * n) (modelT (2 * r) n p) hodd
    (modelT_ge_class r n hr hodd hin)
  have hnextLift := congrArg (fun z : ℚ => (z : ℝ)) hnext
  push_cast at hnextLift
  have hnextR :
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 1) : ℝ) =
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) +
          ((40 * n - 40 * n / p : ℕ) : ℝ) - ((p / 2 : ℕ) : ℝ) * (modelQ n p : ℝ) := by
    simpa only [modelKappa, modelQ, modelX, Nat.cast_mul, Nat.cast_ofNat] using hnextLift
  have hbase := model_rows_remainder_bound s r n M hr hodd hKM hin
  have hgood := model_good_remainder_bound n M hodd hKM
  have heq : ((37 * n : ℕ) : ℝ) -
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p + 1) : ℝ) -
        (p : ℝ) * (sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) - nplus (modelX n p)) =
      (((37 * n : ℕ) : ℝ) -
        (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) -
          (p : ℝ) * sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)) -
        ((((40 * n - 40 * n / p : ℕ) : ℝ) - ((p / 2 : ℕ) : ℝ) * (modelQ n p : ℝ)) -
          (p : ℝ) * nplus (modelX n p)) := by rw [hnextR]; ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem modelKappa_bound (s ν n M : ℕ) (hν : ν ≤ 10) (hKM : 40 * n < p * M) :
    |(modelKappa s ν n p : ℝ)| ≤ (s : ℝ) + 26 * M := by
  have hT := modelT_bounds ν n M hν hKM
  have hQ := modelQ_bounds n M hKM
  unfold modelKappa
  push_cast
  rw [abs_le]
  constructor <;> linarith [hT.1, hT.2, hQ.1, hQ.2]

end
end BInnerExplicit
