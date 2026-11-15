/- Author: Codex GPT-6 U49/E244. PROOF-DRAFT.
Adapted from Firsching mo271/Zeta5@be1c0d82 Apery/PotentialIneq.lean:1-152;
Paul-Lez metadata, Apache-2.0. Fauzan re-derivation; not a new/independent proof. -/
import Mathlib
import Apery.TableCheck

/-!
# Towards the potential inequality (6.2): reduction to a finite verification

* `Uω_le_inside`, `Uω_le_right`, `Uω_le_left` : certificate shapes for upper bounds of `Uω`;
* `log_le_of_pow_two_upper` : certified upper bounds for logarithms;
* `arctan` reductions;
* `Vfield_ge_Vstar` : the mixed lower bound (A.6) on `[q₋, q₊]`;
* `potential_ineq_tail` : `2 Uρ(t) - V(t) ≤ M₀` for `t ≥ 2`.
-/

open Finset Set

namespace U49
open Apery

/-! ### Certificate shapes -/

lemma Uω_le_inside {a b t u : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) (hu : Real.log ((b - a) / 4) ≤ u) :
    Uω a b t ≤ u := by
  rw [Uω_of_mem h1 h2]; exact hu

lemma Uω_le_right {a b t s u : ℝ} (hab : a < b) (h : b ≤ t) (hs0 : 0 ≤ s)
    (hs : (t - a) * (t - b) ≤ s ^ 2) (hu : Real.log ((t - (a + b) / 2 + s) / 2) ≤ u) :
    Uω a b t ≤ u := by
  rw [Uω_of_ge hab h]
  refine le_trans (Real.log_le_log ?_ ?_) hu
  · have := Real.sqrt_nonneg ((t - a) * (t - b)); linarith
  · have : Real.sqrt ((t - a) * (t - b)) ≤ s := Real.sqrt_le_iff.mpr ⟨hs0, hs⟩
    linarith

lemma Uω_le_left {a b t s u : ℝ} (hab : a < b) (h : t ≤ a) (hs0 : 0 ≤ s)
    (hs : (t - a) * (t - b) ≤ s ^ 2) (hu : Real.log (((a + b) / 2 - t + s) / 2) ≤ u) :
    Uω a b t ≤ u := by
  rw [Uω_of_le hab h]
  refine le_trans (Real.log_le_log ?_ ?_) hu
  · have := Real.sqrt_nonneg ((t - a) * (t - b)); linarith
  · have : Real.sqrt ((t - a) * (t - b)) ≤ s := Real.sqrt_le_iff.mpr ⟨hs0, hs⟩
    linarith

/-- Certified upper bound for `log y`: with `r = 2^k y ≥ 1`, `x = (r-1)/(r+1)`,
`log y ≤ 2 ∑_{j<m} x^(2j+1)/(2j+1) + 2 x^(2m+1)/((2m+1)(1-x²)) - k · 0.6931471803`. -/
lemma log_le_of_pow_two_upper {y : ℝ} (hy : 0 < y) (k m : ℕ) (hk : 1 ≤ 2 ^ k * y) :
    Real.log y ≤ 2 * ∑ j ∈ range m, (1 / (2 * (j : ℝ) + 1)) *
        ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * j + 1) +
      2 * ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * m + 1) /
        ((2 * m + 1) * (1 - ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ 2)) - k * 0.6931471803 := by
  have h1 := log_le_artanh hk m
  have h2 : Real.log (2 ^ k * y) = k * Real.log 2 + Real.log y := by
    rw [Real.log_mul (by positivity) hy.ne', Real.log_pow]
  have h3 := Real.log_two_gt_d9
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h3.le hk0]

/-- `arctan x = π/2 - arctan (1/x)` for `x > 0`. -/
lemma arctan_eq_pi_div_two_sub {x : ℝ} (hx : 0 < x) :
    Real.arctan x = Real.pi / 2 - Real.arctan (1 / x) := by
  rw [one_div, Real.arctan_inv_of_pos hx]; ring

/-- Half-angle lower bound: `2 arctan (x / (1 + w)) ≤ arctan x` when `√(1+x²) ≤ w`. -/
lemma arctan_ge_half {x w : ℝ} (hx : 0 ≤ x) (hw : Real.sqrt (1 + x ^ 2) ≤ w) :
    2 * Real.arctan (x / (1 + w)) ≤ Real.arctan x := by
  rw [arctan_eq_two_mul_arctan hx]
  have hs : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left (Real.arctan_strictMono.monotone ?_) (by norm_num)
  exact div_le_div_of_nonneg_left hx (by linarith) (by linarith)

/-- Half-angle upper bound: `arctan x ≤ 2 arctan (x / (1 + w))` when `0 ≤ w ≤ √(1+x²)`. -/
lemma arctan_le_half {x w : ℝ} (hx : 0 ≤ x) (hw0 : 0 ≤ w) (hw : w ≤ Real.sqrt (1 + x ^ 2)) :
    Real.arctan x ≤ 2 * Real.arctan (x / (1 + w)) := by
  rw [arctan_eq_two_mul_arctan hx]
  refine mul_le_mul_of_nonneg_left (Real.arctan_strictMono.monotone ?_) (by norm_num)
  exact div_le_div_of_nonneg_left hx (by linarith) (by linarith)

/-! ### `Uρ` as an explicit sum of sixteen terms -/

lemma Uρ_eq (t : ℝ) : Uρ t =
    cρ 1 * Uω (aρ 1) (bρ 1) t + cρ 2 * Uω (aρ 2) (bρ 2) t + cρ 3 * Uω (aρ 3) (bρ 3) t +
    cρ 4 * Uω (aρ 4) (bρ 4) t + cρ 5 * Uω (aρ 5) (bρ 5) t + cρ 6 * Uω (aρ 6) (bρ 6) t +
    cρ 7 * Uω (aρ 7) (bρ 7) t + cρ 8 * Uω (aρ 8) (bρ 8) t + cρ 9 * Uω (aρ 9) (bρ 9) t +
    cρ 10 * Uω (aρ 10) (bρ 10) t + cρ 11 * Uω (aρ 11) (bρ 11) t + cρ 12 * Uω (aρ 12) (bρ 12) t +
    cρ 13 * Uω (aρ 13) (bρ 13) t + cρ 14 * Uω (aρ 14) (bρ 14) t + cρ 15 * Uω (aρ 15) (bρ 15) t +
    cρ 16 * Uω (aρ 16) (bρ 16) t := by
  unfold Uρ
  simp only [Finset.sum_Icc_succ_top (show 1 ≤ 16 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 15 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 14 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 13 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 12 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 11 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 10 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 9 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 8 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 7 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 6 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 5 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 4 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 3 by norm_num), Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num),
    Finset.Icc_self, Finset.sum_singleton]

/-! ### The mixed bound (A.6) on `[q₋, q₊]` -/

/-- `V*` of (A.6). -/
noncomputable def Vstar : ℝ :=
  Real.log (1 + qm) - 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
    2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm))

lemma Vfield_ge_Vstar {t : ℝ} (h1 : qm ≤ t) (h2 : t ≤ qp) : Vstar ≤ Vfield t := by
  have hqm : (0 : ℝ) < qm := by norm_num
  have ht : 0 < t := hqm.trans_le h1
  rw [Vfield_eq ht]
  unfold Vstar
  have hs1 : Real.sqrt qm ≤ Real.sqrt t := Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt t ≤ Real.sqrt qp := Real.sqrt_le_sqrt h2
  have hsqm := sqrt_qm_pos
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  -- the parenthesis: `P̃ ≤ P(√t)` and `P̃ < 0`
  have hP1 : Real.arctan (1 / Real.sqrt qp) ≤ Real.arctan (1 / Real.sqrt t) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hst hs2)
  have hP2 : Real.arctan ((3 / 40) / Real.sqrt t) ≤ Real.arctan ((3 / 40) / Real.sqrt qm) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hsqm hs1)
  have hPneg : Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm) < 0 := by
    have := Pfun_sqrt_qm_neg
    unfold Pfun at this
    have h := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsqm
      (Real.sqrt_le_sqrt (by norm_num : qm ≤ qp)))
    linarith
  have hL1 : Real.log (1 + qm) ≤ Real.log (1 + t) := Real.log_le_log (by norm_num) (by linarith)
  have hL2 : Real.log (t + (3 / 40) ^ 2) ≤ Real.log (qp + (3 / 40) ^ 2) :=
    Real.log_le_log (by positivity) (add_le_add h2 le_rfl)
  have hprod : 2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) -
      6 * Real.arctan ((3 / 40) / Real.sqrt qm)) ≤
      2 * Real.sqrt t * (Real.pi + Real.arctan (1 / Real.sqrt t) - 6 * Real.arctan ((3 / 40) / Real.sqrt t)) := by
    have hPle : Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm) ≤
        Real.pi + Real.arctan (1 / Real.sqrt t) - 6 * Real.arctan ((3 / 40) / Real.sqrt t) := by linarith
    calc 2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm))
        ≤ 2 * Real.sqrt t * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm)) :=
          mul_le_mul_of_nonpos_right (by linarith) hPneg.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hPle (by positivity)
  have hL2' : 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) :=
    mul_le_mul_of_nonneg_left hL2 (by norm_num)
  set X := Real.log (1 + t) with hX
  set Y := Real.log (t + (3 / 40) ^ 2) with hY
  set A := 2 * Real.sqrt t * (Real.pi + Real.arctan (1 / Real.sqrt t) - 6 * Real.arctan ((3 / 40) / Real.sqrt t)) with hA
  set X0 := Real.log (1 + qm) with hX0
  set Y0 := Real.log (qp + (3 / 40) ^ 2) with hY0
  set A0 := 2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm)) with hA0
  linarith


end U49

namespace U49
open Apery Finset
lemma Vfield_ge_of_bounds_pos {p slo shi l1 l2 A1 A2 : ℝ} (hp : 0 < p) (hslo : 0 < slo)
    (hs1 : slo ≤ Real.sqrt p) (hs2 : Real.sqrt p ≤ shi) (hl1 : l1 ≤ Real.log (1 + p))
    (hl2 : Real.log (p + (3 / 40) ^ 2) ≤ l2) (hA1 : A1 ≤ Real.arctan (1 / shi))
    (hA2 : Real.arctan ((3 / 40) / slo) ≤ A2)
    (hP : 0 ≤ 3.14159265358979323846 + A1 - 6 * A2) :
    l1 - 6 * (3 / 40) * l2 - 2 + 12 * (3 / 40) + 2 * slo * (3.14159265358979323846 + A1 - 6 * A2) ≤ Vfield p := by
  rw [Vfield_eq hp]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hshi : 0 < shi := hsp.trans_le hs2
  have hm1 : Real.arctan (1 / shi) ≤ Real.arctan (1 / Real.sqrt p) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsp hs2)
  have hm2 : Real.arctan ((3 / 40) / Real.sqrt p) ≤ Real.arctan ((3 / 40) / slo) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hslo hs1)
  have hpi := Real.pi_gt_d20
  have hPle : 3.14159265358979323846 + A1 - 6 * A2 ≤
      Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p) := by linarith
  have hprod : 2 * slo * (3.14159265358979323846 + A1 - 6 * A2) ≤
      2 * Real.sqrt p * (Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p)) :=
    mul_le_mul (by linarith) hPle hP (by positivity)
  have hl2' : 6 * (3 / 40) * Real.log (p + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * l2 :=
    mul_le_mul_of_nonneg_left hl2 (by norm_num)
  linarith

lemma Vfield_ge_of_bounds_neg {p slo shi l1 l2 A1 A2 : ℝ} (hp : 0 < p) (hslo : 0 < slo)
    (hs1 : slo ≤ Real.sqrt p) (hs2 : Real.sqrt p ≤ shi) (hl1 : l1 ≤ Real.log (1 + p))
    (hl2 : Real.log (p + (3 / 40) ^ 2) ≤ l2) (hA1 : A1 ≤ Real.arctan (1 / shi))
    (hA2 : Real.arctan ((3 / 40) / slo) ≤ A2)
    (hP : 3.14159265358979323846 + A1 - 6 * A2 ≤ 0) :
    l1 - 6 * (3 / 40) * l2 - 2 + 12 * (3 / 40) + 2 * shi * (3.14159265358979323846 + A1 - 6 * A2) ≤ Vfield p := by
  rw [Vfield_eq hp]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hshi : 0 < shi := hsp.trans_le hs2
  have hm1 : Real.arctan (1 / shi) ≤ Real.arctan (1 / Real.sqrt p) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsp hs2)
  have hm2 : Real.arctan ((3 / 40) / Real.sqrt p) ≤ Real.arctan ((3 / 40) / slo) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hslo hs1)
  have hpi := Real.pi_gt_d20
  have hPle : 3.14159265358979323846 + A1 - 6 * A2 ≤
      Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p) := by linarith
  have hprod : 2 * shi * (3.14159265358979323846 + A1 - 6 * A2) ≤
      2 * Real.sqrt p * (Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p)) := by
    calc 2 * shi * (3.14159265358979323846 + A1 - 6 * A2)
        ≤ 2 * Real.sqrt p * (3.14159265358979323846 + A1 - 6 * A2) :=
          mul_le_mul_of_nonpos_right (by linarith) hP
      _ ≤ _ := mul_le_mul_of_nonneg_left hPle (by positivity)
  have hl2' : 6 * (3 / 40) * Real.log (p + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * l2 :=
    mul_le_mul_of_nonneg_left hl2 (by norm_num)
  linarith
end U49
