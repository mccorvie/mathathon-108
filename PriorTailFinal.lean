import Apery.Table.Tail
/-! CITED: Moritz Firsching, mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/EnergyFinal.lean88-110, Apache-2.0. Paul-Lez contributed Comparator metadata.
The following prior declaration is copied byte-for-byte; no fine chunk import.
Supporting status PROOF-DRAFT until parent gate, overall CONJECTURE. -/
open MeasureTheory Set Real Filter Topology Finset
open Apery
namespace U51.Prior
lemma potential_ineq_tail' {t c : ℝ} (ht : 2 ≤ t) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 20) :
    2 * Uρ t - Vfield t + c * Real.sqrt t ≤ M0 := by
  have ht0 : 0 < t := by linarith
  have h1 := Uρ_le_log ht
  have h2 := Vfield_ge_tail ht
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs2 : (141 / 100 : ℝ) ≤ Real.sqrt t := le_sqrt_of_sq_le (by norm_num) (by norm_num; linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have e : Real.log (Real.sqrt t ^ 2) = 2 * Real.log (Real.sqrt t) := by
      rw [Real.log_pow]; norm_num
    rw [hs] at e
    rw [e]
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hq : (3 / 40 : ℝ) ^ 2 / t ≤ (3 / 40) ^ 2 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hpi := Real.pi_gt_d2
  have hprod : 314 / 100 * Real.sqrt t ≤ Real.pi * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (by norm_num at hpi; linarith) hs0.le
  have hcs : c * Real.sqrt t ≤ 1 / 20 * Real.sqrt t := mul_le_mul_of_nonneg_right hc hs0.le
  unfold M0
  linarith


end U51.Prior
