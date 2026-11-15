-- Adapted from Firsching/Paul-Lez mo271/Zeta5@be1c0d82, Growth/ClassData.lean:1-95; Apache-2.0; namespace/import changes only.
import Mathlib
import ClassSum


/-!
# Class data and `v_p(S_K)` in the inner and outer ranges

* `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)` for `1 ≤ c ≤ m`;
* `-v_p(S_K) ≤ -2h⌊K/p⌋ + 12h⌊N/p⌋ + 2 ∑_{j ≥ 1} (h - jp/2)⁺` when `p² > max(2h, N)`, `p` odd.
-/

open Finset

namespace BOuterBridge
open AperyS

variable {p : ℕ} [hp : Fact p.Prime]

lemma succ_mod_cases (X q : ℕ) (hq : 0 < q) :
    ((X + 1) % q = X % q + 1 ∧ (X + 1) / q = X / q) ∨
      (X % q = q - 1 ∧ (X + 1) % q = 0 ∧ (X + 1) / q = X / q + 1) := by
  have h := Nat.div_add_mod X q
  have hl := Nat.mod_lt X hq
  rcases Nat.lt_or_ge (X % q + 1) q with h1 | h1
  · left
    have : (X + 1) / q = X / q ∧ (X + 1) % q = X % q + 1 :=
      (Nat.div_mod_unique hq).mpr ⟨by linarith, h1⟩
    exact ⟨this.2, this.1⟩
  · right
    have hb : X % q = q - 1 := by omega
    have : (X + 1) / q = X / q + 1 ∧ (X + 1) % q = 0 :=
      (Nat.div_mod_unique hq).mpr ⟨by rw [Nat.mul_add, mul_one]; omega, hq⟩
    exact ⟨hb, this.2, this.1⟩

lemma count_res (r : ℕ) (hr1 : 1 ≤ r) (hrp : r < p) (X : ℕ) :
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = ((r : ℤ) : ZMod p)).card =
      X / p + (if r ≤ X % p then 1 else 0) := by
  have hp0 : 0 < p := by omega
  induction X with
  | zero => simp; omega
  | succ X ih =>
    rw [← insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
    have hiff : ((((X + 1 : ℕ) : ℤ) : ZMod p) = ((r : ℤ) : ZMod p)) ↔ (X + 1) % p = r := by
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrp]
    have hnot : X + 1 ∉ (Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = ((r : ℤ) : ZMod p) := by
      simp
    rcases succ_mod_cases X p hp0 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · by_cases h : (X + 1) % p = r
      · rw [if_pos (hiff.mpr h), Finset.card_insert_of_notMem hnot, ih, h2]
        split_ifs <;> omega
      · rw [if_neg (fun h' => h (hiff.mp h')), ih, h2]
        split_ifs <;> omega
    · rw [if_neg (fun h' => by have := hiff.mp h'; omega), ih, h3, h2, h1]
      split_ifs <;> omega

/-- **`SX` on a class**: `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)`. -/
lemma SX_class {m : ℕ} (hm : 2 * m + 1 = p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) (X : ℕ) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = 2 * (X / p) + aCnt p (X % p) c := by
  unfold SX aCnt
  have hneg : -(((c : ℕ) : ℤ) : ZMod p) = (((p - c : ℕ) : ℤ) : ZMod p) := by
    rw [Nat.cast_sub (by omega), Int.cast_sub]; simp
  rw [hneg, count_res c hc1 (by omega) X, count_res (p - c) (by omega) (by omega) X]
  have := Nat.mod_lt X (show 0 < p by omega)
  split_ifs <;> omega

lemma SX_zero (X : ℕ) : SX p X 0 = 2 * (X / p) := by
  unfold SX
  have h : ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = 0).card = X / p := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div X p]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Int.cast_natCast,
      ZMod.natCast_eq_zero_iff]
    omega
  rw [neg_zero, h]; ring

/-! ### `v_p(S_K)` -/

lemma padicValNat_factorial_ge {k : ℕ} : k / p ≤ padicValNat p k.factorial := by
  rcases Nat.lt_or_ge k p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [padicValNat_factorial (b := Nat.log p k + 1) (by omega)]
    have h1 : 1 ∈ Ico 1 (Nat.log p k + 1) := by
      simp only [Finset.mem_Ico]
      exact ⟨le_rfl, by have := Nat.log_pos hp.out.one_lt h; omega⟩
    have := Finset.single_le_sum (f := fun i => k / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this

lemma padicValNat_factorial_small {k : ℕ} (hk : k < p ^ 2) : padicValNat p k.factorial = k / p := by
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · exact Nat.log_lt_of_lt_pow h0.ne' hk

end BOuterBridge
