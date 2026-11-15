import BInnerStatement
/- E420, Codex inner_explicit. PROOF-DRAFT helper adaptation.
CITED: Firsching/Paul-Lez mo271/Zeta5@be1c0d82, Apache2.0.
Apery/Growth/ClassData.lean18-74 verbatim proof bodies, namespace adapted
and actual AperyS.SX supplied by the unchanged event arithmetic import.
aCnt formula copied from Apery/Growth/ClassSum.lean34-35.
-/
open Finset
namespace BInnerExplicit
open AperyS
variable {p : ℕ} [hp : Fact p.Prime]
def aCnt (p v c : ℕ) : ℕ := (if c ≤ v then 1 else 0) + (if p - v ≤ c then 1 else 0)
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


/- CITED: pinned upstream Apery/Norm.lean99-111; proof body unchanged, actual AperyS definitions. -/
lemma Sep_PlK {K : ℕ} (hK : 2 * K < p ^ 2) : Sep p (PlK K) := by
  intro r hr s hs hrs _ hdvd
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  obtain ⟨j', hj', ε', hε', rfl⟩ := mem_PlK_iff hs
  have h1 := Finset.mem_Icc.mp hj
  have h2 := Finset.mem_Icc.mp hj'
  have hlt : |ε * (j : ℤ) - ε' * j'| < (p : ℤ) ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> rw [abs_lt] <;> constructor <;>
      push_cast <;> nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hrs (by linarith)

end BInnerExplicit
