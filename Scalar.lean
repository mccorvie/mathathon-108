import OuterTargets

/-! E418 scalar helper, Codex outer_above_k,2026-11-14.
PROOF-DRAFT pending driver gate. Adapted from Firsching/Paul-Lez,
mo271/Zeta5@be1c0d82,Apery/Legendre.lean:27-61; factorial-small helper
is the source argument of Apery/Growth/ClassData.lean:88-94,Apache-2.0.
Actual AperyS.SS and AssemblyTarget.vSK are retained unchanged.
-/
open Finset
namespace BOuterAboveK
noncomputable section
open AperyS AperyS.AssemblyTarget

theorem scalar_valuation (ν K N h p : ℕ) [Fact p.Prime] :
    padicValRat p (SS ν K N h) =
      (2 * h : ℕ) * (padicValNat p K.factorial : ℤ) +
        (h - 1 : ℕ) * (padicValNat p 4 : ℤ) -
        (2 * ν * h : ℕ) * (padicValNat p N.factorial : ℤ) -
        2 * ∑ i ∈ Icc 1 (h - 1), (padicValNat p (2 * i).factorial : ℤ) := by
  have hnum : ((K.factorial : ℚ) ^ (2 * h) * 4 ^ (h - 1)) ≠ 0 := by positivity
  have hden : ((N.factorial : ℚ) ^ (2 * ν * h) *
      ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2) ≠ 0 := by
    apply mul_ne_zero (by positivity)
    exact prod_ne_zero_iff.mpr fun i _ => by positivity
  unfold SS
  rw [padicValRat.div hnum hden,
    padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul (by positivity) (prod_ne_zero_iff.mpr fun i _ => by positivity),
    padicValRat_finset_prod _ _ (fun i _ => by positivity)]
  simp only [padicValRat.pow, padicValRat.of_nat]
  rw [mul_sum]
  push_cast
  ring

theorem vSK_formula (ν K N p : ℕ) [Fact p.Prime] :
    vSK ν K N p =
      (2 * (K - N) : ℕ) * (padicValNat p K.factorial : ℤ) +
        ((K - N) - 1 : ℕ) * (padicValNat p 4 : ℤ) -
        (2 * ν * (K - N) : ℕ) * (padicValNat p N.factorial : ℤ) -
        2 * ∑ i ∈ Icc 1 ((K - N) - 1), (padicValNat p (2 * i).factorial : ℤ) :=
  scalar_valuation ν K N (K - N) p

lemma factorial_val_lt {p k : ℕ} [hp : Fact p.Prime] (hk : k < p) :
    padicValNat p k.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => by
    have := hp.out.dvd_factorial.mp h
    omega)

lemma factorial_val_small {p k : ℕ} [Fact p.Prime] (hk : k < p ^ 2) :
    padicValNat p k.factorial = k / p := by
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · exact Nat.log_lt_of_lt_pow h0.ne' hk

lemma sum_double_div {p m h : ℕ} (hm : 2 * m + 1 = p) (hh1 : 1 ≤ h) (hhp : h ≤ p) :
    ∑ i ∈ Icc 1 (h - 1), 2 * i / p = h - (m + 1) := by
  have hterm : ∀ i ∈ Icc 1 (h - 1), 2 * i / p = if m < i then 1 else 0 := by
    intro i hi
    have hi' := mem_Icc.mp hi
    split_ifs with hmi
    · exact Nat.div_eq_of_lt_le (by omega : 1 * p ≤ 2 * i) (by omega : 2 * i < (1 + 1) * p)
    · exact Nat.div_eq_of_lt (by omega)
  rw [sum_congr rfl hterm, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have heq : (Icc 1 (h - 1)).filter (fun i => m < i) = Icc (m + 1) (h - 1) := by
    ext i
    simp only [mem_filter, mem_Icc]
    omega
  rw [heq, Nat.card_Icc]
  have hh : h - 1 + 1 = h := by omega
  rw [hh]
  simp

theorem vSK_above_exact (ν n p : ℕ) (hn : 1 ≤ n) (hpp : p.Prime)
    (hKp : 40 * n < p) (hpB : p ≤ 74 * n) :
    -(vSK ν (40 * n) (3 * n) p : ℝ) =
      2 * ((37 * n : ℕ) : ℝ) - (p : ℝ) - 1 := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hp7 : 7 ≤ p := by omega
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  have hm : 2 * (p / 2) + 1 = p := by
    have hodd := hpp.odd_of_ne_two (by omega)
    rcases hodd with ⟨a, ha⟩
    omega
  have hKval : padicValNat p (40 * n).factorial = 0 := factorial_val_lt hKp
  have hNval : padicValNat p (3 * n).factorial = 0 := factorial_val_lt (by omega)
  have h4val : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
    have := Nat.le_of_dvd (by norm_num : 0 < 4) h
    omega)
  have hs : ∑ i ∈ Icc 1 (37 * n - 1), padicValNat p (2 * i).factorial =
      37 * n - (p / 2 + 1) := by
    rw [sum_congr rfl (fun i hi => factorial_val_small (by
      have hi' := mem_Icc.mp hi
      have hi2 : 2 * i < 2 * p := by omega
      nlinarith : 2 * i < p ^ 2))]
    exact sum_double_div hm (by omega) (by omega)
  have hsZ : ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) =
      ((37 * n - (p / 2 + 1) : ℕ) : ℤ) := by exact_mod_cast hs
  rw [vSK_formula, hshape, hKval, hNval, h4val, hsZ]
  have hceil : p / 2 + 1 ≤ 37 * n := by omega
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast,
    Int.cast_ofNat, Nat.cast_sub hceil, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, mul_zero, add_zero, zero_sub, neg_neg]
  have hmR : 2 * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hm
  linarith

#print axioms scalar_valuation
#print axioms vSK_formula
#print axioms vSK_above_exact
end
end BOuterAboveK
