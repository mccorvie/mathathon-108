import Scalar

/-!
E418 q0 branch, Codex outer_above_k helper,2026-11-14.
PROOF-DRAFT until driver gate; no human status upgrade.
Actual sharp/raw definitions and actual root Tout are imported unchanged.
Source arithmetic patterns: Firsching/Paul-Lez mo271/Zeta5@be1c0d82,
Apery/Legendre.lean:15-61 and laneL OuterScope.lean:86-132.
-/
open Finset
namespace BOuterAboveK
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.RangeBridgeTarget

theorem WOsharp_above_K (s ν K N p : ℕ) (hpp : p.Prime)
    (hm : 2 * (p / 2) + 1 = p) (hKp : K < p)
    (hbudget : K + (ν - 2) * N ≤ ((s - 1) / 2) * K) :
    WOsharp s ν K N p = 0 := by
  classical
  letI : Fact p.Prime := ⟨hpp⟩
  have hnb : ∀ c, nbC hm N K c = 0 := by
    intro c
    unfold nbC
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjc, hpj⟩ := mem_filter.mp hj
    have hjK := (mem_Icc.mp (mem_filter.mp hjc).1).2
    omega
  have hzero : LoC hm N K 0 = 0 := by
    unfold LoC
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjT, hjc⟩ := mem_filter.mp hj
    have hjI := mem_Icc.mp hjT
    have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hjc
    have hpj : p ≤ j := Nat.le_of_dvd (by omega) hd
    omega
  have hw : ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i = 0 := by
    apply sum_eq_zero
    intro c _
    by_cases hc : c = 0
    · subst c; simp [hzero]
    · apply sum_eq_zero
      intro i _
      simp [wO, hc, hnb]
  have hr : rawRank s ν K N p = 0 := by
    unfold rawRank
    rw [outer_rank_zero_above_K ν K N ((s - 1) / 2) p hbudget hKp]
    simp
  simp only [WOsharp, dif_pos hpp, dif_pos hm, hw, hr, mul_zero,
    Nat.zero_min, Nat.cast_zero, sub_self]

theorem shape_rank_budget (s ν n : ℕ) (hs : 5 ≤ s) (hν : ν ≤ 10) :
    40 * n + (ν - 2) * (3 * n) ≤ ((s - 1) / 2) * (40 * n) := by
  have hν' : ν - 2 ≤ 8 := by omega
  have hr : 2 ≤ (s - 1) / 2 := by omega
  have hνn := Nat.mul_le_mul_right (3 * n) hν'
  have hrn := Nat.mul_le_mul_right (40 * n) hr
  nlinarith

theorem LpSharp_above_K (s ν n M p : ℕ) (L : Allocations)
    (hs : 5 ≤ s) (hν : ν ≤ 10) (hn : max 1 s ≤ n) (hM : 3 ≤ M)
    (hpp : p.Prime) (hKp : 40 * n < p) :
    LpSharp s ν (40 * n) (3 * n) M p L = vSK ν (40 * n) (3 * n) p := by
  have hm : 2 * (p / 2) + 1 = p := by
    rcases hpp.odd_of_ne_two (by omega) with ⟨a, ha⟩
    omega
  have hflag : OuterOK s (40 * n) (3 * n) p := by
    refine ⟨hm, by omega, by omega, by omega, ?_, by omega⟩
    have hp0 : 0 < p := hpp.pos
    nlinarith
  have hsmall : ¬p * M ≤ 40 * n := by
    have hpM := Nat.mul_le_mul_left p hM
    omega
  have hinner : ¬3 * p ≤ 40 * n := by omega
  have hw := WOsharp_above_K s ν (40 * n) (3 * n) p hpp hm hKp
    (shape_rank_budget s ν n hs hν)
  simp [LpSharp, hsmall, hinner, hflag, hw]

theorem Tout_above_one (s ν y : ℝ) (hy : 1 < y) (hyB : y ≤ 37 / 20) :
    Tout s ν (3 / 40) y = 37 / 20 - y := by
  have hfl := fl0 y hy
  have hnot : ¬(1 / 3 < y ∧ y ≤ 1) := by intro h; linarith [h.2]
  unfold Tout gOuter legendreTerm
  rw [if_neg hnot, hfl]
  simp only [Nat.cast_zero, mul_zero, add_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  norm_num
  repeat first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
  ring

theorem outer_local_above_K_exact (s ν n M p : ℕ) (L : Allocations)
    (hscope : ParameterScope s ν) (hn : max 1 s ≤ n) (hM : 3 ≤ M)
    (hpp : p.Prime) (hpB : p ≤ primeBound s (40 * n) (3 * n))
    (hKp : 40 * n < p) :
    -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ) -
      ((40 * n : ℕ) : ℝ) * Tout (s : ℝ) (ν : ℝ) (3 / 40)
        ((p : ℝ) / ((40 * n : ℕ) : ℝ)) = -1 := by
  have hn1 : 1 ≤ n := by omega
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  have hpBound : primeBound s (40 * n) (3 * n) = 74 * n := by
    unfold primeBound
    rw [hshape]
    omega
  rw [hpBound] at hpB
  have hK0 : (0 : ℝ) < (40 * n : ℕ) := by positivity
  have hy : (1 : ℝ) < (p : ℝ) / ((40 * n : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hK0]
    simp only [one_mul]
    exact_mod_cast hKp
  have hyB : (p : ℝ) / ((40 * n : ℕ) : ℝ) ≤ 37 / 20 := by
    rw [div_le_iff₀ hK0]
    have h : (20 : ℝ) * p ≤ 37 * (40 * n : ℕ) := by
      exact_mod_cast (show 20 * p ≤ 37 * (40 * n) by omega)
    linarith
  rw [LpSharp_above_K s ν n M p L hscope.2.1 hscope.2.2.2.2 hn hM hpp hKp,
    vSK_above_exact ν n p hn1 hpp hKp hpB,
    Tout_above_one (s : ℝ) (ν : ℝ) _ hy hyB]
  field_simp
  push_cast
  ring

theorem outer_local_above_K_bound (s ν n M p : ℕ) (L : Allocations)
    (hscope : ParameterScope s ν) (hn : max 1 s ≤ n) (hM : 3 ≤ M)
    (hpp : p.Prime) (hpB : p ≤ primeBound s (40 * n) (3 * n))
    (hKp : 40 * n < p) :
    |-(LpSharp s ν (40 * n) (3 * n) M p L : ℝ) -
      ((40 * n : ℕ) : ℝ) * Tout (s : ℝ) (ν : ℝ) (3 / 40)
        ((p : ℝ) / ((40 * n : ℕ) : ℝ))| ≤ 1 := by
  rw [outer_local_above_K_exact s ν n M p L hscope hn hM hpp hpB hKp]
  norm_num

#print axioms outer_local_above_K_exact
#print axioms outer_local_above_K_bound

end
end BOuterAboveK
