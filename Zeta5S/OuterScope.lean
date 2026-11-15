import Zeta5S.OuterEntryMain

/-!
L7 stage 3 scope bridge, Codex lane L, Sat Nov 14 2026 (event work).
The rank expression is adapted from Firsching/Paul-Lez mo271/Zeta5@be1c0d82,
Apery/Arith/OuterFrame.lean:95-212 and OuterEntryMain.lean:483-509, Apache-2.0.
The two parameter restrictions are those of criterion5/derivation.md section 8.
No analytic interpretation of the general functional is asserted here.
-/

namespace AperyS

/-- First moment index not known integral from the strict moment inequality. -/
def momentCutS (s p : ℕ) : ℕ := ((s - 1) / 2) * (p - 1) - 1

theorem momentCutS_spec (s p : ℕ) (hodd : Odd s) (hs : 3 ≤ s) (hp : 3 ≤ p) :
    1 ≤ momentCutS s p ∧ 2 * momentCutS s p + 2 = (s - 1) * (p - 1) := by
  obtain ⟨a, ha⟩ := hodd
  have hr : 2 * ((s - 1) / 2) = s - 1 := by omega
  have hr1 : 1 ≤ (s - 1) / 2 := by omega
  have hp1 : 2 ≤ p - 1 := by omega
  have hprod : 2 ≤ ((s - 1) / 2) * (p - 1) := by nlinarith
  have hmul : 2 * (((s - 1) / 2) * (p - 1)) = (s - 1) * (p - 1) := by
    calc
      2 * (((s - 1) / 2) * (p - 1)) = (2 * ((s - 1) / 2)) * (p - 1) := by ring
      _ = (s - 1) * (p - 1) := congrArg (fun a : ℕ => a * (p - 1)) hr
  unfold momentCutS
  constructor <;> omega

/-- The nested natural subtractions in the formal outer frame are the
clamped paper rank bound, once `h=K-N` and `T=q-1`. -/
theorem outer_rank_loss_eq (ν K N q : ℕ) (hν : 2 ≤ ν) (hNK : N ≤ K) (hq : 1 ≤ q) :
    (K - N) - (((q - 1 + K - ν * N) - ((K - N) - 1))) =
      min (K - N) (K + (ν - 2) * N - q) := by
  have hmul : ν * N = (ν - 2) * N + 2 * N := by
    calc
      ν * N = ((ν - 2) + 2) * N := by congr 1; omega
      _ = (ν - 2) * N + 2 * N := Nat.add_mul _ _ _
  omega

/-- Section 8(H1), including its safe boundary: `N/K≤1/6` supplies
`2N<p` in the outer range `K<3p`. -/
theorem outer_removed_poles_lt (N K p : ℕ) (hα : 6 * N ≤ K) (houter : K < 3 * p) :
    2 * N < p := by omega

/-- Section 8(H2) is used to discard the moment correction above K.
This finite statement is separate from the outer bound that retains the correction. -/
theorem outer_rank_zero_above_K (ν K N r p : ℕ)
    (hbudget : K + (ν - 2) * N ≤ r * K) (hp : K < p) :
    K + (ν - 2) * N - r * (p - 1) = 0 := by
  have hK : K ≤ p - 1 := by omega
  have hmul := Nat.mul_le_mul_left r hK
  omega

/-- The symbolic outer theorem with its moment threshold instantiated.
This is the raw rank-loss bound of the upstream Lean proof, not E13's
sharpened minimum with the zero count. -/
theorem outer_boundS_moment {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hodd : Odd s) (hs : 3 ≤ s) (hps : s ≤ p) (hν : 1 ≤ ν)
    (hp7 : 7 ≤ p) (hK3 : K < 3 * p) (hK : 2 * K < p ^ 2) (hpN : N < p) :
    GV p (ΔS s ν K N (K - N))
      (2 * ∑ c, ∑ i ∈ Finset.range (LoC hm N K c), wO hm s ν N K c i -
        (((K - N) - ((momentCutS s p + K - ν * N) - ((K - N) - 1)) : ℕ) : ℚ)) := by
  have hcut := momentCutS_spec s p hodd hs (by omega)
  exact outer_boundS hm s ν N K hodd (by omega) hps hν (momentCutS s p)
    (le_of_eq hcut.2) hcut.1 hp7 hK3 hK hpN

/-- Explicit clamped-rank form of the upstream raw outer estimate. -/
theorem outer_boundS_clamped {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hodd : Odd s) (hs : 3 ≤ s) (hps : s ≤ p) (hν : 2 ≤ ν) (hNK : N ≤ K)
    (hp7 : 7 ≤ p) (hK3 : K < 3 * p) (hK : 2 * K < p ^ 2) (hpN : N < p) :
    GV p (ΔS s ν K N (K - N))
      (2 * ∑ c, ∑ i ∈ Finset.range (LoC hm N K c), wO hm s ν N K c i -
        ((min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1)) : ℕ) : ℚ)) := by
  have hcut := momentCutS_spec s p hodd hs (by omega)
  have hq : 1 ≤ ((s - 1) / 2) * (p - 1) := by
    unfold momentCutS at hcut
    omega
  have h := outer_boundS_moment hm s ν N K hodd hs hps (by omega) hp7 hK3 hK hpN
  simpa only [momentCutS, outer_rank_loss_eq ν K N _ hν hNK hq] using h

/-- General-s version of the section 8 claim for p>K, with its finite
rank-budget hypothesis explicit. This concerns Delta, not the scalar-normalized F. -/
theorem determinant_integral_above_K {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hodd : Odd s) (hs : 3 ≤ s) (hps : s ≤ p) (hν : 2 ≤ ν) (hNK : N ≤ K)
    (hp7 : 7 ≤ p) (hKp : K < p)
    (hbudget : K + (ν - 2) * N ≤ ((s - 1) / 2) * K) :
    GV p (ΔS s ν K N (K - N)) 0 := by
  have hnb : ∀ c, nbC hm N K c = 0 := by
    intro c
    unfold nbC
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjc, hpj⟩ := Finset.mem_filter.mp hj
    have hjK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hjc).1).2
    omega
  have hzero : LoC hm N K 0 = 0 := by
    unfold LoC
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjT, hjc⟩ := Finset.mem_filter.mp hj
    have hjI := Finset.mem_Icc.mp hjT
    have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hjc
    have hpj : p ≤ j := Nat.le_of_dvd (by omega) hd
    omega
  have hw : ∑ c, ∑ i ∈ Finset.range (LoC hm N K c), wO hm s ν N K c i = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c = 0
    · subst c; simp [hzero]
    · apply Finset.sum_eq_zero
      intro i _
      simp [wO, hc, hnb]
  have h := outer_boundS_clamped hm s ν N K hodd hs hps hν hNK hp7
    (by omega) (by nlinarith) (by omega)
  rw [hw, outer_rank_zero_above_K ν K N ((s - 1) / 2) p hbudget hKp] at h
  simpa using h

end AperyS
