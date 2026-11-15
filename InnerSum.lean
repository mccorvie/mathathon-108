import TransferStatement

/-!
E429 Codex inner_regularity, lane B. PROOF-DRAFT until parent gate.
The exact E405/E420 model/selected-allocation statements are unchanged.
Actual regularity and inversion are imported from frozen E426; generic uniform
PNT transfer is E421, crediting prior Deicyde. The missing actual localcost
identification is an explicit named hypothesis, never silently discharged.
-/
open Filter Topology Finset
namespace BInnerSum
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.RangeBridgeTarget
open Mathathon.P108.InnerExplicitTarget

theorem primeBound_shape (s n : ℕ) (hn : max 1 s ≤ n) :
    primeBound s (40 * n) (3 * n) = 74 * n := by
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  unfold primeBound
  rw [hshape]
  omega

theorem lower_floor (M n : ℕ) :
    ⌊(1 / (M : ℝ)) * ((40 * n : ℕ) : ℝ)⌋₊ = 40 * n / M := by
  rw [show (1 / (M : ℝ)) * ((40 * n : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) / M by ring,
    Nat.floor_div_natCast, Nat.floor_natCast]

theorem upper_floor (n : ℕ) :
    ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊ = 40 * n / 3 := by
  rw [show (1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) / 3 by ring,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Nat.floor_div_natCast, Nat.floor_natCast]

theorem inner_prime_set (s M n : ℕ) (hM : 0 < M) (hn : max 1 s ≤ n) :
    (range (primeBound s (40 * n) (3 * n) + 1)).filter
        (fun p => p.Prime ∧ 40 * n < p * M ∧ 3 * p ≤ 40 * n) =
      (Ioc ⌊(1 / (M : ℝ)) * ((40 * n : ℕ) : ℝ)⌋₊
        ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  rw [primeBound_shape s n hn, lower_floor, upper_floor]
  ext p
  simp only [mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨hpB, hpp, hKM, h3⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul hM).mpr hKM,
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr (by omega)⟩, hpp⟩
  · rintro ⟨⟨hpM, hp3⟩, hpp⟩
    have hKM := (Nat.div_lt_iff_lt_mul hM).mp hpM
    have h3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hp3
    exact ⟨by omega, hpp, hKM, by omega⟩

theorem inner_sum_eq_weighted (s ν n M : ℕ) (hM : 0 < M) (hn : max 1 s ≤ n) :
    innerPrimeLogContribution s ν (40 * n) (3 * n) M
        (explicitAllocation s ν (40 * n) (3 * n) M) /
        (((40 * n : ℕ) : ℝ) ^ 2) =
      BPrimeTransfer.weightedSum (1 / (M : ℝ)) (1 / 3)
        (fun n p => -(LpSharp s ν (40 * n) (3 * n) M p
          (explicitAllocation s ν (40 * n) (3 * n) M) : ℝ)) n := by
  unfold innerPrimeLogContribution BPrimeTransfer.weightedSum BPrimeTransfer.K
  rw [inner_prime_set s M n hM hn]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

theorem scaled_innerWeight (s ν : ℝ) (n p : ℕ) (hn : 1 ≤ n) :
    (BPrimeTransfer.K n : ℝ) *
        BInnerLimit.innerWeight s ν ((p : ℝ) / BPrimeTransfer.K n) =
      (p : ℝ) * innerR s ν (3 / 40) ((BPrimeTransfer.K n : ℝ) / p) := by
  have hK : (0 : ℝ) < BPrimeTransfer.K n := BPrimeTransfer.K_pos hn
  unfold BInnerLimit.innerWeight
  rw [inv_div, ← mul_assoc, mul_div_cancel₀ _ hK.ne']

theorem inner_limit_of_local (hlocal : InnerExplicitLocalStatement) :
    InnerExplicitLimitStatement := by
  intro s ν M hscope hM ε hε
  have hM0 : 0 < M := by omega
  have hM3 : 3 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  obtain ⟨C, hC, hbound⟩ := hlocal s ν M hscope hM
  let w : ℕ → Unit → ℕ → ℝ := fun n _ p =>
    -(LpSharp s ν (40 * n) (3 * n) M p (explicitAllocation s ν (40 * n) (3 * n) M) : ℝ)
  have hw : ∀ᶠ n : ℕ in atTop, ∀ (i : Unit) (p : ℕ),
      p ∈ Ioc ⌊(1 / (M : ℝ)) * BPrimeTransfer.K n⌋₊
        ⌊(1 / 3 : ℝ) * BPrimeTransfer.K n⌋₊ → p.Prime →
      |w n i p - (BPrimeTransfer.K n : ℝ) *
        BInnerLimit.innerWeight (s : ℝ) (ν : ℝ) ((p : ℝ) / BPrimeTransfer.K n)| ≤ C := by
    filter_upwards [hbound, eventually_ge_atTop (max 1 s)] with n hnLocal hn
    intro i p hp hpp
    change p ∈ Ioc ⌊(1 / (M : ℝ)) * ((40 * n : ℕ) : ℝ)⌋₊
      ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊ at hp
    rw [lower_floor, upper_floor, mem_Ioc] at hp
    have hKM := (Nat.div_lt_iff_lt_mul hM0).mp hp.1
    have h3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hp.2
    have hpB : p ≤ primeBound s (40 * n) (3 * n) := by
      rw [primeBound_shape s n hn]
      omega
    have h := (hnLocal p hpp hpB hKM (by omega)).2
    rw [scaled_innerWeight s ν n p (by omega)]
    exact h
  have hlimit := BPrimeTransfer.uniform_weighted_prime_limit
    (a := 1 / (M : ℝ)) (b := (1 / 3 : ℝ)) (one_div_pos.mpr hMR)
    (one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast (show 3 < M by omega)))
    (BInnerLimit.innerWeight_bounded s ν hM3)
    (BInnerLimit.innerWeight_disc_finite s ν hM3) w hC hw ε hε
  filter_upwards [hlimit, eventually_ge_atTop (max 1 s)] with n hlim hn
  have h := hlim ()
  rw [BInnerLimit.integral_inner_weight s ν hM3] at h
  change |BPrimeTransfer.weightedSum (1 / (M : ℝ)) (1 / 3)
    (fun n p => -(LpSharp s ν (40 * n) (3 * n) M p
      (explicitAllocation s ν (40 * n) (3 * n) M) : ℝ)) n -
      (∫ x in (3 : ℝ)..M, innerR s ν (3 / 40) x / x ^ 3)| ≤ ε at h
  rw [← inner_sum_eq_weighted s ν n M hM0 hn] at h
  exact h

theorem transfer_statement : InnerTransferStatement := inner_limit_of_local

theorem inner_cost_tendsto_of_local (hlocal : InnerExplicitLocalStatement)
    (s ν M : ℕ) (hscope : ParameterScope s ν) (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => innerPrimeLogContribution s ν (40 * n) (3 * n) M
      (explicitAllocation s ν (40 * n) (3 * n) M) /
        (((40 * n : ℕ) : ℝ) ^ 2)) atTop (nhds (innerIntegral s ν M)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [inner_limit_of_local hlocal s ν M hscope hM (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact hn.trans_lt (by linarith)

#print axioms inner_sum_eq_weighted
#print axioms inner_limit_of_local
#print axioms transfer_statement
#print axioms inner_cost_tendsto_of_local
end
end BInnerSum
