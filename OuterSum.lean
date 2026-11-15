import Regularity
import FinalLocal

/-!
E425, native Codex outer_sum, lane B, 2026-11-14.
PROOF-DRAFT until the parent repository gate. The actual E405 outer definitions
and statements are unchanged. This is the uniform weighted-prime transfer from
E421, combined with the actual root Tout regularity from E423 and local E418.
The generic PNT/Riemann machinery credits PRIOR Deicyde in its source headers.
No normalizer, inner-range, actual determinant-valuation or irrationality claim.
-/

open Filter Topology Finset
namespace BOuterSum
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.RangeBridgeTarget

theorem primeBound_shape (s n : ℕ) (hn : max 1 s ≤ n) :
    primeBound s (40 * n) (3 * n) = 74 * n := by
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  unfold primeBound
  rw [hshape]
  omega

theorem lower_floor (n : ℕ) :
    ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊ = 40 * n / 3 := by
  rw [show (1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) / 3 by ring,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Nat.floor_div_natCast, Nat.floor_natCast]

theorem upper_floor (n : ℕ) :
    ⌊(37 / 20 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊ = 74 * n := by
  have h : (37 / 20 : ℝ) * ((40 * n : ℕ) : ℝ) = ((74 * n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h, Nat.floor_natCast]

theorem outer_prime_set (s n : ℕ) (hn : max 1 s ≤ n) :
    (range (primeBound s (40 * n) (3 * n) + 1)).filter
        (fun p => p.Prime ∧ 40 * n < 3 * p) =
      (Ioc ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊
        ⌊(37 / 20 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  rw [primeBound_shape s n hn, lower_floor, upper_floor]
  ext p
  simp only [mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨hpB, hpp, h3⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mpr (by omega), by omega⟩, hpp⟩
  · rintro ⟨⟨hp3, hpB⟩, hpp⟩
    have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hp3
    exact ⟨by omega, hpp, by omega⟩

theorem outer_sum_eq_weighted (s ν n M : ℕ) (L : Allocations) (hn : max 1 s ≤ n) :
    outerPrimeLogContribution s ν (40 * n) (3 * n) M L /
        (((40 * n : ℕ) : ℝ) ^ 2) =
      BPrimeTransfer.weightedSum (1 / 3) (37 / 20)
        (fun n p => -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)) n := by
  unfold outerPrimeLogContribution BPrimeTransfer.weightedSum BPrimeTransfer.K
  rw [outer_prime_set s n hn]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

abbrev Parameters := {M : ℕ // 3 ≤ M} × Allocations

theorem outer_limit_of_local (hlocal : OuterLocalStatement) : OuterLimitStatement := by
  intro s ν hscope ε hε
  obtain ⟨C, hC, hbound⟩ := hlocal s ν hscope
  let w : ℕ → Parameters → ℕ → ℝ := fun n i p =>
    -(LpSharp s ν (40 * n) (3 * n) i.1.val p i.2 : ℝ)
  have hw : ∀ᶠ n : ℕ in atTop, ∀ (i : Parameters) (p : ℕ),
      p ∈ Ioc ⌊(1 / 3 : ℝ) * BPrimeTransfer.K n⌋₊
        ⌊(37 / 20 : ℝ) * BPrimeTransfer.K n⌋₊ → p.Prime →
      |w n i p - (BPrimeTransfer.K n : ℝ) *
        Tout (s : ℝ) (ν : ℝ) (3 / 40) ((p : ℝ) / BPrimeTransfer.K n)| ≤ C := by
    filter_upwards [eventually_ge_atTop (max 1 s)] with n hn
    intro i p hp hpp
    change p ∈ Ioc ⌊(1 / 3 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊
      ⌊(37 / 20 : ℝ) * ((40 * n : ℕ) : ℝ)⌋₊ at hp
    rw [lower_floor, upper_floor, mem_Ioc] at hp
    have hpB : p ≤ primeBound s (40 * n) (3 * n) := by
      rw [primeBound_shape s n hn]
      exact hp.2
    have h3 : 40 * n < 3 * p := by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hp.1
      omega
    exact hbound n hn i.1.val i.1.property i.2 p hpp hpB h3
  have hlimit := BPrimeTransfer.uniform_weighted_prime_limit
    (a := (1 / 3 : ℝ)) (b := (37 / 20 : ℝ))
    (by norm_num) (by norm_num) (BOuterLimit.Tout_bounded s ν)
    (BOuterLimit.Tout_finite_discontinuities s ν) w hC hw ε hε
  filter_upwards [hlimit, eventually_ge_atTop (max 1 s)] with n hlim hn
  intro M hM L
  have h := hlim (⟨M, hM⟩, L)
  have hI : (∫ y in (1 / 3 : ℝ)..(37 / 20 : ℝ), Tout (s : ℝ) (ν : ℝ) (3 / 40) y) =
      Iout (s : ℝ) (ν : ℝ) (3 / 40) := by norm_num [Iout]
  rw [hI] at h
  change |BPrimeTransfer.weightedSum (1 / 3) (37 / 20)
    (fun n p => -(LpSharp s ν (40 * n) (3 * n) M p L : ℝ)) n -
      Iout (s : ℝ) (ν : ℝ) (3 / 40)| ≤ ε at h
  rw [← outer_sum_eq_weighted s ν n M L hn] at h
  rw [abs_le] at h
  constructor <;> linarith

/-- PROOF-DRAFT: the literal actual outer limit target, with no local premise. -/
theorem outer_limit_statement : OuterLimitStatement :=
  outer_limit_of_local BOuterBridge.outer_local_statement

/-- PROOF-DRAFT: the exact approved E405 outer bridge, both halves. -/
theorem outer_bridge_statement : OuterBridgeStatement :=
  ⟨BOuterBridge.outer_local_statement, outer_limit_statement⟩

/-- PROOF-DRAFT: allocations may vary with n in this direct limit corollary. -/
theorem outer_cost_tendsto (s ν M : ℕ) (hscope : ParameterScope s ν) (hM : 3 ≤ M)
    (L : ℕ → Allocations) :
    Tendsto (fun n : ℕ => outerPrimeLogContribution s ν (40 * n) (3 * n) M (L n) /
      (((40 * n : ℕ) : ℝ) ^ 2)) atTop (nhds (Iout s ν (3 / 40))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [outer_limit_statement s ν hscope (ε / 2) (half_pos hε)] with n hn
  obtain ⟨h1, h2⟩ := hn M hM (L n)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

#print axioms outer_sum_eq_weighted
#print axioms outer_limit_of_local
#print axioms outer_limit_statement
#print axioms outer_bridge_statement
#print axioms outer_cost_tendsto
end
end BOuterSum
