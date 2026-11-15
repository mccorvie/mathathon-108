import BridgeTargets

/-!
B3 / E404, Codex, lane B, 2026-11-14. Finite small-prime bounds only.
PROOF-DRAFT until the driver runs the repository declaration gate.

Adapted proof blocks name their source ranges below. Source architecture:
Firsching/Paul-Lez, mo271/Zeta5@be1c0d82, Apache-2.0. The actual Lp and
smallPrimeLogContribution definitions come unchanged from BridgeTargets.
No asymptotic or full-normalizer growth statement is proved in this file.
-/

open Finset

namespace Mathathon.P108.BridgeFinite

noncomputable section

open AperyS.AssemblyTarget Mathathon.P108.BridgeTarget

def smallPrimes (s K N M : ℕ) : Finset ℕ :=
  (range (primeBound s K N + 1)).filter (fun p => p.Prime ∧ p * M ≤ K)

lemma mem_smallPrimes {s K N M p : ℕ} :
    p ∈ smallPrimes s K N M ↔ p ≤ primeBound s K N ∧ p.Prime ∧ p * M ≤ K := by
  simp only [smallPrimes, mem_filter, mem_range, Nat.lt_succ_iff]

theorem Lp_small_eq (s ν K N M p : ℕ) (L : Allocations) (hsmall : p * M ≤ K) :
    Lp s ν K N M p L = Lsmall s ν K N p := by
  unfold Lp
  rw [if_pos hsmall]

theorem neg_Lp_small (s ν K N M p : ℕ) (L : Allocations) (hsmall : p * M ≤ K) :
    -(Lp s ν K N M p L : ℝ) =
      ((s : ℝ) + 1) * (K - N : ℕ) * (Nat.log p (degreeBound s ν K N + 1) : ℝ) +
        (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℝ) := by
  rw [Lp_small_eq s ν K N M p L hsmall]
  simp only [Lsmall, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Nat.cast_add, Nat.cast_one, Int.cast_one, neg_neg]

theorem allocation_independent (s ν K N M : ℕ) (L₁ L₂ : Allocations) :
    smallPrimeLogContribution s ν K N M L₁ = smallPrimeLogContribution s ν K N M L₂ := by
  unfold smallPrimeLogContribution
  apply sum_congr rfl
  intro p hp
  have hsmall := (mem_filter.mp hp).2.2
  rw [Lp_small_eq s ν K N M p L₁ hsmall, Lp_small_eq s ν K N M p L₂ hsmall]

lemma log_nonneg_prime {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_le)

theorem small_term_nonneg (s ν K N M p : ℕ) (L : Allocations)
    (hp : p.Prime) (hsmall : p * M ≤ K) :
    0 ≤ Real.log (p : ℝ) * (-(Lp s ν K N M p L : ℝ)) := by
  rw [neg_Lp_small s ν K N M p L hsmall]
  exact mul_nonneg (log_nonneg_prime hp) (by positivity)

/-- Adapted verbatim in substance from upstream
Apery/Growth/Assembly1.lean:42-49; only local naming changed. -/
lemma log_mul_natLog_le {k Z : ℕ} (hk : 2 ≤ k) (hZ : 1 ≤ Z) :
    (Nat.log k Z : ℝ) * Real.log k ≤ Real.log Z := by
  have h := Nat.pow_log_le_self k (show Z ≠ 0 by omega)
  have h' : ((k ^ Nat.log k Z : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_pow]
  push_cast at h'
  exact Real.log_le_log (pow_pos hk0 _) h'

/-- Prime-only form of upstream Assembly1.lean:51-67. -/
lemma prime_log_natLog_le {p D : ℕ} (hp : p.Prime) (hD : 1 ≤ D) :
    Real.log (p : ℝ) * (Nat.log p D : ℝ) ≤
      Real.log (p : ℝ) + if p * p ≤ D then Real.log (D : ℝ) else 0 := by
  by_cases hsq : p * p ≤ D
  · rw [if_pos hsq]
    have h := log_mul_natLog_le hp.two_le hD
    have hlog := log_nonneg_prime hp
    nlinarith
  · rw [if_neg hsq]
    have hlt : Nat.log p D ≤ 1 := by
      have : D < p ^ 2 := by rw [sq]; omega
      exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) this)
    have hltR : (Nat.log p D : ℝ) ≤ 1 := by exact_mod_cast hlt
    nlinarith [log_nonneg_prime hp]

/-- Symbolic replacement for the fixed factorial24 subargument in
upstream Assembly1.lean:101-128. -/
lemma prime_log_padicVal_le {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    Real.log (p : ℝ) * (padicValNat p f : ℝ) ≤
      if p ≤ f then Real.log (f : ℝ) else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hpf : p ≤ f
  · rw [if_pos hpf]
    have hdvd : p ^ padicValNat p f ∣ f := pow_padicValNat_dvd
    have hpow : p ^ padicValNat p f ≤ f := Nat.le_of_dvd (by omega) hdvd
    have hpowR : ((p ^ padicValNat p f : ℕ) : ℝ) ≤ f := by exact_mod_cast hpow
    push_cast at hpowR
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlog := Real.log_le_log (pow_pos hpR _) hpowR
    rw [Real.log_pow] at hlog
    nlinarith
  · rw [if_neg hpf]
    have hv : padicValNat p f = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by omega : 0 < f) h
      omega)
    simp [hv]

lemma sum_log_le_theta (P : Finset ℕ) (T : ℕ)
    (hP : ∀ p ∈ P, p ≤ T ∧ p.Prime) :
    ∑ p ∈ P, Real.log (p : ℝ) ≤ Chebyshev.theta (T : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr (hP p hp)
  · intro p hp _
    exact log_nonneg_prime (Nat.mem_primesLE.mp hp).2

/-- General finite-set form of upstream Assembly1.lean:140-157. -/
lemma square_error_sum_le (P : Finset ℕ) (D : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hD : 1 ≤ D) :
    ∑ p ∈ P, (if p * p ≤ D then Real.log (D : ℝ) else 0) ≤
      (Real.sqrt (D : ℝ) + 1) * Real.log (D : ℝ) := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hlog : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  have hsub : P.filter (fun p => p * p ≤ D) ⊆ Icc 1 (Nat.sqrt D) := by
    intro p hp
    exact mem_Icc.mpr ⟨hP p (mem_filter.mp hp).1, Nat.le_sqrt.mpr (mem_filter.mp hp).2⟩
  have hc : (P.filter (fun p => p * p ≤ D)).card ≤ Nat.sqrt D := by
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hcR : ((P.filter (fun p => p * p ≤ D)).card : ℝ) ≤ Nat.sqrt D := by exact_mod_cast hc
  have hsqrt : (Nat.sqrt D : ℝ) ≤ Real.sqrt (D : ℝ) := Real.nat_sqrt_le_real_sqrt
  exact mul_le_mul_of_nonneg_right (by linarith) hlog

/-- Symbolic analogue of the bounded exceptional-prime sum in
upstream Assembly1.lean:158-168. -/
lemma finite_factorial_error_le (P : Finset ℕ) (f : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hf : 1 ≤ f) :
    ∑ p ∈ P, (if p ≤ f then Real.log (f : ℝ) else 0) ≤
      (f : ℝ) * Real.log (f : ℝ) := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hsub : P.filter (fun p => p ≤ f) ⊆ Icc 1 f := by
    intro p hp
    exact mem_Icc.mpr ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  have hc : (P.filter (fun p => p ≤ f)).card ≤ f := by
    have := card_le_card hsub
    simpa using this
  have hcR : ((P.filter (fun p => p ≤ f)).card : ℝ) ≤ f := by exact_mod_cast hc
  exact mul_le_mul_of_nonneg_right hcR (Real.log_nonneg (by exact_mod_cast hf))

/-- The exact finite upper-bound proposition approved as B2/E402. -/
theorem finite_small_prime_statement : FiniteSmallPrimeStatement := by
  intro s ν K N M L _hs _hNK hM
  let P := smallPrimes s K N M
  let D := degreeBound s ν K N + 1
  let f := (s - 1).factorial
  let h : ℝ := (K - N : ℕ)
  let A : ℝ := ((s : ℝ) + 1) * h
  have hP : ∀ p ∈ P, p.Prime ∧ p * M ≤ K := by
    intro p hp
    exact (mem_smallPrimes.mp hp).2
  have hPpos : ∀ p ∈ P, 1 ≤ p := fun p hp => (hP p hp).1.one_le
  have hθ : ∑ p ∈ P, Real.log (p : ℝ) ≤ Chebyshev.theta ((K / M : ℕ) : ℝ) :=
    sum_log_le_theta P (K / M) (fun p hp =>
      ⟨(Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr (hP p hp).2, (hP p hp).1⟩)
  have hsq := square_error_sum_le P D hPpos (by dsimp [D]; omega)
  have hf := finite_factorial_error_le P f hPpos (Nat.factorial_pos _)
  have hterm : ∀ p ∈ P,
      Real.log (p : ℝ) * (-(Lp s ν K N M p L : ℝ)) ≤
        A * (Real.log (p : ℝ) + if p * p ≤ D then Real.log (D : ℝ) else 0) +
          h * (if p ≤ f then Real.log (f : ℝ) else 0) := by
    intro p hp
    have h1 := prime_log_natLog_le (hP p hp).1 (show 1 ≤ D by dsimp [D]; omega)
    have h2 := prime_log_padicVal_le (hP p hp).1 (show 1 ≤ f from Nat.factorial_pos _)
    rw [neg_Lp_small s ν K N M p L (hP p hp).2]
    change Real.log (p : ℝ) * (A * (Nat.log p D : ℝ) + h * (padicValNat p f : ℝ)) ≤ _
    calc
      _ = A * (Real.log (p : ℝ) * (Nat.log p D : ℝ)) +
          h * (Real.log (p : ℝ) * (padicValNat p f : ℝ)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (by dsimp [A, h]; positivity))
        (mul_le_mul_of_nonneg_left h2 (by dsimp [h]; positivity))
  change (∑ p ∈ P, Real.log (p : ℝ) * (-(Lp s ν K N M p L : ℝ))) ≤ _
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib]
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hθ hsq) (show 0 ≤ A by dsimp [A, h]; positivity))
    (mul_le_mul_of_nonneg_left hf (show 0 ≤ h by dsimp [h]; positivity))
  dsimp [smallPrimeFiniteEnvelope]
  dsimp [A, h, D, f] at hsum
  convert hsum using 1 <;> ring

/-- Universal finite lower bound: every prime counted by theta lies below
the range cutoff, the actual support, and the logarithm argument. -/
theorem finite_small_prime_lower (s ν K N M : ℕ) (L : Allocations) (hM : 1 ≤ M) :
    ((s : ℝ) + 1) * (K - N : ℕ) *
      Chebyshev.theta ((min (K / M) (min (primeBound s K N)
        (degreeBound s ν K N + 1)) : ℕ) : ℝ) ≤
      smallPrimeLogContribution s ν K N M L := by
  let T := min (K / M) (min (primeBound s K N) (degreeBound s ν K N + 1))
  let P := smallPrimes s K N M
  let A : ℝ := ((s : ℝ) + 1) * (K - N : ℕ)
  have hsub : Nat.primesLE T ⊆ P := by
    intro p hp
    obtain ⟨hpT, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpKM : p ≤ K / M := hpT.trans (min_le_left _ _)
    have hpB : p ≤ primeBound s K N := hpT.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact mem_smallPrimes.mpr ⟨hpB, hpp,
      (Nat.le_div_iff_mul_le (by omega : 0 < M)).mp hpKM⟩
  have hterm : ∀ p ∈ Nat.primesLE T,
      A * Real.log (p : ℝ) ≤ Real.log (p : ℝ) * (-(Lp s ν K N M p L : ℝ)) := by
    intro p hp
    obtain ⟨hpT, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpD : p ≤ degreeBound s ν K N + 1 :=
      hpT.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hlog : (1 : ℝ) ≤ (Nat.log p (degreeBound s ν K N + 1) : ℝ) := by
      exact_mod_cast (Nat.log_pos hpp.one_lt hpD)
    rw [neg_Lp_small s ν K N M p L (mem_smallPrimes.mp (hsub hp)).2.2]
    have hlp := log_nonneg_prime hpp
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hfac : 0 ≤ (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℝ) := by positivity
    change A * Real.log (p : ℝ) ≤
      Real.log (p : ℝ) * (A * (Nat.log p (degreeBound s ν K N + 1) : ℝ) +
        (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℝ))
    nlinarith [mul_le_mul_of_nonneg_left hlog hA, mul_nonneg hlp hfac]
  change A * Chebyshev.theta (T : ℝ) ≤ _
  rw [Chebyshev.theta_eq_sum_primesLE_log, mul_sum]
  refine (sum_le_sum hterm).trans ?_
  change (∑ p ∈ Nat.primesLE T, _) ≤ ∑ p ∈ P, _
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  have hp' := mem_smallPrimes.mp hp
  exact small_term_nonneg s ν K N M p L hp'.2.1 hp'.2.2

theorem finite_small_prime_lower_full (s ν K N M : ℕ) (L : Allocations) (hM : 1 ≤ M)
    (hsupport : K / M ≤ primeBound s K N)
    (hdegree : K / M ≤ degreeBound s ν K N + 1) :
    ((s : ℝ) + 1) * (K - N : ℕ) * Chebyshev.theta ((K / M : ℕ) : ℝ) ≤
      smallPrimeLogContribution s ν K N M L := by
  have h := finite_small_prime_lower s ν K N M L hM
  rw [min_eq_left (le_min hsupport hdegree)] at h
  exact h

#print axioms Lp_small_eq
#print axioms neg_Lp_small
#print axioms allocation_independent
#print axioms small_term_nonneg
#print axioms finite_small_prime_statement
#print axioms finite_small_prime_lower
#print axioms finite_small_prime_lower_full

end
end Mathathon.P108.BridgeFinite
