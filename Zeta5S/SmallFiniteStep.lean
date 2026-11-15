import Zeta5S.OuterFiniteStep

/-! L10/E309: exact fallback step, Codex lane L, 2026-11-14.
Status: PROOF-DRAFT until the repository gate records these declarations. -/
namespace AperyS.AssemblyTarget

lemma degreeBound_sstep (s ν K N : ℕ) :
    degreeBound (s + 2) ν K N = degreeBound s ν K N + 2 := by
  unfold degreeBound
  omega

theorem factorialVal_sstep (s p : ℕ) [Fact p.Prime] (hs : 1 ≤ s) :
    padicValNat p (s + 2 - 1).factorial = padicValNat p (s - 1).factorial +
      padicValNat p s + padicValNat p (s + 1) := by
  have h1 : s + 2 - 1 = s + 1 := by omega
  have h2 : s = (s - 1) + 1 := by omega
  rw [h1, Nat.factorial_succ,
    padicValNat.mul (by omega) (Nat.factorial_ne_zero s)]
  conv_lhs => arg 2; rw [h2, Nat.factorial_succ]
  rw [padicValNat.mul (by omega) (Nat.factorial_ne_zero (s - 1))]
  rw [← h2]
  omega

/-- Exact integer identity: the logarithmic cutoff may jump, even at fixed p. -/
theorem Lsmall_sstep (s ν K N p : ℕ) [Fact p.Prime] (hs : 1 ≤ s) :
    Lsmall (s + 2) ν K N p - Lsmall s ν K N p =
      -(K - N : ℕ) *
        (2 * (Nat.log p (degreeBound s ν K N + 1) : ℤ) +
          ((s : ℤ) + 3) * ((Nat.log p (degreeBound (s + 2) ν K N + 1) : ℤ) -
            Nat.log p (degreeBound s ν K N + 1)) +
          padicValNat p s + padicValNat p (s + 1)) := by
  unfold Lsmall
  rw [factorialVal_sstep s p hs]
  push_cast
  ring

theorem Lsmall_sstep_same_log (s ν K N p : ℕ) [Fact p.Prime] (hs : 1 ≤ s)
    (hlog : Nat.log p (degreeBound (s + 2) ν K N + 1) =
      Nat.log p (degreeBound s ν K N + 1)) :
    Lsmall (s + 2) ν K N p - Lsmall s ν K N p =
      -(K - N : ℕ) * (2 * (Nat.log p (degreeBound s ν K N + 1) : ℤ) +
        padicValNat p s + padicValNat p (s + 1)) := by
  rw [Lsmall_sstep s ν K N p hs, hlog, sub_self, mul_zero, add_zero]

theorem Lp_small_sstep (s ν K N M p : ℕ) (L : Allocations) [Fact p.Prime]
    (hs : 1 ≤ s) (hcut : p * M ≤ K) :
    Lp (s + 2) ν K N M p L - Lp s ν K N M p L =
      Lsmall (s + 2) ν K N p - Lsmall s ν K N p := by
  simp only [Lp, if_pos hcut]

/-- More generally, either small selection or a failed range flag selects the fallback. -/
def UsesFallback (s ν K N M p : ℕ) (L : Allocations) : Prop :=
  p * M ≤ K ∨ (K < p * M ∧
    ((3 * p ≤ K ∧ ¬ InnerOK s ν K N p L) ∨
      (K < 3 * p ∧ ¬ OuterOK s K N p)))

lemma Lp_eq_Lsmall_of_fallback (s ν K N M p : ℕ) (L : Allocations)
    (h : UsesFallback s ν K N M p L) : Lp s ν K N M p L = Lsmall s ν K N p := by
  rcases h with hc | ⟨hc, ⟨hr, hf⟩ | ⟨hr, hf⟩⟩
  · simp [Lp, hc]
  · simp [Lp, Nat.not_le.mpr hc, hr, hf]
  · simp [Lp, Nat.not_le.mpr hc, Nat.not_le.mpr hr, hf]

theorem Lp_fallback_sstep (s ν K N M p : ℕ) (L : Allocations)
    (h : UsesFallback s ν K N M p L) (h' : UsesFallback (s + 2) ν K N M p L) :
    Lp (s + 2) ν K N M p L - Lp s ν K N M p L =
      Lsmall (s + 2) ν K N p - Lsmall s ν K N p := by
  rw [Lp_eq_Lsmall_of_fallback _ _ _ _ _ _ _ h, Lp_eq_Lsmall_of_fallback _ _ _ _ _ _ _ h']

/-- Original upstream allocation: two finite anchors for the step, with no prime-sum limit. -/
theorem inner13_step_anchor :
    Lp 7 6 40 3 400 13 upstreamAlloc - Lp 5 6 40 3 400 13 upstreamAlloc = -71 := by
  rw [exponent7_inner13, exponent5_inner13]
  norm_num

theorem outer17_step_anchor :
    Lp 7 6 40 3 400 17 upstreamAlloc - Lp 5 6 40 3 400 17 upstreamAlloc = -25 := by
  rw [exponent7_outer17, exponent5_outer17]
  norm_num

end AperyS.AssemblyTarget
