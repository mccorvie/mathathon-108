import OuterTargets
import BridgeTargets

/-!
B7/E408, Codex lane B, 2026-11-14. PROOF-DRAFT pending driver gate.
Finite mechanical identities only, with actual E405 and B3 definitions.
No E405 conjectural outer/inner target is assumed in these proofs.

The log-product argument adapts Firsching/Paul-Lez mo271/Zeta5@be1c0d82,
Apery/Growth/Assembly1.lean:15-30, Apache-2.0. Source copies and licenses
are recorded in SOURCE_MANIFEST.json and NOTICE. No existing probe is edited.
-/

open Finset

namespace Mathathon.P108.SharpSplit

noncomputable section

open AperyS.AssemblyTarget Mathathon.P108.BridgeTarget Mathathon.P108.RangeBridgeTarget

/-- Derived range sum of the actual sharp exponent, using exactly the B3 cutoff. -/
def smallPrimeLogContributionSharp (s ν K N M : ℕ) (L : Allocations) : ℝ :=
  ∑ p ∈ (range (primeBound s K N + 1)).filter (fun p => p.Prime ∧ p * M ≤ K),
    Real.log (p : ℝ) * (-(LpSharp s ν K N M p L : ℝ))

theorem LpSharp_eq_raw_of_small (s ν K N M p : ℕ) (L : Allocations)
    (hsmall : p * M ≤ K) :
    LpSharp s ν K N M p L = Lp s ν K N M p L := by
  unfold LpSharp Lp
  rw [if_pos hsmall, if_pos hsmall]

theorem small_prime_sharp_eq_raw (s ν K N M : ℕ) (L : Allocations) :
    smallPrimeLogContributionSharp s ν K N M L = smallPrimeLogContribution s ν K N M L := by
  unfold smallPrimeLogContributionSharp smallPrimeLogContribution
  apply sum_congr rfl
  intro p hp
  rw [LpSharp_eq_raw_of_small s ν K N M p L (mem_filter.mp hp).2.2]

/-- Source architecture: Apery/Growth/Assembly1.lean:15-30; the prime support
and exponent are the actual sharp definitions, and no integrality premise enters. -/
theorem log_normalizerSharp (s ν K N M : ℕ) (L : Allocations) :
    Real.log (normalizerSharp s ν K N M L : ℝ) =
      ∑ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (-(LpSharp s ν K N M p L : ℝ)) := by
  unfold normalizerSharp
  push_cast
  rw [Real.log_prod (fun p hp => by
    have hpos : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
    exact zpow_ne_zero _ hpos.ne')]
  simp only [Real.log_zpow, Int.cast_neg]
  apply sum_congr rfl
  intro p hp
  ring

theorem log_normalizerSharp_split_sharp (s ν K N M : ℕ) (L : Allocations) (hM : 3 ≤ M) :
    Real.log (normalizerSharp s ν K N M L : ℝ) =
      smallPrimeLogContributionSharp s ν K N M L +
        innerPrimeLogContribution s ν K N M L + outerPrimeLogContribution s ν K N M L := by
  rw [log_normalizerSharp]
  unfold smallPrimeLogContributionSharp innerPrimeLogContribution outerPrimeLogContribution
  simp only [sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · by_cases hsmall : p * M ≤ K
    · have h3 : 3 * p ≤ K := by nlinarith [Nat.mul_le_mul_left p hM]
      simp [hprime, hsmall, show ¬K < p * M by omega, show ¬K < 3 * p by omega]
    · have hlarge : K < p * M := by omega
      by_cases hinner : 3 * p ≤ K
      · simp [hprime, hsmall, hlarge, hinner, show ¬K < 3 * p by omega]
      · simp [hprime, hsmall, hlarge, hinner, show K < 3 * p by omega]
  · simp [hprime]

/-- The actual sharp normalizer splits into the already-proved raw small range
and the actual E405 inner/outer ranges. This is a finite identity, not a bound. -/
theorem log_normalizerSharp_split (s ν K N M : ℕ) (L : Allocations) (hM : 3 ≤ M) :
    Real.log (normalizerSharp s ν K N M L : ℝ) =
      smallPrimeLogContribution s ν K N M L +
        innerPrimeLogContribution s ν K N M L + outerPrimeLogContribution s ν K N M L := by
  rw [← small_prime_sharp_eq_raw s ν K N M L]
  exact log_normalizerSharp_split_sharp s ν K N M L hM

#print axioms LpSharp_eq_raw_of_small
#print axioms small_prime_sharp_eq_raw
#print axioms log_normalizerSharp
#print axioms log_normalizerSharp_split_sharp
#print axioms log_normalizerSharp_split

end
end Mathathon.P108.SharpSplit
