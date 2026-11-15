import Zeta5S.AssemblyData
import Mathathon.P108.SStep

/-!
B2 / E402, lane B, Codex, 2026-11-14. STATEMENTS FOR REVIEW ONLY.

CONJECTURE: these Prop definitions are unproved targets, not theorem declarations.
They use the existing L7 local exponent and the existing package margin literally.
The proposed scope is ONLY the small-prime contribution to log(normalizer).

Source architecture: Firsching/Paul-Lez, mo271/Zeta5@be1c0d82,
Apery/Growth/Assembly1.lean:15-30,42-128 and Growth.lean:25-70,
Apache-2.0. Definitions Lp, degreeBound and primeBound are imported from
lane L's AssemblyData.lean unchanged. The package side is imported from
Mathathon/P108/SStep.lean unchanged. No proof has been attempted here.
-/

open Filter Finset

namespace Mathathon.P108.BridgeTarget

noncomputable section

open AperyS.AssemblyTarget

/-- A derived quantity, not a new local exponent: precisely the factors of the
actual normalizer whose primes satisfy p*M<=K, written additively after log.
The support filter retains the actual finite prime support of the normalizer. -/
def smallPrimeLogContribution (s ν K N M : ℕ) (L : Allocations) : ℝ :=
  ∑ p ∈ (range (primeBound s K N + 1)).filter (fun p => p.Prime ∧ p * M ≤ K),
    Real.log (p : ℝ) * (-(Lp s ν K N M p L : ℝ))

/-- Explicit finite envelope. Let D=degreeBound+1 and f=(s-1)!.
The final h*f*log(f) is a deliberately crude finite bound for the factorial
valuation contribution; f is fixed in the asymptotic target. -/
def smallPrimeFiniteEnvelope (s ν K N M : ℕ) : ℝ :=
  let D : ℝ := (degreeBound s ν K N + 1 : ℕ)
  let f : ℝ := (s - 1).factorial
  ((s : ℝ) + 1) * (K - N : ℕ) *
      (Chebyshev.theta ((K / M : ℕ) : ℝ) + (Real.sqrt D + 1) * Real.log D) +
    (K - N : ℕ) * f * Real.log f

/-- CONJECTURE target: the finite estimate has no hypotheses on the supplied
allocation, no InnerOK/OuterOK assumption and no PNT premise. Parity of s and nu
is unnecessary for this algebraic estimate of the explicitly defined Lp. -/
def FiniteSmallPrimeStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    3 ≤ s → N < K → 1 ≤ M →
    smallPrimeLogContribution s ν K N M L ≤ smallPrimeFiniteEnvelope s ν K N M

/-- CONJECTURE target: for fixed natural s,nu,M, uniformly over every allocation,
the normalized small-prime contribution is eventually at most the explicit
coefficient (s+1)*(1-3/40)/M plus epsilon. PNT is needed in the proof, not assumed
as the desired conclusion or as an unproved premise of this proposition. -/
def EventualSmallPrimeCoefficientStatement : Prop :=
  ∀ (s ν M : ℕ), 3 ≤ s → 3 ≤ M →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ L : Allocations,
        smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
            (((40 * n : ℕ) : ℝ) ^ 2) ≤
          ((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)) / (M : ℝ) + ε

/-- CONJECTURE target: the same bound literally meets End2's thetaPkg definition.
Subtracting U, Iout, and the existing inner integral leaves precisely its
small-prime term. This is a partial bridge; it does not bound the other prime
ranges, the full log(normalizer), or the full package exponent. -/
def EventualSmallPrimePackageStatement : Prop :=
  ∀ (s ν M : ℕ), 3 ≤ s → 3 ≤ M →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ (L : Allocations) (U : ℝ),
        smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
            (((40 * n : ℕ) : ℝ) ^ 2) ≤
          Mathathon.P108.thetaPkg (s : ℝ) (ν : ℝ) (3 / 40) (M : ℝ) U - U -
            Mathathon.P108.Iout (s : ℝ) (ν : ℝ) (3 / 40) -
            (∫ x in (3 : ℝ)..(M : ℝ),
              Mathathon.P108.innerR (s : ℝ) (ν : ℝ) (3 / 40) x / x ^ 3) + ε

/-- Proposed B3 target, pending integrator review. The coefficient version is
also printed separately to expose the literal term of the package being met. -/
def SmallPrimeBridgeStatement : Prop :=
  FiniteSmallPrimeStatement ∧ EventualSmallPrimePackageStatement

#print FiniteSmallPrimeStatement
#print EventualSmallPrimeCoefficientStatement
#print EventualSmallPrimePackageStatement
#print SmallPrimeBridgeStatement

end
end Mathathon.P108.BridgeTarget
