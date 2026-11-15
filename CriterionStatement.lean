import Final

/-!
E436, Codex lane B. CONJECTURE interface only; no target proof is supplied.
Requested by the integrator Sat19:43: symbolic version of C's Assembly.lean.
Credits: Fauzan's construction; Firsching's Zeta5 formalization atbe1c0d82,
Apache-2.0; Paul-Lez Comparator metadata; laneL E311 and laneB E432, with
prior Deicyde/PNT credit preserved in their unchanged source closures.
-/
set_option autoImplicit false
open Polynomial Filter Topology
namespace BSymbolicCriterion
noncomputable section

/-- The same real series as the canonical BAnalyticPoles.zetaS. -/
def xi (s : ℕ) : ℝ := ∑' k : ℕ, 1 / (k : ℝ) ^ s

def K (n : ℕ) : ℝ := ((40 * n : ℕ) : ℝ)

def F (s ν n : ℕ) : ℚ[X] := AperyS.FS s ν (40 * n) (3 * n) (37 * n)

def m (s ν M n : ℕ) : ℚ :=
  AperyS.AssemblyTarget.normalizerSharp s ν (40 * n) (3 * n) M
    (Mathathon.P108.RangeBridgeTarget.explicitAllocation s ν (40 * n) (3 * n) M)

def A (s ν M : ℕ) : ℝ := Mathathon.P108.InnerExplicitTarget.arithmeticPackage s ν M

def DegreeStatement (s ν : ℕ) : Prop := ∀ n : ℕ, (F s ν n).natDegree ≤ 37 * n

def NormalizationStatement (s ν M : ℕ) : Prop :=
  (∀ n : ℕ, 0 < m s ν M n) ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m s ν M n) * F s ν n

def NormalizerGrowthStatement (s ν M : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.log (m s ν M n : ℝ) ≤ (A s ν M + ε) * K n ^ 2

/-- Supplied analytic input, at one fixed order and numerator power. -/
def AnalyticLeadingStatement (s ν : ℕ) (u : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    0 < aeval (xi s) (F s ν n) ∧
      Real.log (aeval (xi s) (F s ν n)) ≤ (u + ε) * K n ^ 2

/-- The arithmetic, integer lift and degree bounds are to be discharged internally.
The only mathematical input besides the parameter conditions is the stated
analytic bound and a negative value of the literal package. -/
def CriterionStatement : Prop :=
  ∀ s ν M : ℕ, Mathathon.P108.RangeBridgeTarget.ParameterScope s ν → 40 ≤ M →
    ∀ u : ℝ, AnalyticLeadingStatement s ν u →
      Mathathon.P108.thetaPkg s ν (3 / 40) M u < 0 → Irrational (xi s)

end
end BSymbolicCriterion
