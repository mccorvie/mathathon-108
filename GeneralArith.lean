import CriterionStatement
import GeneralDegree

/-!
E436, Codex gpt-6.1-sol, lane B, 2026-11-14. PROOF-DRAFT until parent gate.
Uniform fixed-shape instances of lane-L E311's actual sharp normalizer and
lane-B E432's actual same-allocation limit. Finite normalization adapts
C-arith-instance/Proofs.lean:40-54; the growth and margin adapters follow
its lines 71-98, now with symbolic s,ν,M. Prior construction/normalizer:
Firsching/Paul-Lez, mo271/Zeta5@be1c0d82, Apache-2.0. Imported E311/E432
retain their own exact source and Deicyde/PNT attribution. No analytic
bound, negative margin, or irrationality conclusion is assumed or proved here.
-/
set_option autoImplicit false
open Polynomial Filter Topology

namespace BSymbolicCriterion
noncomputable section

open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget

theorem degree_statement (s ν : ℕ) : DegreeStatement s ν := by
  intro n
  exact degree_bound s ν n

/-- The finite E311 hypotheses follow for every positive shape index. -/
theorem arithmetic_side_conditions (s ν : ℕ) (hScope : ParameterScope s ν)
    (n : ℕ) (hn : 1 ≤ n) :
    3 * n < 40 * n ∧ 6 * (3 * n) ≤ 40 * n ∧
      40 * n + (ν - 2) * (3 * n) ≤ ((s - 1) / 2) * (40 * n) ∧
      2 * (40 * n) ≤ degreeBound s ν (40 * n) (3 * n) ∧
      40 * n - 3 * n = 37 * n := by
  obtain ⟨_hodd, hs, _heven, _hν, hνmax⟩ := hScope
  have hνsub : ν - 2 ≤ 8 := by omega
  have hr : 2 ≤ (s - 1) / 2 := by omega
  have hνbudget := Nat.mul_le_mul_right (3 * n) hνsub
  have hsbudget := Nat.mul_le_mul_right (40 * n) hr
  refine ⟨by omega, by omega, by omega, ?_, by omega⟩
  unfold degreeBound
  have hh : 40 * n - 3 * n = 37 * n := by omega
  rw [hh]
  omega

/-- Positivity holds even without a parameter-scope or cutoff hypothesis. -/
theorem normalizer_pos (s ν M n : ℕ) : 0 < m s ν M n := by
  exact normalizerSharp_pos s ν (40 * n) (3 * n) M
    (explicitAllocation s ν (40 * n) (3 * n) M)

theorem normalization (s ν M : ℕ) (hScope : ParameterScope s ν) (_hM : 40 ≤ M) :
    NormalizationStatement s ν M := by
  constructor
  · intro n
    exact normalizer_pos s ν M n
  · intro n hn
    obtain ⟨hNK, hα, hbudget, hshape, hh⟩ := arithmetic_side_conditions s ν hScope n hn
    obtain ⟨hodd, hs, _heven, hν, _hνmax⟩ := hScope
    have h := normalization_sharp s ν (40 * n) (3 * n) M
      (explicitAllocation s ν (40 * n) (3 * n) M)
      hodd (by omega) hν hNK hα hbudget hshape
    simpa only [m, F, hh] using h

/-- The exact E432 normalizer limit; the actual polynomial is not substituted. -/
theorem normalizer_limit (s ν M : ℕ) (hScope : ParameterScope s ν) (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => Real.log (m s ν M n : ℝ) / K n ^ 2)
      atTop (𝓝 (A s ν M)) :=
  BFullBridge.explicit_normalizer_limit_statement s ν M hScope hM

theorem normalizer_growth (s ν M : ℕ) (hScope : ParameterScope s ν) (hM : 40 ≤ M) :
    NormalizerGrowthStatement s ν M := by
  intro ε hε
  have hLim := normalizer_limit s ν M hScope hM
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.log (m s ν M n : ℝ) / K n ^ 2 < A s ν M + ε :=
    hLim.eventually_lt_const (by linarith)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hbound hn
  have hK : 0 < K n := by
    unfold K
    positivity
  exact (div_le_iff₀ (pow_pos hK 2)).mp hbound.le

theorem margin_identity (s ν M : ℕ) (u : ℝ) :
    A s ν M + u = Mathathon.P108.thetaPkg s ν (3 / 40) M u := by
  unfold A Mathathon.P108.InnerExplicitTarget.arithmeticPackage Mathathon.P108.thetaPkg
  ring

#check degree_statement
#check normalization
#check normalizer_growth
#check margin_identity
#print axioms degree_statement
#print axioms arithmetic_side_conditions
#print axioms normalizer_pos
#print axioms normalization
#print axioms normalizer_limit
#print axioms normalizer_growth
#print axioms margin_identity

end
end BSymbolicCriterion
