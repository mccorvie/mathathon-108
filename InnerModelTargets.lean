import Mathathon.P108.InnerShift
import Mathlib
/- E426 native Codex inner_regularity, lane B.
CONJECTURE targets only, literal actual root definitions unchanged. -/
open MeasureTheory Set Filter Topology
namespace BInnerLimit
noncomputable section
open Mathathon.P108

def innerWeight (s ν : ℝ) (y : ℝ) : ℝ := y * innerR s ν (3 / 40) y⁻¹

/-- CONJECTURE: actual-model boundedness, stronger arbitrary real parameters. -/
def BoundedStatement : Prop := ∀ (s ν : ℝ) (M : ℕ), 3 ≤ M →
  ∃ C : ℝ, ∀ y ∈ Icc (1 / (M : ℝ)) (1 / 3), |innerWeight s ν y| ≤ C

/-- CONJECTURE: finite relative discontinuities of the actual model. -/
def FiniteDiscontinuitiesStatement : Prop := ∀ (s ν : ℝ) (M : ℕ), 3 ≤ M →
  {y ∈ Icc (1 / (M : ℝ)) (1 / 3) |
    ¬ContinuousWithinAt (innerWeight s ν) (Icc (1 / (M : ℝ)) (1 / 3)) y}.Finite

/-- CONJECTURE: literal inversion identity, no integrability premise. -/
def InversionStatement : Prop := ∀ (s ν : ℝ) (M : ℕ), 3 ≤ M →
  (∫ y in (1 / (M : ℝ))..(1 / 3), innerWeight s ν y) =
    ∫ x in (3 : ℝ)..M, innerR s ν (3 / 40) x / x ^ 3
end
end BInnerLimit
