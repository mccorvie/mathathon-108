import OuterLocal
import OuterScalar
import AboveK

/-! E418 / C4, Codex lane B. PROOF-DRAFT pending driver gate.
The exact approved E405 OuterLocalStatement is proved from the actual sharp
pole estimate, actual scalar valuation estimate, and the p>K exact branch.
The three imported local pieces are copied byte-exact; LOCAL_PIECE_MANIFEST.json
records their source hashes. No PNT, integration, or inner allocation claim.
-/

namespace BOuterBridge
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.RangeBridgeTarget

def outerLocalConstant (s ν : ℕ) : ℝ := sharpPoleConstant s ν + 11

theorem outerLocalConstant_nonneg (s ν : ℕ) (hs : 1 ≤ s) :
    0 ≤ outerLocalConstant s ν := by
  unfold outerLocalConstant
  linarith [sharpPoleConstant_nonneg s ν hs]

theorem outer_local_bound (s ν n M p : ℕ) (L : Allocations)
    (hscope : ParameterScope s ν) (hn : max 1 s ≤ n) (hM : 3 ≤ M)
    (hp : p.Prime) (hpB : p ≤ primeBound s (40 * n) (3 * n))
    (hout : 40 * n < 3 * p) :
    |-(LpSharp s ν (40 * n) (3 * n) M p L : ℝ) -
      ((40 * n : ℕ) : ℝ) * Tout s ν (3 / 40)
        ((p : ℝ) / ((40 * n : ℕ) : ℝ))| ≤ outerLocalConstant s ν := by
  have hC0 : 0 ≤ sharpPoleConstant s ν := sharpPoleConstant_nonneg s ν (by
    have := hscope.2.1
    omega)
  unfold outerLocalConstant
  by_cases hKp : 40 * n < p
  · exact (BOuterAboveK.outer_local_above_K_bound s ν n M p L
      hscope hn hM hp hpB hKp).trans (by linarith)
  · have hpK : p ≤ 40 * n := by omega
    have hP := sharp_pole_bound s ν n p hscope hn hp hpK hout
    have hS := BOuterScalar.scalar_legendre_bounds ν n p (by omega) hp hout
    rw [selected_sharp_outer s ν n p M L hscope hn hM hp hout]
    simp only [Int.cast_add]
    unfold Tout
    rw [abs_le] at hP ⊢
    constructor <;> linarith [hP.1, hP.2, hS.1, hS.2]

/-- The unchanged E405 local target, on its entire actual prime support. -/
theorem outer_local_statement : OuterLocalStatement := by
  intro s ν hscope
  refine ⟨outerLocalConstant s ν, outerLocalConstant_nonneg s ν (by
    have := hscope.2.1
    omega), ?_⟩
  intro n hn M hM L p hp hpB hout
  exact outer_local_bound s ν n M p L hscope hn hM hp hpB hout

#print axioms outerLocalConstant_nonneg
#print axioms outer_local_bound
#print axioms outer_local_statement
#print outer_local_statement

end
end BOuterBridge
