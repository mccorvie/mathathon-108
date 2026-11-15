import BInnerStatement
import AllM

/-!
E430, Codex native outer_sum, lane B, 2026-11-14.
PROOF-DRAFT until parent gate. This is an implication from the named actual
normalizer-limit target, which remains open. The scalar inequality is the actual
gated U18.theta_allM_gt, not a caller assumption. No irrationality claim.
CITED: lane U E213 AllM.lean28, exact source copied; prior numerical/formal
zeta7 margin failures are credited in the lane R/integrator record. No first
kernel-margin or mathematical novelty claim is made.
-/
open Filter Topology
namespace BNormalizerMargin
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108
open Mathathon.P108.RangeBridgeTarget Mathathon.P108.InnerExplicitTarget

/-- PROOF-DRAFT: adding the fixed analytic exponent gives the literal package limit. -/
theorem explicit_margin_limit (hLimit : ExplicitNormalizerLimitStatement) :
    ZetaSevenExplicitMarginLimitStatement := by
  intro M hM U
  have h := (hLimit 7 6 M (by norm_num [ParameterScope, Odd, Even]) hM).const_add U
  convert h using 1
  simp only [arithmeticPackage, thetaPkg]
  ring

/-- PROOF-DRAFT: exact approved E213 corollary for the actual selected normalizer.
The sole named mathematical premise is the actual full normalizer limit. -/
theorem explicit_margin_positive (hLimit : ExplicitNormalizerLimitStatement) :
    ZetaSevenExplicitMarginPositiveStatement := by
  intro M hM U hU
  have h := explicit_margin_limit hLimit M hM U
  have hMreal : (40 : ℝ) ≤ M := by exact_mod_cast hM
  exact h.eventually_const_lt (U18.theta_allM_gt M U hMreal hU)

#print axioms explicit_margin_limit
#print axioms explicit_margin_positive
#check explicit_margin_positive
end
end BNormalizerMargin
