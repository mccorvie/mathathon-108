import ShortArithmeticFloor
import Witness.Sign
/-! E254/U59, Codex GPT-6, API support only for lane L's sole final integration.
PROOF-DRAFT aliases preserving seven historical export targets and one unregistered
weak scalar helper. Not a submission project, novelty claim or statement comparison.
Original AllM/UPackageMargin remain unchanged. Overall result CONJECTURE. -/
noncomputable section
namespace U18
open Mathathon.P108

/-- PROOF-DRAFT: exact old AllM public type, new proof provider. -/
theorem arithmetic_allM_strict (M : ℝ) (hM : 40 ≤ M) :
    (229:ℝ)/100 < thetaPkg 7 6 (3/40) M 0 :=
  U58.arithmetic_allM_strict M hM

/-- PROOF-DRAFT: exact old AllM public type, new proof provider. -/
theorem theta_allM_gt (M U : ℝ) (hM : 40 ≤ M) (hU : (-139:ℝ)/100 < U) :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) M U :=
  U58.theta_allM_gt M U hM hU

/-- PROOF-DRAFT: exact old explicit-witness specialization. -/
theorem theta_allM_lb6Square15 (M : ℝ) (hM : 40 ≤ M) :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) M U11.lb6Square15 :=
  theta_allM_gt M _ hM U11.lb6Square15_gt

/-- PROOF-DRAFT: exact old ordered-witness specialization. -/
theorem theta_allM_of_witness_le (M U : ℝ) (hM : 40 ≤ M)
    (hU : U11.lb6Square15 ≤ U) :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) M U :=
  theta_allM_gt M U hM (U11.lb6Square15_gt.trans_le hU)

/-- PROOF-DRAFT: weak historical helper is a direct specialization of new floor. -/
theorem arithmetic200_lower : (229:ℝ)/100 ≤
    Iout 7 6 (3/40) + 8*(1-(3/40:ℝ))/200 +
      ∫ x in (3:ℝ)..200, innerR 7 6 (3/40) x / x^3 := by
  simpa only [thetaPkg,zero_add,show (7:ℝ)+1=8 by norm_num] using
    (arithmetic_allM_strict (200:ℝ) (by norm_num)).le

/-- PROOF-DRAFT: exact old cutoff200 public margin. -/
theorem theta200_gt (U : ℝ) (hU : (-139:ℝ)/100 < U) :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) 200 U :=
  theta_allM_gt 200 U (by norm_num) hU

/-- PROOF-DRAFT: exact old cutoff200 explicit-witness margin. -/
theorem theta200_lb6Square15 :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) 200 U11.lb6Square15 :=
  theta_allM_lb6Square15 200 (by norm_num)

/-- PROOF-DRAFT: exact old cutoff200 ordered-witness margin. -/
theorem theta200_of_witness_le (U : ℝ) (hU : U11.lb6Square15 ≤ U) :
    (9:ℝ)/10 < thetaPkg 7 6 (3/40) 200 U :=
  theta_allM_of_witness_le 200 U (by norm_num) hU
end U18
#print axioms U18.arithmetic_allM_strict
#print axioms U18.theta_allM_gt
#print axioms U18.theta_allM_lb6Square15
#print axioms U18.theta_allM_of_witness_le
#print axioms U18.arithmetic200_lower
#print axioms U18.theta200_gt
#print axioms U18.theta200_lb6Square15
#print axioms U18.theta200_of_witness_le
