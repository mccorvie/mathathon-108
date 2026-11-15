import SplitEntry
import ClosingEntry
import BFullPositive
import ShortArithmeticFloor
import AllM
import BoundedFieldSupremum
import FieldCoercivity
import ZetaBridge
import Mathathon.P108.SStepAll
import Mathathon.P108.OuterValues58
import LeanWitness.ClassLoss
import Mathathon.P108.OffsetGap
import Mathathon.P108.LaiSkip
import Zeta5S.FiniteStep
import CompactAnalyticBound

/-!
# The report's Lean results, in three layers

LEAN-CHECKED: these are existing declarations, all in the receiving final gate.
This file adds no mathematical declaration or proof. The report controls the
stronger LEAN-VERIFIED labels and records all differences from the paper claims.
The independent statement-only Comparator challenge is not imported here.
-/

/-! ## Layer 1: symbolic parameters
Report claim 1: the class loss, local valuation and integer normalisation.
The exact hypotheses are printed; these are bounds, not optimality assertions.
-/
#check AperyS.tauXs_direct
#check AperyS.AssemblyTarget.local_valuation_sharp
#check AperyS.AssemblyTarget.normalization_statement
#check AperyS.AssemblyTarget.normalization_sharp_statement

/-! Report claim 2: the scalar s-step and its lower bound; U is a free real input. -/
#check Mathathon.P108.thetaPkg_sstep
#check Mathathon.P108.theta_sstep_7_6
#check Mathathon.P108.sstep_ge
#check Mathathon.P108.thetaPkg_odd_ge

/-! Report claim 5: the fixed-template normalizer limit, the nu=6 finite analytic
bound, identification of zeta, and the criterion with a supplied analytic bound.
The criterion does not supply its own negative margin or analytic hypothesis.
-/
#check BFullBridge.explicit_normalizer_limit_statement
#check LMergeCompactAnalytic.finite_real_bound
#check BZetaIdentification.riemannZeta_eq_zetaS
#check BSymbolicCriterion.criterion_standard

/-! Report claim 5, finite-step qualifications: fixed-allocation comparisons and
a selected-bound branch switch. These are not determinant valuation equalities.
-/
#check AperyS.AssemblyTarget.WI_sstep_bounds
#check AperyS.AssemblyTarget.Lp_inner_sstep
#check AperyS.AssemblyTarget.selected_Lp_can_increase

/-! ## Layer 2: the point (s, nu) = (7, 6)
Report claim 3: the scalar arithmetic floor, the scalar positive margin, the
eventual margin of one explicit normalizer, and the energy floor over the
displayed comparison class. None is a result about the arithmetic nature of zeta(7).
-/
#check U18.arithmetic_allM_strict
#check U18.theta_allM_gt
#check BFullBridge.zeta_seven_explicit_margin_positive_statement
#check U44.optimized_energy_floor_real
#check U44.fieldSup_ne_top
#check U44.package_margin_optimized
#check U44.optimal_energy_floor_real
#check U43.V6_coercive

/-! ## Layer 3: the s=5 instance and concrete audits
Report claim 8: the actual local field and closing certificates, the positive
finite real bound and the unconditional Mathlib zeta(5) statement. This is a
re-derivation of Fauzan's theorem reusing Firsching's formalisation and its credits.
-/
#check CSplitField.local_field_certificate
#check SplitClosing.closing_neg
#check CCertificateSplit.finite_real_bound
#check CCertificateSplit.irrational_five

/-! Report claim 7: the exact scalar integral gain at (5,8), without its valuation
interpretation. The remaining lines locate the concrete certificate audits.
-/
#check Mathathon.P108.gain58_formal
#check Mathathon.P108.classLoss_witness
#check Mathathon.P108.lai_offset_gap_7_2
#check Mathathon.P108.Skip.Delta_eq
#check Mathathon.P108.Skip.lai_skip_witness
