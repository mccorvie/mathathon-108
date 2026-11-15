import SplitAnalytic
import ConfigurationTransport
import RealTransport

/-!
Codex lane L supplement, hagoromo, 2026-11-14.
PROOF-DRAFT until the receiving final gate. This is the composition requested
by the integrator on BOARD.md at 21:03, with the existing U49/U51/U52 leaves.
All constituent proofs retain their own credits to Fauzan, Firsching's
mo271/Zeta5@be1c0d82 formalisation (Apache-2.0), Paul-Lez, and lane U.
E612 receiving revision: threshold -32999/5000, exponent -2650371/2000000.
The new zeta(5) closing uses cutoff1000000; this finite analytic theorem has no cutoff parameter.
It exposes the general-s compact analytic bound, without upstream energy tables.
The stronger historical BAnalyticRealBound declarations are not redefined.
-/
open Polynomial
namespace LMergeCompactAnalytic

/-- PROOF-DRAFT: existing compact certificate composed for every natural s >= 2. -/
theorem finite_real_bound :
    ∀ s n : ℕ, 2 ≤ s → 1 ≤ n →
      0 < aeval (BAnalyticPoles.zetaS s) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n)) ∧
        Real.log (aeval (BAnalyticPoles.zetaS s) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n))) ≤
          ((-2650371 : ℝ) / 2000000) * ((40 * n : ℕ) : ℝ) ^ 2 +
            ((s : ℝ) + 23) * (37 * n : ℕ) * Real.log ((40 * n : ℕ) : ℝ) +
            (12 * Real.log 2 + 23 + Real.log (BAnalyticIntegral.C s (2 * Real.pi))) * (37 * n : ℕ) :=
  U52.real_bound_transport ((-32999 : ℝ) / 5000) ((-2650371 : ℝ) / 2000000)
    (U51.configuration_of_enhanced _
      (U51.local_to_enhanced _ CSplitAnalytic.local_field (by norm_num [Apery.M0])))
    CSplitAnalytic.scalar_budget

#check finite_real_bound
#print axioms finite_real_bound
end LMergeCompactAnalytic
