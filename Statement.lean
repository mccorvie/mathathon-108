import BAnalyticMoments
import Zeta5S.Pullback

/-!
B8/E409: proposed actual-density pole identity, by Codex lane B.
The proposition definitions below are CONJECTURE targets, not theorems.
No proof of a pole identity is asserted in this file.
The two ancillary helpers are PROOF-DRAFT until the repository gate runs.
Copies of B6/L modules are byte-exact, with attribution retained (NOTICE/LICENSE).
-/

open MeasureTheory Set Filter Topology Polynomial

namespace BAnalyticPoles

/-- Real zeta sum; its n=0 term is zero for every s>=1. -/
noncomputable def zetaS (s : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

/-- The exact requested target uses the actual B6 density and actual lane-L polynomial.
This is a proposition definition; no proof or hypothesis asserting it is supplied. -/
def GeneralPoleStatement : Prop :=
  ∀ (s : ℕ), Odd s → 3 ≤ s → ∀ (j : ℕ), 1 ≤ j →
    IntegrableOn (fun y : ℝ => BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2)) (Ioi 0) ∧
      (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2)) =
        aeval (zetaS s) (AperyS.poleValueS s j)

/-- The real-parameter tail needed for a differentiation/recurrence route. -/
noncomputable def zetaTail (s : ℕ) (a : ℝ) : ℝ :=
  ∑' l : ℕ, 1 / (a + ((l : ℝ) + 1)) ^ s

/-- A stronger real-parameter auxiliary target for the preferred Gamma/Mittag-Leffler route.
Again, this definition is not a theorem. -/
def RealPoleStatement : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (a : ℝ), 0 < a →
    (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) =
      a ^ (s - 1) * zetaTail s a - 1 / ((s : ℝ) - 1) + 1 / (2 * a)

/-- Candidate per-index integral recurrence; no proof is asserted here. -/
def PoleRecurrenceStatement : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (a : ℝ), 0 < a →
    (s : ℝ) * (∫ y in Ioi 0, BAnalyticMoments.w (s + 1) y / (y ^ 2 + a ^ 2)) =
      ((s : ℝ) - 1) * (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) +
        2 * a ^ 2 * (∫ y in Ioi 0, BAnalyticMoments.w s y / (y ^ 2 + a ^ 2) ^ 2)

/-- Unfolding the actual lane-L polynomial exposes the intended arithmetic constants. -/
lemma aeval_poleValueS (s j : ℕ) (x : ℝ) :
    aeval x (AperyS.poleValueS s j) =
      (j : ℝ) ^ (s - 1) * (x - (AperyS.Hs s j : ℝ)) -
        1 / ((s : ℝ) - 1) + 1 / (2 * (j : ℝ)) := by
  simp [AperyS.poleValueS]

/-- The integrability part of the target follows already from B6; no pole identity. -/
lemma integrableOn_pole (s : ℕ) (hs : 2 ≤ s) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)) (Ioi 0) := by
  have hw : IntegrableOn (BAnalyticMoments.w s) (Ioi 0) := by
    simpa only [mul_zero, pow_zero, one_mul] using BAnalyticMoments.integrableOn_monomial s hs 0
  have hdom : IntegrableOn (fun y => (1 / a ^ 2) * BAnalyticMoments.w s y) (Ioi 0) :=
    hw.const_mul _
  have hmeas : AEMeasurable (fun y : ℝ => BAnalyticMoments.w s y / (y ^ 2 + a ^ 2))
      (volume.restrict (Ioi 0)) :=
    hw.aestronglyMeasurable.aemeasurable.div (by fun_prop : Measurable fun y : ℝ => y ^ 2 + a ^ 2).aemeasurable
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hwy : 0 < BAnalyticMoments.w s y := BAnalyticMoments.w_pos s hy
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [Real.norm_of_nonneg (div_nonneg hwy.le (by positivity))]
  calc BAnalyticMoments.w s y / (y ^ 2 + a ^ 2)
      ≤ BAnalyticMoments.w s y / a ^ 2 :=
        div_le_div_of_nonneg_left hwy.le ha2 (by nlinarith [sq_nonneg y])
    _ = _ := by ring

#print BAnalyticPoles.GeneralPoleStatement
#print BAnalyticPoles.RealPoleStatement
#print BAnalyticPoles.PoleRecurrenceStatement
#print axioms BAnalyticPoles.aeval_poleValueS
#print axioms BAnalyticPoles.integrableOn_pole
end BAnalyticPoles
