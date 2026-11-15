import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-! E221/U26, Codex, lane U. Every mathematical claim in this file has status
CONJECTURE pending parent gate and human statement comparison.
Uses Mathlib's existing Jacobian theorem and inverse trigonometric API; this is
not a proof yet of equality with the full-angle E212 arcsineMeasure. -/
noncomputable section
namespace U26
open MeasureTheory Set Real
open scoped ENNReal

/-- CONJECTURE: exact nonnegative change of variables for the cosine half-arc. -/
theorem half_angle_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ theta in Ioo (0:ℝ) Real.pi, g (Real.cos theta)) =
      ∫⁻ t in Ioo (-1:ℝ) 1,
        ENNReal.ofReal ((Real.sqrt (1-t^2))⁻¹) * g t := by
  have hi : Real.arccos '' Ioo (-1:ℝ) 1 = Ioo (0:ℝ) Real.pi := by
    exact Real.cosPartialHomeomorph.symm.image_source_eq_target
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (f := Real.arccos) (f' := fun t => -(1 / Real.sqrt (1-t^2)))
    measurableSet_Ioo
    (fun t ht => (Real.hasDerivAt_arccos (by linarith [ht.1]) (by linarith [ht.2])).hasDerivWithinAt)
    (Real.arccos_injOn.mono Ioo_subset_Icc_self)
    (fun theta => g (Real.cos theta))
  rw [hi] at h
  refine h.trans ?_
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [Real.cos_arccos ht.1.le ht.2.le]
  congr 2
  rw [abs_neg, abs_of_nonneg (by positivity)]
  exact one_div _

/-- CONJECTURE: unnormalized density identification for the standard cosine half-arc. -/
theorem half_angle_map :
    Measure.map Real.cos (volume.restrict (Ioo (0:ℝ) Real.pi)) =
      (volume.restrict (Ioo (-1:ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal ((Real.sqrt (1-t^2))⁻¹)) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
  exact half_angle_lintegral g

/-- CONJECTURE: previously available Mathlib Bochner identity, stated for comparison. -/
theorem mathlib_chebyshev_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂Polynomial.Chebyshev.measureT) =
      ∫ theta in (0:ℝ)..Real.pi, f (Real.cos theta) :=
  Polynomial.Chebyshev.integral_measureT_eq_integral_cos

end U26
#print axioms U26.half_angle_lintegral
#print axioms U26.mathlib_chebyshev_integral

#print axioms U26.half_angle_map
