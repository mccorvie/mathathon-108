import ArcMeasureDefs
/-! E222/U27, Codex. Every mathematical claim in this file has status CONJECTURE
pending the parent gate and human statement comparison. -/
noncomputable section
namespace U27
open MeasureTheory Set Real
open scoped ENNReal

def affineMap (a b u : ℝ) : ℝ := (a+b)/2+(b-a)/2*u

def standardWeight (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (1-u^2))⁻¹)
def intervalWeight (a b t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(Real.pi*Real.sqrt ((t-a)*(b-t))))

/-- CONJECTURE: positive affine rescaling sends the standard open support to (a,b). -/
lemma affine_image {a b : ℝ} (hab : a<b) :
    affineMap a b '' Ioo (-1:ℝ) 1 = Ioo a b := by
  have hr : 0<(b-a)/2 := by linarith
  have hf : affineMap a b = (fun u : ℝ => (b-a)/2*u+(a+b)/2) := by
    funext u
    dsimp [affineMap]
    ring
  rw [hf,Set.image_affine_Ioo hr]
  congr 1 <;> ring

/-- CONJECTURE: the affine derivative is the positive half-length. -/
lemma affine_deriv (a b u : ℝ) : HasDerivAt (affineMap a b) ((b-a)/2) u := by
  simpa only [affineMap,mul_one,add_comm] using!
    (((hasDerivAt_id u).const_mul ((b-a)/2)).const_add ((a+b)/2))

/-- CONJECTURE: exact real Jacobian cancellation on the open support. -/
lemma affine_density_factor_real {a b u : ℝ} (hab : a<b) (hu : u∈Ioo (-1:ℝ) 1) :
    (b-a)/2 * (1/(Real.pi*Real.sqrt
      ((affineMap a b u-a)*(b-affineMap a b u)))) =
      Real.pi⁻¹ * (Real.sqrt (1-u^2))⁻¹ := by
  have hr : 0<(b-a)/2 := by linarith
  have hu1 : 0<1-u^2 := by
    nlinarith [mul_pos (by linarith [hu.1] : 0<u+1) (by linarith [hu.2] : 0<1-u)]
  have hs : 0<Real.sqrt (1-u^2) := Real.sqrt_pos.mpr hu1
  have he : (affineMap a b u-a)*(b-affineMap a b u) =
      ((b-a)/2)^2*(1-u^2) := by dsimp [affineMap];ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  field_simp [ne_of_gt hr,ne_of_gt (sub_pos.mpr hab),ne_of_gt hs,ne_of_gt Real.pi_pos]
  <;> ring

/-- CONJECTURE: exact extended-nonnegative Jacobian cancellation. -/
lemma affine_density_factor_enn {a b u : ℝ} (hab : a<b) (hu : u∈Ioo (-1:ℝ) 1) :
    ENNReal.ofReal ((b-a)/2) * intervalWeight a b (affineMap a b u) =
      (ENNReal.ofReal Real.pi)⁻¹ * standardWeight u := by
  unfold intervalWeight standardWeight
  rw [←ENNReal.ofReal_mul (by linarith : 0≤(b-a)/2),
    affine_density_factor_real hab hu,
    ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_inv_of_pos Real.pi_pos]

/-- CONJECTURE: positive affine transport of the normalized standard arcsine density. -/
theorem affine_density_transport {a b : ℝ} (hab : a<b) :
    Measure.map (affineMap a b)
      ((ENNReal.ofReal Real.pi)⁻¹ •
        (volume.restrict (Ioo (-1:ℝ) 1)).withDensity standardWeight) =
      (volume.restrict (Ioo a b)).withDensity (intervalWeight a b) := by
  have hr : 0<(b-a)/2 := by linarith
  have hm : Measurable (affineMap a b) := by unfold affineMap;fun_prop
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioo (-1:ℝ) 1)
    (f := affineMap a b) (f' := fun _ => (b-a)/2) measurableSet_Ioo
    (fun u _ => (affine_deriv a b u).hasDerivWithinAt)
    (by
      intro u hu v hv huv
      apply mul_left_cancel₀ (ne_of_gt hr)
      dsimp [affineMap] at huv
      linarith)
    (fun t => intervalWeight a b t*g t)
  rw [affine_image hab] at hj
  have hgc : Measurable (fun u : ℝ => g (affineMap a b u)) := hg.comp hm
  have hsw : Measurable standardWeight := by unfold standardWeight;fun_prop
  have hiw : Measurable (intervalWeight a b) := by unfold intervalWeight;fun_prop
  rw [lintegral_map hg hm,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hsw hgc,
    lintegral_withDensity_eq_lintegral_mul _ hiw hg]
  change (ENNReal.ofReal Real.pi)⁻¹ *
      (∫⁻ u in Ioo (-1:ℝ) 1, standardWeight u*g (affineMap a b u)) =
    ∫⁻ t in Ioo a b, intervalWeight a b t*g t
  have hwg : Measurable (fun u : ℝ => standardWeight u*g (affineMap a b u)) := hsw.mul hgc
  rw [hj,←lintegral_const_mul _ hwg]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [abs_of_pos hr]
  simpa only [mul_assoc] using congrArg
    (fun z : ℝ≥0∞ => z*g (affineMap a b u)) (affine_density_factor_enn hab hu).symm

end U27
#print axioms U27.affine_image
#print axioms U27.affine_deriv
#print axioms U27.affine_density_factor_real
#print axioms U27.affine_density_factor_enn
#print axioms U27.affine_density_transport
