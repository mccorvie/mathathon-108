import ArcMeasureDefs
/-! E222/U27, Codex. Every mathematical claim in this file has status CONJECTURE
pending the parent gate and human statement comparison. -/
noncomputable section
namespace U27
open MeasureTheory Set Real
open scoped ENNReal

/-- CONJECTURE: reflection exchanges the two open cosine half-arcs. -/
lemma reflected_half_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ theta in Ioo Real.pi (2*Real.pi), g (Real.cos theta)) =
      ∫⁻ theta in Ioo (0:ℝ) Real.pi, g (Real.cos theta) := by
  have hi : (fun theta : ℝ => 2*Real.pi-theta) '' Ioo (0:ℝ) Real.pi =
      Ioo Real.pi (2*Real.pi) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      constructor <;> linarith [hx.1,hx.2]
    · intro hy
      refine ⟨2*Real.pi-y,⟨by linarith [hy.2],by linarith [hy.1]⟩,?_⟩
      ring
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioo (0:ℝ) Real.pi)
    (f := fun theta : ℝ => 2*Real.pi-theta) (f' := fun _ => (-1:ℝ))
    measurableSet_Ioo
    (fun theta _ => by
      have hd : HasDerivAt (fun x : ℝ => 2*Real.pi-x) (-1) theta := by
        simpa using! (hasDerivAt_id theta).const_sub (2*Real.pi)
      exact hd.hasDerivWithinAt)
    (by intro x hx y hy hxy; dsimp at hxy; linarith)
    (fun theta => g (Real.cos theta))
  rw [hi] at h
  simpa only [abs_neg,abs_one,ENNReal.ofReal_one,one_mul,Real.cos_two_pi_sub] using h

/-- CONJECTURE: splitting the full angular interval, including endpoint conventions. -/
lemma full_angle_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ theta in Ioc (0:ℝ) (2*Real.pi), g (Real.cos theta)) =
      2 * ∫⁻ theta in Ioo (0:ℝ) Real.pi, g (Real.cos theta) := by
  have hd : Disjoint (Ioc (0:ℝ) Real.pi) (Ioc Real.pi (2*Real.pi)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  have hs : volume.restrict (Ioc (0:ℝ) (2*Real.pi)) =
      volume.restrict (Ioo (0:ℝ) Real.pi) +
      volume.restrict (Ioo Real.pi (2*Real.pi)) := by
    rw [restrict_Ioo_eq_restrict_Ioc,restrict_Ioo_eq_restrict_Ioc,
      ←Measure.restrict_union hd measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc Real.pi_pos.le (by linarith [Real.pi_pos])]
  rw [hs,lintegral_add_measure,reflected_half_lintegral]
  exact (two_mul _).symm

/-- CONJECTURE: the normalized full-angle cosine pushforward equals the half-angle law. -/
theorem normalized_cos_folding :
    Measure.map Real.cos Mathathon.P108.ArcMeasure.angleMeasure =
      (ENNReal.ofReal Real.pi)⁻¹ •
        Measure.map Real.cos (volume.restrict (Ioo (0:ℝ) Real.pi)) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (by fun_prop),Mathathon.P108.ArcMeasure.angleMeasure,
    lintegral_smul_measure,lintegral_smul_measure,lintegral_map hg (by fun_prop),
    full_angle_lintegral]
  change (ENNReal.ofReal (2*Real.pi))⁻¹ * (2 * _) = (ENNReal.ofReal Real.pi)⁻¹ * _
  have hc : (ENNReal.ofReal (2*Real.pi))⁻¹ * 2 = (ENNReal.ofReal Real.pi)⁻¹ := by
    rw [←ENNReal.ofReal_inv_of_pos (by positivity : 0<2*Real.pi),
      ←ENNReal.ofReal_inv_of_pos Real.pi_pos]
    rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    <;> ring
  rw [←mul_assoc,hc]

end U27
#print axioms U27.reflected_half_lintegral
#print axioms U27.full_angle_lintegral
#print axioms U27.normalized_cos_folding
