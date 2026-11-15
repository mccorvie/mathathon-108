import Folding
import AffineDensity
/-! E222/U27, Codex. Every mathematical claim in this file has status CONJECTURE
pending the parent gate and human statement comparison. The three E212 measure
definitions are extracted with literal declaration bodies and original names;
see source-map.json. No arbitrary-measure energy inequality is asserted. -/
noncomputable section
namespace U27
open MeasureTheory Set Real Mathathon.P108.ArcMeasure
open scoped ENNReal

/-- CONJECTURE: full-angle folding for E212's literal angular-pushforward definitions. -/
theorem arcsineMeasure_folding (a b : ℝ) :
    arcsineMeasure a b =
      Measure.map (affineMap a b)
        ((ENNReal.ofReal Real.pi)⁻¹ •
          Measure.map Real.cos (volume.restrict (Ioo (0:ℝ) Real.pi))) := by
  unfold arcsineMeasure
  change Measure.map (affineMap a b ∘ Real.cos) angleMeasure = _
  rw [←Measure.map_map (by unfold affineMap;fun_prop) (by fun_prop),
    normalized_cos_folding]

/-- CONJECTURE: the literal E212 angular pushforward equals the classical density law. -/
theorem arcsineMeasure_eq_density {a b : ℝ} (hab : a<b) :
    Mathathon.P108.ArcMeasure.arcsineMeasure a b =
      (volume.restrict (Ioo a b)).withDensity (fun t =>
        ENNReal.ofReal (1/(Real.pi*Real.sqrt ((t-a)*(b-t))))) := by
  rw [arcsineMeasure_folding,U26.half_angle_map]
  exact affine_density_transport hab

end U27
#print axioms U27.arcsineMeasure_folding
#print axioms U27.arcsineMeasure_eq_density
