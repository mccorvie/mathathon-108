import BorelEnergy.Gaussian
import Apery.Kernel

/-! E223/U28, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
General product-measure adaptation of prior Apery/EnergyLimit.lean:36-62 (original line numbering).
Explicit diagonal nullness is essential because Real.log 0=0. Whole E201 remains CONJECTURE. -/
noncomputable section
namespace U28
open MeasureTheory Real Set Filter Topology

def logPair (μ ν : Measure ℝ) : ℝ :=
  ∫ p : ℝ×ℝ,Real.log |p.1-p.2| ∂μ.prod ν

def truncatedPair (μ ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ p : ℝ×ℝ,Apery.Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) |p.1-p.2| ∂μ.prod ν

/-- PROOF-DRAFT: arbitrary product-measure limit, with diagonal nullness stated explicitly. -/
theorem truncatedPair_tendsto (μ ν : Measure ℝ)
    (hint : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod ν))
    (hdiag : ∀ᵐ p ∂μ.prod ν,p.1≠p.2) :
    Tendsto (truncatedPair μ ν) atTop (𝓝 (logPair μ ν)) := by
  have hn (n : ℕ) : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  have hn' (n : ℕ) : 1/((n:ℝ)+1)≤(n:ℝ)+1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold truncatedPair logPair
  refine tendsto_integral_of_dominated_convergence
    (fun p : ℝ×ℝ=>|Real.log (|p.1-p.2|)|) ?_ hint.abs ?_ ?_
  · intro n
    exact ((Apery.continuous_Ltr (hn n) (hn' n)).comp
      (by fun_prop : Continuous (fun p : ℝ×ℝ=>|p.1-p.2|))).aestronglyMeasurable
  · intro n
    filter_upwards [hdiag] with p hp
    rw [Real.norm_eq_abs]
    exact Apery.abs_Ltr_le (hn n) (hn' n) (abs_pos.mpr (sub_ne_zero.mpr hp))
  · filter_upwards [hdiag] with p hp
    exact Apery.tendsto_Ltr (abs_pos.mpr (sub_ne_zero.mpr hp))

/-- PROOF-DRAFT: the actual nested Borel energy agrees with the product-measure notation. -/
theorem logPair_eq_nested (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hint : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod ν)) :
    logPair μ ν=(∫ x,∫ y,Real.log |x-y| ∂ν ∂μ) := by
  exact integral_prod _ hint

end U28
#print axioms U28.truncatedPair_tendsto
#print axioms U28.logPair_eq_nested
