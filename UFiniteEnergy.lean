import FiniteMatrix
import Apery.EnergyLimit

/-!
E208 / U13, Codex, 2026-11-14, event work.
CONJECTURE: complete candidate proofs; parent gate and human comparison pending.
The zero-mass theorem is PRIOR WORK, copied with attribution in Apery/EnergyLimit.lean.
Only finite systems of continuous curves are covered. No Borel-measure theorem is asserted.
-/

noncomputable section

namespace Mathathon.P108.FiniteDuality

open Finset MeasureTheory Real

variable {ι : Type*} [Fintype ι]

/-- Normalized pair logarithmic energy of the explicit parametrized curves. -/
def curveKernel (gamma : ι → ℝ → ℂ) (i j : ι) : ℝ :=
  Apery.pairInt gamma (fun z w => Real.log ‖z - w‖) i j / (2 * Real.pi) ^ 2

-- CONJECTURE (parent gate/human comparison pending): exact finite-sum normalization.
theorem quadratic_curveKernel (gamma : ι → ℝ → ℂ) (w : ι → ℝ) :
    quadratic (curveKernel gamma) w =
      Apery.energy w gamma (fun z w => Real.log ‖z - w‖) / (2 * Real.pi) ^ 2 := by
  classical
  unfold quadratic bilinear curveKernel Apery.energy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

-- CONJECTURE (parent gate/human comparison pending): symmetry proved by product-measure swap.
omit [Fintype ι] in
theorem curveKernel_symm (gamma : ι → ℝ → ℂ)
    (hint : ∀ i j, Integrable
      (fun p : ℝ × ℝ => Real.log ‖gamma i p.1 - gamma j p.2‖)
      (Apery.μcirc.prod Apery.μcirc)) (i j : ι) :
    curveKernel gamma i j = curveKernel gamma j i := by
  unfold curveKernel
  congr 1
  rw [Apery.pairInt_eq_prod gamma _ i j (hint i j),
    Apery.pairInt_eq_prod gamma _ j i (hint j i)]
  calc
    _ = ∫ p : ℝ × ℝ, Real.log ‖gamma j p.2 - gamma i p.1‖
        ∂(Apery.μcirc.prod Apery.μcirc) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp
        rw [norm_sub_rev]
    _ = _ := integral_prod_swap
      (fun p : ℝ × ℝ => Real.log ‖gamma j p.1 - gamma i p.2‖)

-- CONJECTURE (parent gate/human comparison pending): zero-mass negativity is derived, not assumed.
theorem curve_quadratic_nonpos (gamma : ι → ℝ → ℂ)
    (hgamma : ∀ i, Continuous (gamma i)) {R : ℝ}
    (hR : ∀ i theta, ‖gamma i theta‖ ≤ R) (w : ι → ℝ) (hmass : ∑ i, w i = 0)
    (hint : ∀ i j, Integrable
      (fun p : ℝ × ℝ => Real.log ‖gamma i p.1 - gamma j p.2‖)
      (Apery.μcirc.prod Apery.μcirc))
    (hae : ∀ i j, ∀ᵐ p ∂(Apery.μcirc.prod Apery.μcirc), gamma i p.1 ≠ gamma j p.2) :
    quadratic (curveKernel gamma) w ≤ 0 := by
  rw [quadratic_curveKernel]
  exact div_nonpos_of_nonpos_of_nonneg
    (Apery.energy_log_nonpos hgamma hR hmass hint hae) (sq_nonneg _)

-- CONJECTURE (parent gate/human comparison pending): finite-curve weak duality with explicit premises.
theorem finite_curve_weak_duality (gamma : ι → ℝ → ℂ)
    (hgamma : ∀ i, Continuous (gamma i)) {R : ℝ}
    (hR : ∀ i theta, ‖gamma i theta‖ ≤ R)
    (hint : ∀ i j, Integrable
      (fun p : ℝ × ℝ => Real.log ‖gamma i p.1 - gamma j p.2‖)
      (Apery.μcirc.prod Apery.μcirc))
    (hae : ∀ i j, ∀ᵐ p ∂(Apery.μcirc.prod Apery.μcirc), gamma i p.1 ≠ gamma j p.2)
    (a b V : ι → ℝ) (lam M : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hma : ∑ i, a i = lam) (hmb : ∑ i, b i = lam)
    (hpotential : ∀ i, 2 * (∑ j, b j * curveKernel gamma i j) - V i ≤ M) :
    quadratic (curveKernel gamma) a - (∑ i, a i * V i) ≤
      lam * M - quadratic (curveKernel gamma) b := by
  have hmass : ∑ i, (a i - b i) = 0 := by
    rw [Finset.sum_sub_distrib, hma, hmb]
    ring
  exact matrix_weak_duality (curveKernel gamma) (curveKernel_symm gamma hint)
    a b V lam M ha hma
    (curve_quadratic_nonpos gamma hgamma hR (fun i => a i - b i) hmass hint hae)
    hpotential

end Mathathon.P108.FiniteDuality

#print axioms Mathathon.P108.FiniteDuality.finite_curve_weak_duality
#print axioms Mathathon.P108.FiniteDuality.curve_quadratic_nonpos
#print axioms Mathathon.P108.FiniteDuality.curveKernel_symm
#print axioms Apery.energy_log_nonpos
