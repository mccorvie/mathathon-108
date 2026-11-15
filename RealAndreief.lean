import Apery.Andreief
/- Author Codex GPT-6 U52/E247. PROOF-DRAFT.
Adapted lane-B E414/E415 reductions, themselves Firsching mo271/Zeta5@be1c0d82;
Fauzan re-derivation; Comparator metadata Paul-Lez; Apache-2.0. See source-map.json. -/
open MeasureTheory Finset Equiv
namespace U52.Det.Generic
variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
/-- The full determinant-product integrand is integrable; no extra premise beyond pair moments.
The proof extracts the finite-expansion integrability argument used inside upstream andreief. -/
theorem integrable_det_mul (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ) :
    Integrable (fun x : Fin n → ℝ =>
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det)
      (Measure.pi fun _ : Fin n => μ) := by
  have hint : ∀ σ τ : Perm (Fin n), Integrable
      (fun x : Fin n → ℝ => (Perm.sign σ : ℝ) * (Perm.sign τ : ℝ) *
        ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i)))) (Measure.pi fun _ : Fin n => μ) := by
    intro σ τ
    have : (fun x : Fin n → ℝ => (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) =
        fun x => ∏ i, (fun i y => f (σ i) y * g (τ i) y) i (x i) := by
      funext x; simp only [← Finset.prod_mul_distrib]
    refine Integrable.const_mul ?_ _
    rw [this]
    exact Integrable.fintype_prod fun i => hfg (σ i) (τ i)
  have hpt : ∀ x : Fin n → ℝ,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ τ : Perm (Fin n), ∑ σ : Perm (Fin n), (Perm.sign σ : ℝ) * (Perm.sign τ : ℝ) *
        ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) := by
    intro x
    rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply]
    ring
  exact (integrable_finsetSum _ (fun τ _ => integrable_finsetSum _ (fun σ _ => hint σ τ))).congr
    (Filter.Eventually.of_forall fun x => (hpt x).symm)
end U52.Det.Generic
