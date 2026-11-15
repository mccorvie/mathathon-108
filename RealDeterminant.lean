/- Author Codex GPT-6 U52/E247. PROOF-DRAFT.
Adapted lane-B E414/E415 reductions, themselves Firsching mo271/Zeta5@be1c0d82;
Fauzan re-derivation; Comparator metadata Paul-Lez; Apache-2.0. See source-map.json. -/
import RealDetStatement
import RealAndreief

/-!
B13/E415: actual determinant as a multivariate integral, Codex lane B.
PROOF-DRAFT until repository gate. Adapted from mo271/Zeta5@be1c0d82,
Apery/DetIntegral.lean:20-57, Firsching; Paul-Lez, Apache-2.0 (NOTICE/LICENSE).
All parameters symbolic; actual GS/DeltaS, zetaS and gramWeight imported unchanged.
No matrix-representation or integrability premise, no energy bound.
-/
open MeasureTheory Set Filter Topology Polynomial Finset AperyS
namespace U52.Det

/-- Integrability plus the exact Andreief representation of the actual determinant. -/
theorem determinant_rep (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) :
    Integrable (detIntegrand s ν K N h) (Measure.pi fun _ : Fin h => μpos) ∧
      aeval (BAnalyticPoles.zetaS s) (ΔS s ν K N h) =
        (1 / (h.factorial : ℝ)) *
          ∫ x : Fin h → ℝ, detIntegrand s ν K N h x ∂(Measure.pi fun _ : Fin h => μpos) := by
  have hdet : aeval (BAnalyticPoles.zetaS s) (ΔS s ν K N h) =
      ((GS s ν K N h).map (aeval (BAnalyticPoles.zetaS s))).det := by
    have hh := RingHom.map_det (aeval (BAnalyticPoles.zetaS s) : ℚ[X] →ₐ[ℚ] ℝ).toRingHom
      (GS s ν K N h)
    simpa [ΔS, RingHom.mapMatrix_apply] using hh
  set f : Fin h → ℝ → ℝ := fun i y => (y ^ 2) ^ (i : ℕ) with hf
  set g : Fin h → ℝ → ℝ := fun j y => (y ^ 2) ^ (j : ℕ) * BAnalyticGram.gramWeight s ν K N y with hg
  have hentry : (GS s ν K N h).map (aeval (BAnalyticPoles.zetaS s)) =
      Matrix.of fun i j => ∫ y, f i y * g j y ∂μpos := by
    ext i j
    have hh := (BAnalyticGram.gram_entry s hs ν K N h i j).2
    simpa only [Matrix.map_apply, Matrix.of_apply, hf, hg, mul_assoc] using hh
  have hfg : ∀ i j, Integrable (fun y => f i y * g j y) μpos := by
    intro i j
    have hh := (BAnalyticGram.gram_entry s hs ν K N h i j).1
    simpa only [μpos, MeasureTheory.IntegrableOn, hf, hg, mul_assoc] using hh
  have hpt : ∀ x : Fin h → ℝ,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
        detIntegrand s ν K N h x := by
    intro x
    have h1 : (Matrix.of fun i j => f i (x j)).det =
        (Matrix.vandermonde fun j => x j ^ 2).det := by
      rw [← Matrix.det_transpose (Matrix.vandermonde _)]
      refine congrArg Matrix.det ?_
      ext i j; simp [hf, Matrix.vandermonde, Matrix.transpose_apply]
    have h2 : (Matrix.of fun i j => g i (x j)).det =
        (∏ j, BAnalyticGram.gramWeight s ν K N (x j)) *
          (Matrix.vandermonde fun j => x j ^ 2).det := by
      have hh : (Matrix.of fun i j => g i (x j)) =
          Matrix.of fun i j => BAnalyticGram.gramWeight s ν K N (x j) *
            (Matrix.of fun i j => f i (x j)) i j := by
        ext i j; simp [hf, hg]; ring
      rw [hh, Matrix.det_mul_row, h1]
    unfold detIntegrand
    rw [h1, h2]
    ring
  constructor
  · exact (Generic.integrable_det_mul f g hfg).congr (Filter.Eventually.of_forall hpt)
  · rw [hdet, hentry, Apery.andreief f g hfg]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- Full multivariate integrability with the requested literal Vandermonde integrand. -/
theorem det_integrable (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) :
    Integrable (fun x : Fin h → ℝ =>
      (Matrix.vandermonde fun j => x j ^ 2).det ^ 2 * ∏ j, BAnalyticGram.gramWeight s ν K N (x j))
      (Measure.pi fun _ : Fin h => volume.restrict (Ioi 0)) :=
  (determinant_rep s hs ν K N h).1

/-- Exact multiple integral formula, including h=0, for actual DeltaS at actual zetaS. -/
theorem delta_eq_integral (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) :
    aeval (BAnalyticPoles.zetaS s) (ΔS s ν K N h) =
      (1 / (h.factorial : ℝ)) *
        ∫ x : Fin h → ℝ, (Matrix.vandermonde fun j => x j ^ 2).det ^ 2 *
          ∏ j, BAnalyticGram.gramWeight s ν K N (x j)
            ∂(Measure.pi fun _ : Fin h => volume.restrict (Ioi 0)) :=
  (determinant_rep s hs ν K N h).2

/-- The exact target posted before proof. -/
theorem determinant_statement : DeterminantStatement := by
  intro s hs ν K N h
  exact determinant_rep s hs ν K N h

end U52.Det
