/- Author Codex GPT-6 U52/E247. PROOF-DRAFT.
Adapted lane-B E414/E415 reductions, themselves Firsching mo271/Zeta5@be1c0d82;
Fauzan re-derivation; Comparator metadata Paul-Lez; Apache-2.0. See source-map.json. -/
import RealPointwise

/-!
E414 conditional analytic staging, Codex lane B. PROOF-DRAFT until gate.
Adapted from mo271/Zeta5@be1c0d82 Apery/EnergyBound.lean:243-303,
Firsching; Paul-Lez, Apache-2.0. Uses actual E415 determinant integral and B5.
The only energy input is the unchanged named configuration statement.
-/
open MeasureTheory Set Filter Topology Polynomial Finset Apery
namespace U52

lemma Kr_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ Kr n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Kr]
  linarith

lemma C_pos (s : ℕ) : 0 < BAnalyticIntegral.C s (2 * Real.pi) := by
  unfold BAnalyticIntegral.C
  positivity

lemma integrableOn_gK (s n : ℕ) (hn : 1 ≤ n) : IntegrableOn (gK s n) (Ioi 0) := by
  change IntegrableOn (BAnalyticIntegral.g s (2 * Real.pi) (Kr n)) (Ioi 0)
  exact BAnalyticIntegral.integrableOn_g s
    (by linarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi) (Kr_ge_one n hn)

lemma integral_gK_le (s n : ℕ) (hn : 1 ≤ n) :
    (∫ y in Ioi 0, gK s n y) ≤ BAnalyticIntegral.C s (2 * Real.pi) * (Kr n) ^ (s + 1) := by
  simpa only [gK, BAnalyticIntegral.g] using BAnalyticIntegral.integral_g_le s
    (by linarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi) (Kr_ge_one n hn)

lemma integral_gK_nonneg (s n : ℕ) : 0 ≤ ∫ y in Ioi 0, gK s n y := by
  refine setIntegral_nonneg measurableSet_Ioi fun y hy => ?_
  have hy : 0 < y := hy
  unfold gK
  positivity

/-- Finite actual-determinant bound, conditional solely on the posted configuration inequality. -/
theorem log_delta_le {T : ℝ} (hConfig : U48.ConfigurationStatement T)
    (s : ℕ) (hs : 2 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (aeval (BAnalyticPoles.zetaS s) (AperyS.ΔS s 6 (40 * n) (3 * n) (37 * n))) ≤
      Aconst T n + ((37 * n : ℕ) : ℝ) *
        (Real.log (BAnalyticIntegral.C s (2 * Real.pi)) + ((s : ℝ) + 1) * Real.log (Kr n)) := by
  have hK : 0 < Kr n := lt_of_lt_of_le (by norm_num) (Kr_ge_one n hn)
  have hC : 0 < BAnalyticIntegral.C s (2 * Real.pi) := C_pos s
  have hΔ := BAnalyticGram.delta_pos s hs 6 (40 * n) (3 * n) (37 * n)
  set I : ℝ := ∫ x : Fin (37 * n) → ℝ,
      U52.Det.detIntegrand s 6 (40 * n) (3 * n) (37 * n) x
        ∂(Measure.pi fun _ : Fin (37 * n) => volume.restrict (Ioi 0)) with hI
  have hdetI : aeval (BAnalyticPoles.zetaS s) (AperyS.ΔS s 6 (40 * n) (3 * n) (37 * n)) =
      (1 / ((37 * n).factorial : ℝ)) * I :=
    (U52.Det.determinant_rep s hs 6 (40 * n) (3 * n) (37 * n)).2
  rw [hdetI] at hΔ ⊢
  have hfac : 0 < ((37 * n).factorial : ℝ) := by positivity
  have hIpos : 0 < I := by
    by_contra hneg
    push_neg at hneg
    have hnonpos : (1 / ((37 * n).factorial : ℝ)) * I ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hgint := integrableOn_gK s n hn
  have hg0 := integral_gK_nonneg s n
  have hg1 := integral_gK_le s n hn
  have hae : ∀ᵐ (x : Fin (37 * n) → ℝ) ∂(Measure.pi fun _ : Fin (37 * n) => volume.restrict (Ioi 0)),
      (∀ i, 0 < x i) ∧ Function.Injective x := by
    simpa only [Apery.μpos] using Apery.ae_pos_injective (37 * n)
  have hleft : Integrable (U52.Det.detIntegrand s 6 (40 * n) (3 * n) (37 * n))
      (Measure.pi fun _ : Fin (37 * n) => volume.restrict (Ioi 0)) :=
    (U52.Det.determinant_rep s hs 6 (40 * n) (3 * n) (37 * n)).1
  have hright := (Integrable.fintype_prod (fun _ : Fin (37 * n) => hgint)).const_mul (Real.exp (Aconst T n))
  have hcomparison : ∀ᵐ x ∂(Measure.pi fun _ : Fin (37 * n) => volume.restrict (Ioi 0)),
      U52.Det.detIntegrand s 6 (40 * n) (3 * n) (37 * n) x ≤
        Real.exp (Aconst T n) * ∏ i, gK s n (x i) := by
    filter_upwards [hae] with x hx
    simpa only [U52.Det.detIntegrand] using integrand_le hConfig s hs n hn x hx.1 hx.2
  have hbound : I ≤ Real.exp (Aconst T n) * (∫ y in Ioi 0, gK s n y) ^ (37 * n) := by
    calc I ≤ ∫ x : Fin (37 * n) → ℝ, Real.exp (Aconst T n) * ∏ i, gK s n (x i)
        ∂(Measure.pi fun _ : Fin (37 * n) => volume.restrict (Ioi 0)) :=
      integral_mono_ae hleft hright hcomparison
      _ = _ := by
        rw [integral_const_mul, integral_fintype_prod_eq_prod (fun _ => gK s n),
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlog1 : Real.log ((1 / ((37 * n).factorial : ℝ)) * I) ≤ Real.log I := by
    rw [Real.log_mul (by positivity) hIpos.ne']
    have hnonpos : Real.log (1 / ((37 * n).factorial : ℝ)) ≤ 0 := by
      rw [one_div, Real.log_inv]
      have hfac1 : (1 : ℝ) ≤ ((37 * n).factorial : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (37 * n)))
      linarith [Real.log_nonneg hfac1]
    linarith
  refine hlog1.trans ?_
  calc Real.log I ≤ Real.log (Real.exp (Aconst T n) *
      (BAnalyticIntegral.C s (2 * Real.pi) * Kr n ^ (s + 1)) ^ (37 * n)) := by
        apply Real.log_le_log hIpos
        exact hbound.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hg0 hg1 (37 * n)) (Real.exp_pos _).le)
    _ = _ := by
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
        Real.log_mul hC.ne' (by positivity), Real.log_pow]
      push_cast
      ring
end U52
