import GramStatement

/-!
B11/E413: actual GS/DeltaS Gram positivity, Codex lane B. PROOF-DRAFT until gate.
Adapted from mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/Positivity.lean:117-221 (Firsching; Paul-Lez), Apache-2.0.
All shape parameters are symbolic; actual lane-L matrices and B6/B9 density retained.
No energy, normalizer-growth or irrationality claim is made here.
-/
open MeasureTheory Set Filter Topology Polynomial Finset AperyS
open scoped Matrix
namespace BAnalyticGram

lemma gramWeight_pos (s ν K N : ℕ) {y : ℝ} (hy : 0 < y) :
    0 < gramWeight s ν K N y := by
  unfold gramWeight
  have h1 := aeval_D_pos N (t := y ^ 2) (by positivity)
  have h2 := aeval_D_pos K (t := y ^ 2) (by positivity)
  have h3 := BAnalyticMoments.w_pos s hy
  positivity

lemma integrand_eq (s ν K N : ℕ) (i j : ℕ) (y : ℝ) :
    BAnalyticFunctional.integrand s K (D N ^ ν * X ^ (i + j)) y =
      (y ^ 2) ^ i * (y ^ 2) ^ j * gramWeight s ν K N y := by
  simp only [BAnalyticFunctional.integrand, gramWeight, map_mul, map_pow, aeval_X]
  rw [pow_add]
  ring

/-- Actual GS entries are integrable Gram entries, with no representation premise. -/
theorem gram_entry (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) (i j : Fin h) :
    IntegrableOn (fun y : ℝ => (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * gramWeight s ν K N y) (Ioi 0) ∧
      aeval (BAnalyticPoles.zetaS s) (GS s ν K N h i j) =
        ∫ y in Ioi 0, (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * gramWeight s ν K N y := by
  have hr := BAnalyticFunctional.moment_rep s hs K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ)))
  constructor
  · exact hr.1.congr_fun (fun y _ => integrand_eq s ν K N i j y) measurableSet_Ioi
  · simpa only [GS] using hr.2.trans
      (setIntegral_congr_fun measurableSet_Ioi (fun y _ => integrand_eq s ν K N i j y))

/-- Positivity of the actual determinant for every natural size, including h=0. -/
theorem delta_pos (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) :
    0 < aeval (BAnalyticPoles.zetaS s) (ΔS s ν K N h) := by
  have hdet : aeval (BAnalyticPoles.zetaS s) (ΔS s ν K N h) = ((GS s ν K N h).map (aeval (BAnalyticPoles.zetaS s))).det := by
    have := RingHom.map_det (aeval (BAnalyticPoles.zetaS s) : ℚ[X] →ₐ[ℚ] ℝ).toRingHom (GS s ν K N h)
    simpa [ΔS, RingHom.mapMatrix_apply] using this
  rw [hdet]
  set M : Matrix (Fin h) (Fin h) ℝ := (GS s ν K N h).map (aeval (BAnalyticPoles.zetaS s)) with hM
  have hentry : ∀ i j : Fin h, M i j =
      ∫ y in Ioi 0, BAnalyticFunctional.integrand s K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ))) y :=
    fun i j => (BAnalyticFunctional.moment_rep s hs K _).2
  have hint : ∀ i j : Fin h,
      IntegrableOn (BAnalyticFunctional.integrand s K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ)))) (Ioi 0) :=
    fun i j => (BAnalyticFunctional.moment_rep s hs K _).1
  apply Matrix.PosDef.det_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, hM, Matrix.map_apply, GS]
    rw [Nat.add_comm (j : ℕ) i]
  · intro x hx
    set f : Fin h → Fin h → ℝ → ℝ := fun i j y =>
      x i * x j * BAnalyticFunctional.integrand s K (D N ^ ν * X ^ ((i : ℕ) + (j : ℕ))) y with hf
    have hfint : ∀ i j, IntegrableOn (f i j) (Ioi 0) := fun i j => (hint i j).const_mul _
    have hpt : ∀ y, ∑ i, ∑ j, f i j y = (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y := by
      intro y
      simp only [hf, integrand_eq]
      rw [sq (∑ i, x i * (y ^ 2) ^ (i : ℕ)), Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hq : star x ⬝ᵥ (M *ᵥ x) = ∫ y in Ioi 0, (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y := by
      have h1 : star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, ∫ y in Set.Ioi 0, f i j y := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, hentry, hf, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]; ring
      rw [h1]
      have h2 : ∀ i, ∑ j, ∫ y in Set.Ioi 0, f i j y = ∫ y in Set.Ioi 0, ∑ j, f i j y :=
        fun i => (integral_finsetSum _ (fun j _ => hfint i j)).symm
      simp_rw [h2]
      rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfint i j))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y)
    rw [hq]
    have hsq : IntegrableOn (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y) (Ioi 0) := by
      have : (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y) = fun y => ∑ i, ∑ j, f i j y :=
        funext fun y => (hpt y).symm
      rw [this]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hfint i j
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
      exact mul_nonneg (sq_nonneg _) (gramWeight_pos s ν K N hy).le
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hsq]
    set q : ℝ[X] := ∑ i : Fin h, C (x i) * X ^ (i : ℕ) with hqdef
    have hqeval : ∀ y : ℝ, q.eval (y ^ 2) = ∑ i, x i * (y ^ 2) ^ (i : ℕ) := by
      intro y; simp [hqdef, eval_finsetSum]
    have hq0 : q ≠ 0 := by
      intro h0
      apply hx
      funext i
      have hc : q.coeff (i : ℕ) = x i := by
        simp only [hqdef, finsetSum_coeff, coeff_C_mul_X_pow]
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h.symm)
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← hc, h0, coeff_zero]; rfl
    have hroots : Set.Finite {t : ℝ | IsRoot q t} := Polynomial.finite_setOfPred_isRoot hq0
    have hB : Set.Finite {y : ℝ | IsRoot q (y ^ 2)} := by
      refine (hroots.image Real.sqrt |>.union (hroots.image fun t => -Real.sqrt t)).subset ?_
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy
      rcases le_or_gt 0 y with h | h
      · exact Or.inl ⟨y ^ 2, hy, Real.sqrt_sq h⟩
      · exact Or.inr ⟨y ^ 2, hy, by
          show -Real.sqrt (y ^ 2) = y
          rw [Real.sqrt_sq_eq_abs, abs_of_neg h, neg_neg]⟩
    have hsub : Set.Ioi 0 \ {y : ℝ | IsRoot q (y ^ 2)} ⊆
        Function.support (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * gramWeight s ν K N y) ∩ Set.Ioi 0 := by
      intro y hy
      obtain ⟨hy0, hyB⟩ := hy
      refine ⟨?_, hy0⟩
      simp only [Function.mem_support]
      have hqy : q.eval (y ^ 2) ≠ 0 := fun h => hyB h
      rw [hqeval] at hqy
      exact mul_ne_zero (pow_ne_zero _ hqy) (gramWeight_pos s ν K N hy0).ne'
    calc (0 : ENNReal) < ⊤ := ENNReal.zero_lt_top
      _ = volume (Set.Ioi (0 : ℝ) \ {y : ℝ | IsRoot q (y ^ 2)}) := by
        rw [measure_sdiff_null (hB.measure_zero volume), Real.volume_Ioi]
      _ ≤ _ := measure_mono hsub

/-- The exact posted Gram-entry target. -/
theorem gram_entry_statement : GramEntryStatement := by
  intro s hs ν K N h i j
  exact gram_entry s hs ν K N h i j

/-- The exact posted positivity target, with no h>0 restriction. -/
theorem gram_positive_statement : GramPositiveStatement := by
  intro s hs ν K N h
  exact delta_pos s hs ν K N h

#print axioms BAnalyticGram.gramWeight_pos
#print axioms BAnalyticGram.gram_entry
#print axioms BAnalyticGram.delta_pos
#print axioms BAnalyticGram.gram_entry_statement
#print axioms BAnalyticGram.gram_positive_statement
end BAnalyticGram
