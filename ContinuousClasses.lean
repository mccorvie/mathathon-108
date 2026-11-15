import ClassSums
import ModelAlgebra

/- E420 Codex inner_explicit. PROOF-DRAFT continuous class-count dictionary.
Definitions iv/cv and bcoef are the namespace-only Apache Zeta5 ClassSum copy.
These elementary integral identities connect that finite estimate to actual
integrals; they are not the complete explicitallocation cost bridge.
-/

open MeasureTheory Set Finset
namespace BInnerExplicit.ContinuousClasses
noncomputable section
open BInnerExplicit.ClassSums

def aCount (f z : ℝ) : ℕ :=
  (if z ≤ f then 1 else 0) + (if 1 - f ≤ z then 1 else 0)

def cvInd (f : ℝ) (i : Fin 3) : ℝ → ℝ :=
  (Set.Icc (cvLo f i) (cvHi f i)).indicator (fun _ => 1)

/-- PROOF-DRAFT: continuous counterpart of the exact imported expand_one. -/
lemma expand_one (f z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (h : ℕ → ℝ) :
    h (aCount f z) = ∑ i, bcoef h i * cvInd f i z := by
  have hz1' : z ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using hz1
  simp only [Fin.sum_univ_three, bcoef, cvInd, cvLo, cvHi, aCount,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Set.indicator, Set.mem_Icc]
  by_cases h1 : z ≤ f <;> by_cases h2 : 1 - f ≤ z
  · simp [h1, h2, hz0, hz1']
  · simp [h1, h2, hz0, hz1']
  · exfalso
    linarith
  · simp [h1, h2, hz0, hz1']

/-- PROOF-DRAFT: both floor-count variables expand into nine intersections. -/
lemma expand_two (f g z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (h : ℕ → ℕ → ℝ) :
    h (aCount f z) (aCount g z) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * (cvInd f i z * cvInd g j z) := by
  rw [expand_one f z hz0 hz1 (fun a => h a (aCount g z))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ a, h a (aCount g z) = ∑ j, bcoef (fun b => h a b) j * cvInd g j z :=
    fun a => expand_one g z hz0 hz1 (fun b => h a b)
  simp only [e, bcoef, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i <;> simp <;> ring

/-- PROOF-DRAFT: actual interval integral of an indicator intersection. -/
lemma integral_cvInd_mul (f g : ℝ) (i j : Fin 3) :
    ∫ z in (0 : ℝ)..(1 / 2), cvInd f i z * cvInd g j z = ccount f g i j := by
  let a := max (cvLo f i) (cvLo g j)
  let b := min (cvHi f i) (cvHi g j)
  have heq : (fun z => cvInd f i z * cvInd g j z) =
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) := by
    funext z
    have hmem : z ∈ Set.Icc a b ↔
        z ∈ Set.Icc (cvLo f i) (cvHi f i) ∧ z ∈ Set.Icc (cvLo g j) (cvHi g j) := by
      simp only [Set.mem_Icc, a, b, max_le_iff, le_min_iff]
      tauto
    by_cases h1 : z ∈ Set.Icc (cvLo f i) (cvHi f i) <;>
      by_cases h2 : z ∈ Set.Icc (cvLo g j) (cvHi g j) <;>
      simp [cvInd, Set.indicator, hmem, h1, h2]
  rw [heq, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hinter : Set.Icc (0 : ℝ) (1 / 2) ∩ Set.Icc a b = Set.Icc (max a 0) (min b (1 / 2)) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Icc, max_le_iff, le_min_iff]
    tauto
  rw [hinter, MeasureTheory.setIntegral_const, Real.volume_real_Icc]
  simp only [smul_eq_mul, mul_one]
  dsimp [ccount, a, b]
  exact max_comm _ _

/-- PROOF-DRAFT: all nine continuous class terms are interval integrable. -/
lemma intervalIntegrable_cvInd_mul (f g : ℝ) (i j : Fin 3) :
    IntervalIntegrable (fun z => cvInd f i z * cvInd g j z) volume 0 (1 / 2) := by
  have hm1 : AEStronglyMeasurable (cvInd f i) (volume.restrict (Set.Icc (0 : ℝ) (1 / 2))) := by
    exact aestronglyMeasurable_const.indicator measurableSet_Icc
  have hm2 : AEStronglyMeasurable (cvInd g j) (volume.restrict (Set.Icc (0 : ℝ) (1 / 2))) := by
    exact aestronglyMeasurable_const.indicator measurableSet_Icc
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 (1 / 2)) :=
    integrableOn_const (by simp)
  have hi : IntegrableOn (fun z => cvInd f i z * cvInd g j z) (Set.Icc 0 (1 / 2)) := by
    refine hc.mono' (hm1.mul hm2) (Filter.Eventually.of_forall fun z => ?_)
    unfold cvInd
    simp only [Set.indicator]
    split_ifs <;> norm_num
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hi

/-- PROOF-DRAFT: the imported nine-coefficient continuous count is an actual
interval integral, for every finite table of class values. -/
lemma class_integral (f g : ℝ) (h : ℕ → ℕ → ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), h (aCount f z) (aCount g z) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * ccount f g i j := by
  have hint (i j : Fin 3) : IntervalIntegrable
      (fun z => bcoef (fun a => bcoef (fun b => h a b) j) i *
        (cvInd f i z * cvInd g j z)) volume 0 (1 / 2) :=
    (intervalIntegrable_cvInd_mul f g i j).const_mul _
  have heq : Set.EqOn
      (fun z => h (aCount f z) (aCount g z))
      (fun z => ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        (cvInd f i z * cvInd g j z)) (Set.uIcc (0 : ℝ) (1 / 2)) := by
    intro z hz
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hz
    exact expand_two f g z hz.1 hz.2 h
  have hrow (i : Fin 3) : IntervalIntegrable
      (fun z => ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        (cvInd f i z * cvInd g j z)) volume 0 (1 / 2) := by
    simpa only [Fin.sum_univ_three] using ((hint i 0).add (hint i 1)).add (hint i 2)
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_finsetSum (fun i _ => hrow i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cvInd_mul]

/-- PROOF-DRAFT: finite ordinary-class sum versus an actual continuous
integral. Error depends only on its nine table coefficients, not p. -/
theorem finite_class_integral_approx {p m v v' : ℕ}
    (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (ClassSums.aCnt p v c) (ClassSums.aCnt p v' c) -
        (p : ℝ) * ∫ z in (0 : ℝ)..(1 / 2),
          h (aCount ((v : ℝ) / p) z) (aCount ((v' : ℝ) / p) z)| ≤
      5 / 2 * ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| := by
  rw [class_integral]
  exact class_sum_approx hm hv hv' h

end
end BInnerExplicit.ContinuousClasses
