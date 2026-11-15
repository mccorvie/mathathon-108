import Mathathon.P108.InnerShift
import Mathlib.MeasureTheory.Integral.Prod

/-!
# #108: `x ↦ R_(s,ν)(x)/x³` is interval integrable on `[3, M]` (EVENT WORK)

Formalizer (Claude Opus 5.5), Fri Nov 13 2026. Discharges the hypothesis `hint` of
`inner_crude_sstep` / `thetaPkg_sstep`: `R_(s,ν)` is measurable (the `z`-integral by
`StronglyMeasurable.integral_prod_right'`) and bounded on `[3, M]` (every floor is within 1 of its
argument), hence `R/x³` is integrable there, for all real `s, ν, α`.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-- `f` is bounded in absolute value on `S`. -/
def BddOn {X : Type*} (f : X → ℝ) (S : Set X) : Prop := ∃ C, ∀ x ∈ S, |f x| ≤ C

section
variable {X : Type*} {S : Set X} {f g : X → ℝ}

lemma bdd_const (c : ℝ) : BddOn (fun _ : X => c) S := ⟨|c|, fun _ _ => le_refl _⟩

lemma bdd_add (hf : BddOn f S) (hg : BddOn g S) : BddOn (fun x => f x + g x) S := by
  obtain ⟨C1, h1⟩ := hf; obtain ⟨C2, h2⟩ := hg
  exact ⟨C1 + C2, fun x hx => (abs_add_le _ _).trans (add_le_add (h1 x hx) (h2 x hx))⟩

lemma bdd_neg (hf : BddOn f S) : BddOn (fun x => -f x) S := by
  obtain ⟨C, h⟩ := hf
  exact ⟨C, fun x hx => by rw [abs_neg]; exact h x hx⟩

lemma bdd_sub (hf : BddOn f S) (hg : BddOn g S) : BddOn (fun x => f x - g x) S := by
  have := bdd_add hf (bdd_neg hg)
  simpa [sub_eq_add_neg] using this

lemma bdd_mul (hf : BddOn f S) (hg : BddOn g S) : BddOn (fun x => f x * g x) S := by
  obtain ⟨C1, h1⟩ := hf; obtain ⟨C2, h2⟩ := hg
  refine ⟨C1 * C2, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h1 x hx) (h2 x hx) (abs_nonneg _) ((abs_nonneg _).trans (h1 x hx))

lemma bdd_div_const (hf : BddOn f S) (c : ℝ) : BddOn (fun x => f x / c) S := by
  have := bdd_mul hf (bdd_const (S := S) c⁻¹)
  simpa [div_eq_mul_inv] using this

lemma abs_floor_le (a : ℝ) : |((⌊a⌋ : ℤ) : ℝ)| ≤ |a| + 1 := by
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := le_abs_self a
  have h4 := neg_abs_le a
  rw [abs_le]; constructor <;> linarith

lemma bdd_floor (hf : BddOn f S) : BddOn (fun x => ((⌊f x⌋ : ℤ) : ℝ)) S := by
  obtain ⟨C, h⟩ := hf
  exact ⟨C + 1, fun x hx => (abs_floor_le _).trans (by linarith [h x hx])⟩

lemma bdd_max0 (hf : BddOn f S) : BddOn (fun x => max (f x) 0) S := by
  obtain ⟨C, h⟩ := hf
  refine ⟨C, fun x hx => le_trans ?_ (h x hx)⟩
  have h3 := le_abs_self (f x)
  have h4 := neg_abs_le (f x)
  rw [abs_le]
  constructor
  · linarith [le_max_right (f x) 0, abs_nonneg (f x)]
  · exact max_le h3 (abs_nonneg _)

end

lemma bdd_id (M : ℝ) (hM : 3 ≤ M) : BddOn (fun x : ℝ => x) (Icc 3 M) :=
  ⟨M, fun x hx => by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]⟩

lemma bdd_fst (M : ℝ) (hM : 3 ≤ M) :
    BddOn (fun p : ℝ × ℝ => p.1) (Icc 3 M ×ˢ Icc 0 (1/2)) :=
  ⟨M, fun p hp => by rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2]⟩

lemma bdd_snd (M : ℝ) :
    BddOn (fun p : ℝ × ℝ => p.2) (Icc 3 M ×ˢ Icc 0 (1/2)) :=
  ⟨1/2, fun p hp => by rw [abs_le]; constructor <;> linarith [hp.2.1, hp.2.2]⟩

/-- Combinator tactic for `BddOn` goals built from `+ - * /`, constants, floors and `max · 0`. -/
macro "bdd_tac" M:term "," hM:term : tactic => `(tactic| (
  repeat' (first
    | exact bdd_const _
    | exact bdd_id $M $hM
    | exact bdd_fst $M $hM
    | exact bdd_snd $M
    | assumption
    | apply bdd_add
    | apply bdd_sub
    | apply bdd_mul
    | apply bdd_neg
    | apply bdd_div_const
    | apply bdd_floor
    | apply bdd_max0)))

lemma bdd_gammaIntegrand (s ν α M : ℝ) (hM : 3 ≤ M) :
    BddOn (fun p : ℝ × ℝ => gammaIntegrand s ν α p.1 p.2) (Icc 3 M ×ˢ Icc 0 (1/2)) := by
  unfold gammaIntegrand Tc Hc ell
  bdd_tac M, hM

lemma bdd_gammaInt (s ν α M : ℝ) (hM : 3 ≤ M) :
    BddOn (fun x => ∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z) (Icc 3 M) := by
  obtain ⟨C, h⟩ := bdd_gammaIntegrand s ν α M hM
  refine ⟨C * |(1:ℝ)/2 - 0|, fun x hx => ?_⟩
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun z hz => ?_)
  rw [uIoc_of_le (by norm_num)] at hz
  rw [Real.norm_eq_abs]
  exact h (x, z) ⟨hx, ⟨hz.1.le, hz.2⟩⟩

lemma bdd_innerR (s ν α M : ℝ) (hM : 3 ≤ M) : BddOn (fun x => innerR s ν α x) (Icc 3 M) := by
  have hI := bdd_gammaInt s ν α M hM
  unfold innerR innerGamma innerN Jfun sigmaC Tc Hc nplus
  bdd_tac M, hM

lemma measurable_gammaInt (s ν α : ℝ) :
    Measurable (fun x => ∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z) := by
  have hG : Measurable (fun p : ℝ × ℝ => gammaIntegrand s ν α p.1 p.2) := by
    unfold gammaIntegrand Tc Hc ell; fun_prop
  have h := hG.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) (1/2)))
  have e : (fun x => ∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z)
      = fun x => ∫ z, gammaIntegrand s ν α x z ∂(volume.restrict (Ioc (0:ℝ) (1/2))) := by
    funext x; rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [e]; exact h.measurable

lemma measurable_innerR (s ν α : ℝ) : Measurable (fun x => innerR s ν α x) := by
  have hI := measurable_gammaInt s ν α
  unfold innerR innerGamma innerN Jfun sigmaC Tc Hc nplus
  fun_prop

/-- **`hint` holds**: for all real `s, ν, α` and `M ≥ 3`, `x ↦ R_(s,ν)(x)/x³` is interval integrable
on `[3, M]`. -/
theorem innerR_div_intervalIntegrable (s ν α M : ℝ) (hM : 3 ≤ M) :
    IntervalIntegrable (fun x => innerR s ν α x / x ^ 3) volume 3 M := by
  obtain ⟨C, hC⟩ := bdd_innerR s ν α M hM
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hM]
  refine IntegrableOn.of_bound measure_Icc_lt_top
    (((measurable_innerR s ν α).div (measurable_id.pow_const 3)).aestronglyMeasurable) (C / 27)
    (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_))
  have hx3 : (27:ℝ) ≤ x ^ 3 := by
    have : (3:ℝ) ≤ x := hx.1
    nlinarith [this, sq_nonneg x, mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < x)]
  have hxpos : (0:ℝ) < x ^ 3 := by linarith
  have hCx := hC x hx
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hCx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpos]
  calc |innerR s ν α x| / x ^ 3 ≤ C / x ^ 3 := div_le_div_of_nonneg_right hCx hxpos.le
    _ ≤ C / 27 := div_le_div_of_nonneg_left hC0 (by norm_num) hx3

end

end Mathathon.P108
