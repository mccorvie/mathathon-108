import Dictionary
import ContinuousClasses

/- E426 Codex inner_regularity. PROOF-DRAFT actual inner regularity.
The finite-cell integral theorem is the frozenE420 worker's attributed
extension of the Apache Zeta5 ClassSum interval-count architecture. -/
open MeasureTheory Set Filter Topology Finset
namespace BInnerLimit
noncomputable section
open Mathathon.P108 BInnerExplicit.ClassSums

def gammaTable (s ν T qA qX : ℝ) (a b : ℕ) : ℝ :=
  (T - ν / 2 * (2 * qA + a)) *
    (T + ν / 2 * (2 * qA + a) - (2 * qX + b) - s)

def gammaCells (s ν T qA qX f g : ℝ) : ℝ :=
  ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => gammaTable s ν T qA qX a b) j) i *
    ccount f g i j

theorem integral_gamma_cells (s ν α x : ℝ) :
    (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand s ν α x z) =
      gammaCells s ν (Tc ν α x) (⌊α * x⌋ : ℝ) (⌊x⌋ : ℝ)
        (Int.fract (α * x)) (Int.fract x) := by
  calc
    _ = ∫ z in (0 : ℝ)..(1 / 2), gammaTable s ν (Tc ν α x)
        (⌊α * x⌋ : ℝ) (⌊x⌋ : ℝ)
        (BInnerExplicit.ContinuousClasses.aCount (Int.fract (α * x)) z)
        (BInnerExplicit.ContinuousClasses.aCount (Int.fract x) z) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hz
      rw [gammaIntegrand, ell_fract_dictionary (α * x) z hz.1 hz.2,
        ell_fract_dictionary x z hz.1 hz.2]
      rfl
    _ = _ := BInnerExplicit.ContinuousClasses.class_integral _ _ _

theorem continuousAt_floorCast {x : ℝ} (h : x ≠ (⌊x⌋ : ℝ)) :
    ContinuousAt (fun y : ℝ => (⌊y⌋ : ℝ)) x :=
  (continuousOn_floor ⌊x⌋).continuousAt <|
    Ico_mem_nhds ((Int.floor_le _).lt_of_ne h.symm) (Int.lt_floor_add_one _)

theorem continuousAt_gammaCells (s ν : ℝ) {T A X f g : ℝ → ℝ} {x : ℝ}
    (hT : ContinuousAt T x) (hA : ContinuousAt A x) (hX : ContinuousAt X x)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => gammaCells s ν (T y) (A y) (X y) (f y) (g y)) x := by
  unfold gammaCells
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  change ContinuousAt (fun y => bcoef (fun a => bcoef (fun b => gammaTable s ν (T y) (A y) (X y) a b) j) i * ccount (f y) (g y) i j) x
  fin_cases i <;> fin_cases j <;>
    simp only [bcoef, gammaTable, ccount, cvLo, cvHi, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem integral_gamma_continuousAt (s ν α x : ℝ)
    (hx : ∀ k : ℤ, x ≠ k) (hαx : ∀ k : ℤ, α * x ≠ k)
    (cT : ContinuousAt (Tc ν α) x) :
    ContinuousAt (fun y => ∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand s ν α y z) x := by
  simp_rw [integral_gamma_cells]
  have cf : ContinuousAt Int.fract x := continuousAt_fract (hx _)
  have ca : ContinuousAt (fun y : ℝ => Int.fract (α * y)) x :=
    (continuousAt_fract (hαx _)).comp (continuousAt_const.mul continuousAt_id)
  have cX := continuousAt_floorCast (hx ⌊x⌋)
  have cA : ContinuousAt (fun y : ℝ => (⌊α * y⌋ : ℝ)) x :=
    (continuousAt_floorCast (hαx _)).comp (continuousAt_const.mul continuousAt_id)
  exact continuousAt_gammaCells s ν cT cA cX ca cf

theorem innerR_continuousAt (s ν α x : ℝ)
    (hx : ∀ k : ℤ, x ≠ k) (hαx : ∀ k : ℤ, α * x ≠ k)
    (cT : ContinuousAt (Tc ν α) x)
    (h2x : ∀ k : ℤ, 2 * x ≠ k)
    (hlamx : ∀ k : ℤ, 2 * (1 - α) * x ≠ k) :
    ContinuousAt (innerR s ν α) x := by
  have cI := integral_gamma_continuousAt s ν α x hx hαx cT
  have cX := continuousAt_floorCast (hx ⌊x⌋)
  have cA : ContinuousAt (fun y : ℝ => (⌊α * y⌋ : ℝ)) x :=
    (continuousAt_floorCast (hαx _)).comp (continuousAt_const.mul continuousAt_id)
  have c2 : ContinuousAt (fun y : ℝ => (⌊2 * y⌋ : ℝ)) x :=
    (continuousAt_floorCast (h2x _)).comp (continuousAt_const.mul continuousAt_id)
  have clam : ContinuousAt (fun y : ℝ => (⌊2 * ((1 - α) * y)⌋ : ℝ)) x := by
    have h : 2 * ((1 - α) * x) ≠ (⌊2 * ((1 - α) * x)⌋ : ℝ) := by
      simpa only [mul_assoc] using hlamx ⌊2 * ((1 - α) * x)⌋
    have hm : ContinuousAt (fun y : ℝ => 2 * ((1 - α) * y)) x := by fun_prop
    exact ContinuousAt.comp (f := fun y : ℝ => 2 * ((1 - α) * y)) (g := fun z : ℝ => (⌊z⌋ : ℝ)) (x := x) (continuousAt_floorCast h) hm
  unfold innerR innerGamma innerN sigmaC nplus Jfun
  fun_prop

#print axioms integral_gamma_cells
#print axioms innerR_continuousAt
end
end BInnerLimit
