import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# #108: the general (s, ν) outer function and `I_out` (EVENT WORK)

Formalizer (Claude Opus 5.5), Fri Nov 13 2026, started 22:14 PT. Lean v4.35.0, Mathlib v4.35.0.

Definitions transcribe criterion5 `derivation.md` §3 and its code `general_sq.py` (`c_rem`, `z_rem`,
`g_general`, `PkgGen.Tout`, `I_out_gen`), which theta.py's reading 'S' (`Pkg.outer_parts`,
`Pkg.Tout`) also implements. With `y = p/K`, `k = ⌊1/y⌋`, `v = 1 − ky`, `u = (α + v − y)₊`,
`m_v = min(α, v)`, removed classes of length `ℓ = 2k, 2k+1, 2k+2` have densities
`α − m_v, m_v − u, u`, and

  g_(s,ν)(y) = (s+2)[(1 − y) − Σ_ℓ dens(ℓ)(ℓ−2)] + Σ_ℓ dens(ℓ) c¹(ℓ) + min(r̂, ẑ)   (1/3 < y ≤ 1; else 0),
  c¹(ℓ) = Σ_(i=0)^(ℓ−3) max(0, ℓ + s − 1 − ν − 2i),  z¹(ℓ) = 1 + #{i ≤ ℓ−3 : ℓ + s − 1 − ν − 2i ≤ 0},
  ẑ = y − 2α + Σ_ℓ dens(ℓ) z¹(ℓ),  r̂ = min(λ, (1 + (ν−2)α − ((s−1)/2) y)₊),
  T_out(y) = g_(s,ν)(y) − 2λ⌊1/y⌋ + Σ_(j=1)^6 (2λ − jy)₊,
  I_out(s, ν, α) = ∫_(1/3)^(2λ) T_out(y) dy,   λ = 1 − α.

Differences from derivation.md (read before citing):
* the Legendre sum is truncated at `j = 6` exactly as in the code (`range(1, 7)`); on the
  integration range `y ≥ 1/3` and for `λ ≤ 1` every term `j ≥ 6` is `≤ 0`, so this equals the
  derivation's `Σ_(j≥1)` there;
* `⌊1/y⌋` is the natural-number floor `⌊1/y⌋₊`, equal to the integer floor for `y > 0`;
* the formulas are taken as written (the code's general outer function); that they are the
  correct (s, ν) generalisation of Fauzan (4.10)-(4.14) is the advocate's PROOF-DRAFT, not
  formalized here.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-- `c¹(ℓ) = Σ_(i=0)^(ℓ−3) max(0, ℓ + s − 1 − ν − 2i)`: cost of a class with one removed pole
(general_sq.py `c_rem`). -/
def cRem (s ν : ℝ) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (l - 2), max 0 ((l : ℝ) + s - 1 - ν - 2 * (i : ℝ))

/-- `z¹(ℓ) = 1 + #{i ≤ ℓ−3 : ℓ + s − 1 − ν − 2i ≤ 0}`: zero weights of such a class
(general_sq.py `z_rem`). -/
def zRem (s ν : ℝ) (l : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (l - 2), if (l : ℝ) + s - 1 - ν - 2 * (i : ℝ) ≤ 0 then (1 : ℝ) else 0

/-- The general outer limiting function `g_(s,ν)(y)` (general_sq.py `g_general`). -/
def gOuter (s ν α y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y ≤ 1 then
    let k : ℕ := ⌊1 / y⌋₊
    let v : ℝ := 1 - (k : ℝ) * y
    let u : ℝ := max 0 (α + v - y)
    let mv : ℝ := min α v
    let d0 : ℝ := α - mv
    let d1 : ℝ := mv - u
    let d2 : ℝ := u
    let cost : ℝ := (s + 2) * ((1 - y) - (d0 * (2 * (k : ℝ) - 2) + d1 * (2 * (k : ℝ) + 1 - 2)
        + d2 * (2 * (k : ℝ) + 2 - 2)))
      + (d0 * cRem s ν (2 * k) + d1 * cRem s ν (2 * k + 1) + d2 * cRem s ν (2 * k + 2))
    let zz : ℝ := (y - 2 * α)
      + (d0 * zRem s ν (2 * k) + d1 * zRem s ν (2 * k + 1) + d2 * zRem s ν (2 * k + 2))
    let r : ℝ := min (1 - α) (max 0 (1 + (ν - 2) * α - (s - 1) / 2 * y))
    cost + min r zz
  else 0

/-- The `S_K` (Legendre) part `−2λ⌊1/y⌋ + Σ_(j=1)^6 (2λ − jy)₊` (general_sq.py `PkgGen.Tout`). -/
def legendreTerm (α y : ℝ) : ℝ :=
  -2 * (1 - α) * (⌊1 / y⌋₊ : ℝ) + ∑ j ∈ Finset.range 6, max (2 * (1 - α) - ((j : ℝ) + 1) * y) 0

/-- `T_out = g_(s,ν) + Legendre part`. -/
def Tout (s ν α y : ℝ) : ℝ := gOuter s ν α y + legendreTerm α y

/-- `I_out(s, ν, α) = ∫_(1/3)^(2λ) T_out(y) dy`, `λ = 1 − α` (general_sq.py `I_out_gen`;
Fauzan (5.10) and Lai (84) at (s, ν) = (5, 6)). -/
def Iout (s ν α : ℝ) : ℝ := ∫ y in (1 / 3 : ℝ)..(2 * (1 - α)), Tout s ν α y

lemma fl2 (y : ℝ) (h1 : 1 / 3 < y) (h2 : y ≤ 1 / 2) : ⌊1 / y⌋₊ = 2 := by
  have hy : 0 < y := by linarith
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hy]; push_cast; linarith
  · rw [div_lt_iff₀ hy]; push_cast; linarith

lemma fl1 (y : ℝ) (h1 : 1 / 2 < y) (h2 : y ≤ 1) : ⌊1 / y⌋₊ = 1 := by
  have hy : 0 < y := by linarith
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hy]; push_cast; linarith
  · rw [div_lt_iff₀ hy]; push_cast; linarith

lemma fl0 (y : ℝ) (h1 : 1 < y) : ⌊1 / y⌋₊ = 0 := by
  have hy : 0 < y := by linarith
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · push_cast; positivity
  · rw [div_lt_iff₀ hy]; push_cast; linarith

/-- An a.e.-affine piece integrates as an affine function. -/
lemma piece_integral (f : ℝ → ℝ) (l r a b : ℝ) (hlr : l ≤ r) (h : ∀ y ∈ Ioc l r, f y = a + b * y) :
    IntervalIntegrable f volume l r ∧ ∫ y in l..r, f y = a * (r - l) + b * (r ^ 2 - l ^ 2) / 2 := by
  have hc : IntervalIntegrable (fun y => a + b * y) volume l r :=
    (by fun_prop : Continuous fun y : ℝ => a + b * y).intervalIntegrable _ _
  have heq : EqOn (fun y => a + b * y) f (uIoc l r) := by
    rw [uIoc_of_le hlr]; intro y hy; exact (h y hy).symm
  refine ⟨hc.congr heq, ?_⟩
  rw [intervalIntegral.integral_congr_ae (g := fun y => a + b * y)
    (Filter.Eventually.of_forall (fun y hy => (heq hy).symm))]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_id'.intervalIntegrable _ _).const_mul b), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

lemma integral_concat (f : ℝ → ℝ) (a b c I1 I2 : ℝ)
    (h1 : IntervalIntegrable f volume a b ∧ ∫ y in a..b, f y = I1)
    (h2 : IntervalIntegrable f volume b c ∧ ∫ y in b..c, f y = I2) :
    IntervalIntegrable f volume a c ∧ ∫ y in a..c, f y = I1 + I2 :=
  ⟨h1.1.trans h2.1, by rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1, h1.2, h2.2]⟩

/-! Piece tactics. Each unfolds `Tout` at a point `y` of a piece `Ioc l r`, fixes `⌊1/y⌋₊`, evaluates
the class sums, and resolves every `max`/`min` by `linarith` from `l < y ≤ r` (innermost first: the
argument-free `max`es, then `min α ·` and `min λ ·` at α = 3/40, then the outer `min r̂ ẑ`). They are
specific to α = 3/40. -/

/-- Piece tactic on `(1/3, 1/2]` (`⌊1/y⌋ = 2`). -/
macro "piece2" : tactic => `(tactic| (
  intro y hy
  obtain ⟨hl, hr⟩ := hy
  have hk : ⌊1 / y⌋₊ = 2 := fl2 y (by linarith) (by linarith)
  have hc : (1 / 3 : ℝ) < y ∧ y ≤ 1 := ⟨by linarith, by linarith⟩
  unfold Tout gOuter legendreTerm
  rw [if_pos hc]
  simp only [hk, cRem, zRem, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  repeat (first | (rw [max_eq_left]; rotate_left; linarith) | (rw [max_eq_right]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_left (a := (37/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (37/40:ℝ))]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left]; rotate_left; linarith) | (rw [min_eq_right]; rotate_left; linarith))
  linarith))

/-- Piece tactic on `(1/2, 1]` (`⌊1/y⌋ = 1`). -/
macro "piece1" : tactic => `(tactic| (
  intro y hy
  obtain ⟨hl, hr⟩ := hy
  have hk : ⌊1 / y⌋₊ = 1 := fl1 y (by linarith) (by linarith)
  have hc : (1 / 3 : ℝ) < y ∧ y ≤ 1 := ⟨by linarith, by linarith⟩
  unfold Tout gOuter legendreTerm
  rw [if_pos hc]
  simp only [hk, cRem, zRem, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  repeat (first | (rw [max_eq_left]; rotate_left; linarith) | (rw [max_eq_right]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_left (a := (37/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (37/40:ℝ))]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left]; rotate_left; linarith) | (rw [min_eq_right]; rotate_left; linarith))
  linarith))

/-- Piece tactic on `(1, 2λ]` (`⌊1/y⌋ = 0`, `g = 0`). -/
macro "piece0" : tactic => `(tactic| (
  intro y hy
  obtain ⟨hl, hr⟩ := hy
  have hk : ⌊1 / y⌋₊ = 0 := fl0 y (by linarith)
  have hc : ¬ ((1 / 3 : ℝ) < y ∧ y ≤ 1) := fun h => by linarith [h.2]
  unfold Tout gOuter legendreTerm
  rw [if_neg hc]
  simp only [hk, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  repeat (first | (rw [max_eq_left]; rotate_left; linarith) | (rw [max_eq_right]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (3/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_left (a := (37/40:ℝ))]; rotate_left; linarith) | (rw [min_eq_right (a := (37/40:ℝ))]; rotate_left; linarith))
  repeat (first | (rw [min_eq_left]; rotate_left; linarith) | (rw [min_eq_right]; rotate_left; linarith))
  linarith))

end

end Mathathon.P108
