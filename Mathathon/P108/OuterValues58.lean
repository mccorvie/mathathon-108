import Mathathon.P108.OuterValues
import Mathathon.P108.InnerShift

/-!
# #108: the ν = 8 rescue at (s, ν) = (5, 8), α = 3/40: exact arithmetic (EVENT WORK)

Formalizer (Claude Opus 5.5), Sat Nov 14 2026. Lean v4.33.1, Mathlib v4.33.1.

Source: `../nu8_rescue/derive_fauzan-residue/derivation.md` (Proposition A and its "Consequence";
§0 item 3; §3 table), computed there by `residue58.py integral`. On `(1/3, 17/40]` the package's outer
integrand `T_out(y) = g(y) + scal(y)` (criterion5 `general_sq.py` `PkgGen.Tout`; here `Tout 5 8 (3/40)`
of `OuterDefs.lean`) is replaced by Proposition A's outer weight `T_new(y) = y R_(5,8)(1/y)`
(criterion5 `derivation.md` (2.2); here `innerR 5 8 (3/40)` of `InnerShift.lean`).

Definitions (rational piecewise-affine, `0` outside `(1/3, 17/40]`):
* `TnewA58`: Proposition A's outer weight `y R_(5,8)(1/y)`, 6 affine pieces;
* `ToutPkg58`: the package outer function `T_out` at (5, 8), 3 affine pieces;
* `IoutNew58`: the new outer integral, `∫_(1/3)^(17/40) T_new + ∫_(17/40)^(2λ) T_out`.

Proved by exact rational computation (every floor, `max` and `min` resolved by `linarith` on the piece,
every integral by `piece_integral` / `ioo_const_integral`; gate: axioms only propext, Classical.choice,
Quot.sound):
* `TnewA58_eq_innerR`, `ToutPkg58_eq_Tout`: on `(1/3, 17/40]` the two piecewise-affine functions
  equal the probe's existing formal `y * innerR 5 8 (3/40) (1/y)` and `Tout 5 8 (3/40) y`
  (so the 9 pieces are not trusted from Python: they are re-derived from those definitions);
* (i) `gain58`, `gain58_formal`: `∫_(1/3)^(17/40) (T_out − T_new) = 1159/28800`;
* (ii) `Iout_new_5_8`: `I_out(5,8) − gain = 363473/288000`, from `Iout_5_8 = 125021/96000`
  (`OuterValues.lean`, gate runs 3 and v4.33.1); `IoutNew58_value`, `IoutNew58_formal`: the
  replaced integral itself is `363473/288000`; `Iout_5_8_split`, `IoutNew58_eq`: it is
  `I_out(5,8)` minus the gain, as integrals;
* `gain58_pos`, `gain58_end`: `T_new < T_out` on `(1/3, 17/40)` and `T_new = T_out` at `17/40`
  (derivation's γ* = 17/40).

Not formalized: Proposition A itself (that Fauzan's allocation (4.4)-(4.8) at (5, 8) gives
`v_p(Δ_K) ≥ γ_p^in = pΓ_(5,8)(K/p) + O(1)` for `K/3 < p ≤ 17K/40`, i.e. that `y R_(5,8)(1/y)` is a valid
outer weight there) and the transcription of its weights from Fauzan; `T_new = y R(1/y)` is taken
from derivation.md's "Consequence" as stated.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-! ## Definitions -/

/-- Proposition A's outer weight at (s, ν) = (5, 8), α = 3/40, on `(1/3, 17/40]`:
`T_new(y) = y R_(5,8)(1/y)` (derivation.md, "Consequence"), as a rational piecewise-affine function
(pieces from `x = 1/y` at the breaks 20/7, 120/43, 100/37, 5/2, 120/49 of `R`); `0` outside. -/
def TnewA58 (y : ℝ) : ℝ :=
  if y ≤ 1/3 then 0
  else if y ≤ 7/20 then 31/20 + 4 * y
  else if y ≤ 43/120 then 111/40 + 1/2 * y
  else if y ≤ 37/100 then 283/40 + (-23/2) * y
  else if y ≤ 2/5 then 209/40 + (-13/2) * y
  else if y ≤ 49/120 then 169/40 + (-4) * y
  else if y ≤ 17/40 then 109/20 + (-7) * y
  else 0

/-- The package's outer function `T_out(y) = g_(5,8)(y) + scal(y)` at α = 3/40 on `(1/3, 17/40]`
(criterion5 general_sq.py `PkgGen.Tout`), as a rational piecewise-affine function; `0` outside. -/
def ToutPkg58 (y : ℝ) : ℝ :=
  if y ≤ 1/3 then 0
  else if y ≤ 43/120 then 23/4 + (-6) * y
  else if y ≤ 37/100 then 89/8 + (-21) * y
  else if y ≤ 17/40 then 371/40 + (-16) * y
  else 0

/-- The new outer integral at (5, 8): `T_new` on `(1/3, 17/40]`, the package's `T_out` on `(17/40, 2λ]`. -/
def IoutNew58 : ℝ :=
  (∫ y in (1/3:ℝ)..(17/40), TnewA58 y) + ∫ y in (17/40:ℝ)..(2 * (1 - 3/40)), Tout 5 8 (3/40) y

/-! ## Pieces of the two definitions -/

lemma TnewA58_p1 : ∀ y ∈ Ioc (1/3:ℝ) (7/20), TnewA58 y = (31/20:ℝ) + (4:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr h1), if_pos h2]

lemma TnewA58_p2 : ∀ y ∈ Ioc (7/20:ℝ) (43/120), TnewA58 y = (111/40:ℝ) + (1/2:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr h1), if_pos h2]

lemma TnewA58_p3 : ∀ y ∈ Ioc (43/120:ℝ) (37/100), TnewA58 y = (283/40:ℝ) + (-23/2:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr (by linarith : (7/20:ℝ) < y)),
    if_neg (not_le.mpr h1), if_pos h2]

lemma TnewA58_p4 : ∀ y ∈ Ioc (37/100:ℝ) (2/5), TnewA58 y = (209/40:ℝ) + (-13/2:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr (by linarith : (7/20:ℝ) < y)),
    if_neg (not_le.mpr (by linarith : (43/120:ℝ) < y)), if_neg (not_le.mpr h1), if_pos h2]

lemma TnewA58_p5 : ∀ y ∈ Ioc (2/5:ℝ) (49/120), TnewA58 y = (169/40:ℝ) + (-4:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr (by linarith : (7/20:ℝ) < y)),
    if_neg (not_le.mpr (by linarith : (43/120:ℝ) < y)), if_neg (not_le.mpr (by linarith : (37/100:ℝ) < y)),
    if_neg (not_le.mpr h1), if_pos h2]

lemma TnewA58_p6 : ∀ y ∈ Ioc (49/120:ℝ) (17/40), TnewA58 y = (109/20:ℝ) + (-7:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold TnewA58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr (by linarith : (7/20:ℝ) < y)),
    if_neg (not_le.mpr (by linarith : (43/120:ℝ) < y)), if_neg (not_le.mpr (by linarith : (37/100:ℝ) < y)),
    if_neg (not_le.mpr (by linarith : (2/5:ℝ) < y)), if_neg (not_le.mpr h1), if_pos h2]

lemma ToutPkg58_p1 : ∀ y ∈ Ioc (1/3:ℝ) (43/120), ToutPkg58 y = (23/4:ℝ) + (-6:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold ToutPkg58
  rw [if_neg (not_le.mpr h1), if_pos h2]

lemma ToutPkg58_p2 : ∀ y ∈ Ioc (43/120:ℝ) (37/100), ToutPkg58 y = (89/8:ℝ) + (-21:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold ToutPkg58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr h1), if_pos h2]

lemma ToutPkg58_p3 : ∀ y ∈ Ioc (37/100:ℝ) (17/40), ToutPkg58 y = (371/40:ℝ) + (-16:ℝ) * y := by
  rintro y ⟨h1, h2⟩
  unfold ToutPkg58
  rw [if_neg (not_le.mpr (by linarith : (1/3:ℝ) < y)), if_neg (not_le.mpr (by linarith : (43/120:ℝ) < y)),
    if_neg (not_le.mpr h1), if_pos h2]

/-! ## `ToutPkg58` is the probe's `Tout 5 8 (3/40)` on `(1/3, 17/40]` (pieces of `Iout_5_8`) -/

theorem ToutPkg58_eq_Tout (y : ℝ) (hy : y ∈ Ioc (1/3:ℝ) (17/40)) :
    ToutPkg58 y = Tout 5 8 (3/40) y := by
  obtain ⟨h1, h2⟩ := hy
  rcases le_or_gt y (43/120) with c1 | c1
  · rw [ToutPkg58_p1 y ⟨h1, c1⟩, Iout_5_8_p0 y ⟨h1, c1⟩]
  rcases le_or_gt y (37/100) with c2 | c2
  · rw [ToutPkg58_p2 y ⟨c1, c2⟩, Iout_5_8_p1 y ⟨c1, c2⟩]
  rcases le_or_gt y (23/60) with c3 | c3
  · rw [ToutPkg58_p3 y ⟨c2, h2⟩, Iout_5_8_p2 y ⟨c2, c3⟩]
  · rw [ToutPkg58_p3 y ⟨c2, h2⟩, Iout_5_8_p3 y ⟨c3, by linarith⟩]

/-! ## `TnewA58` is `y * innerR 5 8 (3/40) (1/y)` on `(1/3, 17/40]`

For `x = 1/y ∈ [40/17, 3)`: `⌊x⌋ = 2`, `⌊αx⌋ = 0`, `T = ⌊(49/20)x⌋ ∈ {5, 6, 7}`, `⌊2x⌋ ∈ {4, 5}`,
`⌊2λx⌋ ∈ {4, 5}`, and the `z`-integrand of `Γ` is constant on three `z`-intervals cut at `αx` and at
`x − 2` (case A, `x < 5/2`) or `3 − x` (cases A2, B). -/

/-- A function equal to the constant `c` on `Ioo a b` integrates to `c (b − a)`. -/
lemma ioo_const_integral (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (h : ∀ z ∈ Ioo a b, f z = c) :
    IntervalIntegrable f volume a b ∧ ∫ z in a..b, f z = c * (b - a) := by
  have hI : IntegrableOn f (Ioo a b) volume :=
    (integrableOn_const (C := c) (by simp)).congr_fun (fun z hz => (h z hz).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hI, ?_⟩
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => c) h, setIntegral_const,
    Real.volume_real_Ioo_of_le hab, smul_eq_mul]
  ring

/-- Case A (`40/17 ≤ x < 5/2`): `z`-cuts `0 < αx < x − 2 < 1/2`; `ℓ(x, z) = 5, 5, 4`, `ℓ(αx, z) = 1, 0, 0`. -/
lemma gammaInt58_A (x : ℝ) (h1 : 40/17 ≤ x) (h2 : x < 5/2) :
    ∫ z in (0:ℝ)..(1/2), gammaIntegrand 5 8 (3/40) x z
      = ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) * (3/40 * x)
        + (Tc 8 (3/40) x * (Tc 8 (3/40) x - 10)) * ((x - 2) - 3/40 * x)
        + (Tc 8 (3/40) x * (Tc 8 (3/40) x - 9)) * (1/2 - (x - 2)) := by
  have e1 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) 0 (3/40 * x)
    ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e2 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (3/40 * x) (x - 2)
    (Tc 8 (3/40) x * (Tc 8 (3/40) x - 10)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = -1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e3 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (x - 2) (1/2)
    (Tc 8 (3/40) x * (Tc 8 (3/40) x - 9)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = -1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have c2 := integral_concat _ _ _ _ _ _ e1 e2
  have c3 := integral_concat _ _ _ _ _ _ c2 e3
  rw [c3.2]
  ring

/-- Case A2 (`5/2 ≤ x < 120/43`): `z`-cuts `0 < αx < 3 − x ≤ 1/2`; `ℓ(x, z) = 5, 5, 6`, `ℓ(αx, z) = 1, 0, 0`. -/
lemma gammaInt58_A2 (x : ℝ) (h1 : 5/2 ≤ x) (h2 : x < 120/43) :
    ∫ z in (0:ℝ)..(1/2), gammaIntegrand 5 8 (3/40) x z
      = ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) * (3/40 * x)
        + (Tc 8 (3/40) x * (Tc 8 (3/40) x - 10)) * ((3 - x) - 3/40 * x)
        + (Tc 8 (3/40) x * (Tc 8 (3/40) x - 11)) * (1/2 - (3 - x)) := by
  have e1 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) 0 (3/40 * x)
    ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e2 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (3/40 * x) (3 - x)
    (Tc 8 (3/40) x * (Tc 8 (3/40) x - 10)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = -1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e3 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (3 - x) (1/2)
    (Tc 8 (3/40) x * (Tc 8 (3/40) x - 11)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = -1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 3 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have c2 := integral_concat _ _ _ _ _ _ e1 e2
  have c3 := integral_concat _ _ _ _ _ _ c2 e3
  rw [c3.2]
  ring

/-- Case B (`120/43 ≤ x < 3`): `z`-cuts `0 < 3 − x ≤ αx < 1/2`; `ℓ(x, z) = 5, 6, 6`, `ℓ(αx, z) = 1, 1, 0`. -/
lemma gammaInt58_B (x : ℝ) (h1 : 120/43 ≤ x) (h2 : x < 3) :
    ∫ z in (0:ℝ)..(1/2), gammaIntegrand 5 8 (3/40) x z
      = ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) * (3 - x)
        + ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 7)) * (3/40 * x - (3 - x))
        + (Tc 8 (3/40) x * (Tc 8 (3/40) x - 11)) * (1/2 - 3/40 * x) := by
  have e1 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) 0 (3 - x)
    ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 6)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e2 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (3 - x) (3/40 * x)
    ((Tc 8 (3/40) x - 4) * (Tc 8 (3/40) x - 7)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 3 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have e3 := ioo_const_integral (fun z => gammaIntegrand 5 8 (3/40) x z) (3/40 * x) (1/2)
    (Tc 8 (3/40) x * (Tc 8 (3/40) x - 11)) (by linarith) (by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have f1 : ⌊3/40 * x - z⌋ = -1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f2 : ⌊3/40 * x + z⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f3 : ⌊x - z⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have f4 : ⌊x + z⌋ = 3 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      simp only [gammaIntegrand, ell, f1, f2, f3, f4]
      push_cast; ring)
  have c2 := integral_concat _ _ _ _ _ _ e1 e2
  have c3 := integral_concat _ _ _ _ _ _ c2 e3
  rw [c3.2]
  ring

lemma Hc_8_alpha : Hc 8 (3/40) = 49/40 := by unfold Hc; norm_num

/-- `R_(5,8)(x) = 4 + (31/20) x` on `[20/7, 3)` (`T = 7`, `⌊2x⌋ = 5`, `⌊2λx⌋ = 5`, case B). -/
lemma innerR58_x1 (x : ℝ) (h1 : 20/7 ≤ x) (h2 : x < 3) :
    innerR 5 8 (3/40) x = 4 + 31/20 * x := by
  have hT : Tc 8 (3/40) x = 7 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 7 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 5 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 5 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 0 := by
    rw [hA]; exact max_eq_right (by linarith)
  have hI := gammaInt58_B x (by linarith) h2
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

/-- `R_(5,8)(x) = 1/2 + (111/40) x` on `[120/43, 20/7)` (`T = 6`, `⌊2x⌋ = 5`, `⌊2λx⌋ = 5`, case B). -/
lemma innerR58_x2 (x : ℝ) (h1 : 120/43 ≤ x) (h2 : x < 20/7) :
    innerR 5 8 (3/40) x = 1/2 + 111/40 * x := by
  have hT : Tc 8 (3/40) x = 6 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 6 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 5 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 5 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1/2 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 9/40 * x - 1/2 := by
    rw [hA]; exact max_eq_left (by linarith)
  have hI := gammaInt58_B x h1 (by linarith)
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

/-- `R_(5,8)(x) = −23/2 + (283/40) x` on `[100/37, 120/43)` (`T = 6`, `⌊2x⌋ = 5`, `⌊2λx⌋ = 5`, case A2). -/
lemma innerR58_x3 (x : ℝ) (h1 : 100/37 ≤ x) (h2 : x < 120/43) :
    innerR 5 8 (3/40) x = -23/2 + 283/40 * x := by
  have hT : Tc 8 (3/40) x = 6 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 6 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 5 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 5 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1/2 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 9/40 * x - 1/2 := by
    rw [hA]; exact max_eq_left (by linarith)
  have hI := gammaInt58_A2 x (by linarith) h2
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

/-- `R_(5,8)(x) = −13/2 + (209/40) x` on `[5/2, 100/37)` (`T = 6`, `⌊2x⌋ = 5`, `⌊2λx⌋ = 4`, case A2). -/
lemma innerR58_x4 (x : ℝ) (h1 : 5/2 ≤ x) (h2 : x < 100/37) :
    innerR 5 8 (3/40) x = -13/2 + 209/40 * x := by
  have hT : Tc 8 (3/40) x = 6 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 6 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 5 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 4 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1/2 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 9/40 * x - 1/2 := by
    rw [hA]; exact max_eq_left (by linarith)
  have hI := gammaInt58_A2 x h1 (by linarith)
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

/-- `R_(5,8)(x) = −4 + (169/40) x` on `[120/49, 5/2)` (`T = 6`, `⌊2x⌋ = 4`, `⌊2λx⌋ = 4`, case A). -/
lemma innerR58_x5 (x : ℝ) (h1 : 120/49 ≤ x) (h2 : x < 5/2) :
    innerR 5 8 (3/40) x = -4 + 169/40 * x := by
  have hT : Tc 8 (3/40) x = 6 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 6 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 4 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 4 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 0 := by
    rw [hA]; exact max_eq_right (by linarith)
  have hI := gammaInt58_A x (by linarith) h2
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

/-- `R_(5,8)(x) = −7 + (109/20) x` on `[40/17, 120/49)` (`T = 5`, `⌊2x⌋ = 4`, `⌊2λx⌋ = 4`, case A). -/
lemma innerR58_x6 (x : ℝ) (h1 : 40/17 ≤ x) (h2 : x < 120/49) :
    innerR 5 8 (3/40) x = -7 + 109/20 * x := by
  have hT : Tc 8 (3/40) x = 5 := by
    unfold Tc; rw [Hc_8_alpha]
    have h : ⌊2 * (49/40 : ℝ) * x⌋ = 5 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [h]; norm_num
  have hq : ⌊2 * x⌋ = 4 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hx : ⌊x⌋ = 2 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have ha : ⌊3/40 * x⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hm : ⌊2 * ((1 - 3/40) * x)⌋ = 4 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hA : sigmaC 8 (3/40) x - nplus x = 9/40 * x - 1/2 := by
    unfold sigmaC nplus; rw [Hc_8_alpha, hT, hq]; push_cast; ring
  have hmax : max (sigmaC 8 (3/40) x - nplus x) 0 = 9/40 * x - 1/2 := by
    rw [hA]; exact max_eq_left (by linarith)
  have hI := gammaInt58_A x h1 (by linarith)
  unfold innerR innerGamma
  rw [hI, hmax]
  unfold sigmaC innerN Jfun
  rw [Hc_8_alpha, hT, hq, hx, ha, hm]
  push_cast
  ring

theorem TnewA58_eq_innerR (y : ℝ) (hy : y ∈ Ioc (1/3:ℝ) (17/40)) :
    TnewA58 y = y * innerR 5 8 (3/40) (1/y) := by
  obtain ⟨h1, h2⟩ := hy
  have hy0 : 0 < y := by linarith
  have hxy : y * (1/y) = 1 := by rw [mul_one_div, div_self hy0.ne']
  rcases le_or_gt y (7/20) with c1 | c1
  · rw [TnewA58_p1 y ⟨h1, c1⟩,
      innerR58_x1 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-31/20 : ℝ) * hxy
  rcases le_or_gt y (43/120) with c2 | c2
  · rw [TnewA58_p2 y ⟨c1, c2⟩,
      innerR58_x2 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-111/40 : ℝ) * hxy
  rcases le_or_gt y (37/100) with c3 | c3
  · rw [TnewA58_p3 y ⟨c2, c3⟩,
      innerR58_x3 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-283/40 : ℝ) * hxy
  rcases le_or_gt y (2/5) with c4 | c4
  · rw [TnewA58_p4 y ⟨c3, c4⟩,
      innerR58_x4 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-209/40 : ℝ) * hxy
  rcases le_or_gt y (49/120) with c5 | c5
  · rw [TnewA58_p5 y ⟨c4, c5⟩,
      innerR58_x5 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-169/40 : ℝ) * hxy
  · rw [TnewA58_p6 y ⟨c5, h2⟩,
      innerR58_x6 (1/y) (by rw [le_div_iff₀ hy0]; linarith) (by rw [div_lt_iff₀ hy0]; linarith)]
    linear_combination (-109/20 : ℝ) * hxy

/-! ## The integrals -/

theorem TnewA58_integral : IntervalIntegrable TnewA58 volume (1/3) (17/40) ∧
    ∫ y in (1/3:ℝ)..(17/40), TnewA58 y = 9091/36000 := by
  have c0 := piece_integral TnewA58 (1/3:ℝ) (7/20:ℝ) (31/20:ℝ) (4:ℝ) (by norm_num) TnewA58_p1
  have c1 := integral_concat _ _ _ _ _ _ c0
    (piece_integral TnewA58 (7/20:ℝ) (43/120:ℝ) (111/40:ℝ) (1/2:ℝ) (by norm_num) TnewA58_p2)
  have c2 := integral_concat _ _ _ _ _ _ c1
    (piece_integral TnewA58 (43/120:ℝ) (37/100:ℝ) (283/40:ℝ) (-23/2:ℝ) (by norm_num) TnewA58_p3)
  have c3 := integral_concat _ _ _ _ _ _ c2
    (piece_integral TnewA58 (37/100:ℝ) (2/5:ℝ) (209/40:ℝ) (-13/2:ℝ) (by norm_num) TnewA58_p4)
  have c4 := integral_concat _ _ _ _ _ _ c3
    (piece_integral TnewA58 (2/5:ℝ) (49/120:ℝ) (169/40:ℝ) (-4:ℝ) (by norm_num) TnewA58_p5)
  have c5 := integral_concat _ _ _ _ _ _ c4
    (piece_integral TnewA58 (49/120:ℝ) (17/40:ℝ) (109/20:ℝ) (-7:ℝ) (by norm_num) TnewA58_p6)
  refine ⟨c5.1, ?_⟩
  rw [c5.2]
  norm_num

theorem ToutPkg58_integral : IntervalIntegrable ToutPkg58 volume (1/3) (17/40) ∧
    ∫ y in (1/3:ℝ)..(17/40), ToutPkg58 y = 14053/48000 := by
  have c0 := piece_integral ToutPkg58 (1/3:ℝ) (43/120:ℝ) (23/4:ℝ) (-6:ℝ) (by norm_num) ToutPkg58_p1
  have c1 := integral_concat _ _ _ _ _ _ c0
    (piece_integral ToutPkg58 (43/120:ℝ) (37/100:ℝ) (89/8:ℝ) (-21:ℝ) (by norm_num) ToutPkg58_p2)
  have c2 := integral_concat _ _ _ _ _ _ c1
    (piece_integral ToutPkg58 (37/100:ℝ) (17/40:ℝ) (371/40:ℝ) (-16:ℝ) (by norm_num) ToutPkg58_p3)
  refine ⟨c2.1, ?_⟩
  rw [c2.2]
  norm_num

/-- **(i), piecewise form.** `∫_(1/3)^(17/40) (T_out − T_new) dy = 1159/28800`. -/
theorem gain58 : ∫ y in (1/3:ℝ)..(17/40), (ToutPkg58 y - TnewA58 y) = 1159/28800 := by
  rw [intervalIntegral.integral_sub ToutPkg58_integral.1 TnewA58_integral.1,
    ToutPkg58_integral.2, TnewA58_integral.2]
  norm_num

/-- **(i), formal form.** The same gain with the probe's definitions:
`∫_(1/3)^(17/40) (T_out(5,8)(y) − y R_(5,8)(1/y)) dy = 1159/28800` at α = 3/40. -/
theorem gain58_formal :
    ∫ y in (1/3:ℝ)..(17/40), (Tout 5 8 (3/40) y - y * innerR 5 8 (3/40) (1/y)) = 1159/28800 := by
  rw [← gain58]
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  rw [uIoc_of_le (show (1/3:ℝ) ≤ 17/40 by norm_num)] at hy
  rw [ToutPkg58_eq_Tout y hy, TnewA58_eq_innerR y hy]

/-- `T_out(5,8)` on `(17/40, 2λ]`, from the pieces of `Iout_5_8` (the first one cut at 17/40). -/
theorem Tout58_tail : IntervalIntegrable (Tout 5 8 (3/40)) volume (17/40) (37/20) ∧
    ∫ y in (17/40:ℝ)..(37/20), Tout 5 8 (3/40) y = 6461/6400 := by
  have c3 := piece_integral (Tout 5 8 (3/40)) (17/40:ℝ) (9/20:ℝ) (371/40:ℝ) (-16:ℝ) (by norm_num)
    (fun y hy => Iout_5_8_p3 y ⟨by linarith [hy.1], hy.2⟩)
  have c4 := integral_concat _ _ _ _ _ _ c3 (piece_integral _ (9/20:ℝ) (11/24:ℝ) (371/40:ℝ) (-16:ℝ) (by norm_num) Iout_5_8_p4)
  have c5 := integral_concat _ _ _ _ _ _ c4 (piece_integral _ (11/24:ℝ) (37/80:ℝ) (213/20:ℝ) (-19:ℝ) (by norm_num) Iout_5_8_p5)
  have c6 := integral_concat _ _ _ _ _ _ c5 (piece_integral _ (37/80:ℝ) (29/60:ℝ) (13/4:ℝ) (-3:ℝ) (by norm_num) Iout_5_8_p6)
  have c7 := integral_concat _ _ _ _ _ _ c6 (piece_integral _ (29/60:ℝ) (1/2:ℝ) (13/4:ℝ) (-3:ℝ) (by norm_num) Iout_5_8_p7)
  have c8 := integral_concat _ _ _ _ _ _ c7 (piece_integral _ (1/2:ℝ) (61/120:ℝ) (41/10:ℝ) (-1:ℝ) (by norm_num) Iout_5_8_p8)
  have c9 := integral_concat _ _ _ _ _ _ c8 (piece_integral _ (61/120:ℝ) (43/80:ℝ) (41/10:ℝ) (-1:ℝ) (by norm_num) Iout_5_8_p9)
  have c10 := integral_concat _ _ _ _ _ _ c9 (piece_integral _ (43/80:ℝ) (37/60:ℝ) (93/8:ℝ) (-15:ℝ) (by norm_num) Iout_5_8_p10)
  have c11 := integral_concat _ _ _ _ _ _ c10 (piece_integral _ (37/60:ℝ) (2/3:ℝ) (391/40:ℝ) (-12:ℝ) (by norm_num) Iout_5_8_p11)
  have c12 := integral_concat _ _ _ _ _ _ c11 (piece_integral _ (2/3:ℝ) (29/40:ℝ) (391/40:ℝ) (-12:ℝ) (by norm_num) Iout_5_8_p12)
  have c13 := integral_concat _ _ _ _ _ _ c12 (piece_integral _ (29/40:ℝ) (37/40:ℝ) (333/40:ℝ) (-10:ℝ) (by norm_num) Iout_5_8_p13)
  have c14 := integral_concat _ _ _ _ _ _ c13 (piece_integral _ (37/40:ℝ) (1:ℝ) (0:ℝ) (-1:ℝ) (by norm_num) Iout_5_8_p14)
  have c15 := integral_concat _ _ _ _ _ _ c14 (piece_integral _ (1:ℝ) (37/20:ℝ) (37/20:ℝ) (-1:ℝ) (by norm_num) Iout_5_8_p15)
  refine ⟨c15.1, ?_⟩
  rw [c15.2]
  norm_num

/-- **(ii).** `I_out_new(5,8) = I_out(5,8) − gain = 363473/288000`, from `Iout_5_8 = 125021/96000`. -/
theorem Iout_new_5_8 :
    Iout 5 8 (3/40) - (∫ y in (1/3:ℝ)..(17/40), (Tout 5 8 (3/40) y - y * innerR 5 8 (3/40) (1/y)))
      = 363473/288000 := by
  rw [Iout_5_8, gain58_formal]
  norm_num

/-- **(ii), replaced integral (piecewise form).** `∫_(1/3)^(17/40) T_new + ∫_(17/40)^(2λ) T_out = 363473/288000`. -/
theorem IoutNew58_value : IoutNew58 = 363473/288000 := by
  unfold IoutNew58
  rw [show (2 * (1 - (3/40:ℝ))) = 37/20 by norm_num, TnewA58_integral.2, Tout58_tail.2]
  norm_num

/-- **(ii), replaced integral (formal form).** With `T_new(y) = y R_(5,8)(1/y)` from `innerR`:
`∫_(1/3)^(17/40) y R_(5,8)(1/y) dy + ∫_(17/40)^(2λ) T_out(5,8) dy = 363473/288000`. -/
theorem IoutNew58_formal :
    (∫ y in (1/3:ℝ)..(17/40), y * innerR 5 8 (3/40) (1/y))
      + ∫ y in (17/40:ℝ)..(2 * (1 - 3/40)), Tout 5 8 (3/40) y = 363473/288000 := by
  have h : ∫ y in (1/3:ℝ)..(17/40), y * innerR 5 8 (3/40) (1/y)
      = ∫ y in (1/3:ℝ)..(17/40), TnewA58 y := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [uIoc_of_le (show (1/3:ℝ) ≤ 17/40 by norm_num)] at hy
    exact (TnewA58_eq_innerR y hy).symm
  rw [h]
  exact IoutNew58_value

/-- `I_out(5,8)` splits at 17/40 (both parts integrable). -/
theorem Iout_5_8_split :
    Iout 5 8 (3/40) = (∫ y in (1/3:ℝ)..(17/40), Tout 5 8 (3/40) y)
      + ∫ y in (17/40:ℝ)..(2 * (1 - 3/40)), Tout 5 8 (3/40) y := by
  have hA : IntervalIntegrable (Tout 5 8 (3/40)) volume (1/3) (17/40) := by
    refine ToutPkg58_integral.1.congr ?_
    intro y hy
    rw [uIoc_of_le (show (1/3:ℝ) ≤ 17/40 by norm_num)] at hy
    exact ToutPkg58_eq_Tout y hy
  have hB := Tout58_tail.1
  rw [show (2 * (1 - (3/40:ℝ))) = 37/20 by norm_num]
  unfold Iout
  rw [show (2 * (1 - (3/40:ℝ))) = 37/20 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals hA hB).symm

/-- **(ii), as integrals.** The replaced integral is `I_out(5,8)` minus the gain integral. -/
theorem IoutNew58_eq :
    (∫ y in (1/3:ℝ)..(17/40), y * innerR 5 8 (3/40) (1/y))
      + ∫ y in (17/40:ℝ)..(2 * (1 - 3/40)), Tout 5 8 (3/40) y
      = Iout 5 8 (3/40)
        - ∫ y in (1/3:ℝ)..(17/40), (Tout 5 8 (3/40) y - y * innerR 5 8 (3/40) (1/y)) := by
  rw [IoutNew58_formal, Iout_new_5_8]

/-! ## Positivity of the gain on `(1/3, 17/40)` and the crossing at `17/40` -/

/-- `T_new(y) < T_out(y)` for `1/3 < y < 17/40` (derivation.md: "T_out − T_new is positive on (1/3, 17/40)"). -/
theorem gain58_pos (y : ℝ) (hy : y ∈ Ioo (1/3:ℝ) (17/40)) :
    y * innerR 5 8 (3/40) (1/y) < Tout 5 8 (3/40) y := by
  have hy' : y ∈ Ioc (1/3:ℝ) (17/40) := ⟨hy.1, hy.2.le⟩
  rw [← TnewA58_eq_innerR y hy', ← ToutPkg58_eq_Tout y hy']
  obtain ⟨h1, h2⟩ := hy
  rcases le_or_gt y (7/20) with c1 | c1
  · rw [TnewA58_p1 y ⟨h1, c1⟩, ToutPkg58_p1 y ⟨h1, by linarith⟩]; linarith
  rcases le_or_gt y (43/120) with c2 | c2
  · rw [TnewA58_p2 y ⟨c1, c2⟩, ToutPkg58_p1 y ⟨by linarith, c2⟩]; linarith
  rcases le_or_gt y (37/100) with c3 | c3
  · rw [TnewA58_p3 y ⟨c2, c3⟩, ToutPkg58_p2 y ⟨c2, c3⟩]; linarith
  rcases le_or_gt y (2/5) with c4 | c4
  · rw [TnewA58_p4 y ⟨c3, c4⟩, ToutPkg58_p3 y ⟨c3, by linarith⟩]; linarith
  rcases le_or_gt y (49/120) with c5 | c5
  · rw [TnewA58_p5 y ⟨c4, c5⟩, ToutPkg58_p3 y ⟨by linarith, by linarith⟩]; linarith
  · rw [TnewA58_p6 y ⟨c5, h2.le⟩, ToutPkg58_p3 y ⟨by linarith, h2.le⟩]; linarith

/-- `T_new(17/40) = T_out(17/40)` (= 99/40): the gain vanishes at γ* = 17/40. -/
theorem gain58_end :
    (17/40:ℝ) * innerR 5 8 (3/40) (1/(17/40)) = Tout 5 8 (3/40) (17/40) := by
  have h : (17/40:ℝ) ∈ Ioc (1/3:ℝ) (17/40) := ⟨by norm_num, le_rfl⟩
  rw [← TnewA58_eq_innerR _ h, ← ToutPkg58_eq_Tout _ h,
    TnewA58_p6 (17/40) ⟨by norm_num, le_rfl⟩, ToutPkg58_p3 (17/40) ⟨by norm_num, le_rfl⟩]
  norm_num

end

end Mathathon.P108
