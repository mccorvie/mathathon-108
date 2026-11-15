import MarginPieces
/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
namespace MarginPieces
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_0 (x : ℝ) (hl : (3:ℝ) < x) (hr : x < (70/23:ℝ)) :
    innerR 7 6 (3/40) x = (-6:ℝ) + (109/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (5:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (-15:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-12:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-42:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-15:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-12:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-3:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-15:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-12:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-3:ℝ) + (1:ℝ) * x))) ((-42:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_0 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (3:ℝ) (70/23:ℝ) ∧
    ∫ x in (3:ℝ)..(70/23:ℝ), innerR 7 6 (3/40) x / x^3 = (97/5880:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (3:ℝ) (70/23:ℝ) (-6:ℝ) (109/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_0 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_1 (x : ℝ) (hl : (70/23:ℝ) < x) (hr : x < (120/37:ℝ)) :
    innerR 7 6 (3/40) x = (-(5/2:ℝ)) + (43/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (5:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-12:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-42:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-16:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-12:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-3:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-12:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-3:ℝ) + (1:ℝ) * x))) ((-42:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_1 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (70/23:ℝ) (120/37:ℝ) ∧
    ∫ x in (70/23:ℝ)..(120/37:ℝ), innerR 7 6 (3/40) x / x^3 = (200141/2822400:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (70/23:ℝ) (120/37:ℝ) (-(5/2:ℝ)) (43/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_1 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_2 (x : ℝ) (hl : (120/37:ℝ) < x) (hr : x < (140/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(35/2:ℝ)) + (357/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) (-49:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-42:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-42:ℝ) * ((1/2:ℝ)-((-3:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_2 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (120/37:ℝ) (140/43:ℝ) ∧
    ∫ x in (120/37:ℝ)..(140/43:ℝ), innerR 7 6 (3/40) x / x^3 = (1699/403200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (120/37:ℝ) (140/43:ℝ) (-(35/2:ℝ)) (357/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_2 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_3 (x : ℝ) (hl : (140/43:ℝ) < x) (hr : x < (10/3:ℝ)) :
    innerR 7 6 (3/40) x = (-(35/2:ℝ)) + (357/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) (-49:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-42:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-42:ℝ) * ((1/2:ℝ)-((-3:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_3 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (140/43:ℝ) (10/3:ℝ) ∧
    ∫ x in (140/43:ℝ)..(10/3:ℝ), innerR 7 6 (3/40) x / x^3 = (289/11200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (140/43:ℝ) (10/3:ℝ) (-(35/2:ℝ)) (357/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_3 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_4 (x : ℝ) (hl : (10/3:ℝ) < x) (hr : x < (80/23:ℝ)) :
    innerR 7 6 (3/40) x = (-17:ℝ) + (351/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) (-49:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-42:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-49:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-42:ℝ) * ((1/2:ℝ)-((-3:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_4 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (10/3:ℝ) (80/23:ℝ) ∧
    ∫ x in (10/3:ℝ)..(80/23:ℝ), innerR 7 6 (3/40) x / x^3 = (121/2560:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (10/3:ℝ) (80/23:ℝ) (-17:ℝ) (351/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_4 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_5 (x : ℝ) (hl : (80/23:ℝ) < x) (hr : x < (7/2:ℝ)) :
    innerR 7 6 (3/40) x = (-13:ℝ) + (61/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-15:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) (-48:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-40:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-3:ℝ) + (1:ℝ) * x) ((-15:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-48:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-3:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-15:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-48:ℝ) * (((-3:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-40:ℝ) * ((1/2:ℝ)-((-3:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_5 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (80/23:ℝ) (7/2:ℝ) ∧
    ∫ x in (80/23:ℝ)..(7/2:ℝ), innerR 7 6 (3/40) x / x^3 = (4367/627200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (80/23:ℝ) (7/2:ℝ) (-13:ℝ) (61/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_5 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_6 (x : ℝ) (hl : (7/2:ℝ) < x) (hr : x < (160/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(33/2:ℝ)) + (69/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-15:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((4:ℝ) + (-1:ℝ) * x) (-48:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((4:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (-56:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((4:ℝ) + (-1:ℝ) * x) ((-15:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-48:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((-15:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-48:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-56:ℝ) * ((1/2:ℝ)-((4:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_6 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (7/2:ℝ) (160/43:ℝ) ∧
    ∫ x in (7/2:ℝ)..(160/43:ℝ), innerR 7 6 (3/40) x / x^3 = (344793/5017600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (7/2:ℝ) (160/43:ℝ) (-(33/2:ℝ)) (69/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_6 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_7 (x : ℝ) (hl : (160/43:ℝ) < x) (hr : x < (140/37:ℝ)) :
    innerR 7 6 (3/40) x = (-(9/2:ℝ)) + (27/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (6:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) (-15:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-20:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-56:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-15:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-20:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-15:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-20:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) ((-56:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_7 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (160/43:ℝ) (140/37:ℝ) ∧
    ∫ x in (160/43:ℝ)..(140/37:ℝ), innerR 7 6 (3/40) x / x^3 = (18819/1003520:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (160/43:ℝ) (140/37:ℝ) (-(9/2:ℝ)) (27/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_7 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_8 (x : ℝ) (hl : (140/37:ℝ) < x) (hr : x < (90/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(23/2:ℝ)) + (29/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) (-15:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-20:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-56:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-15:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-20:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-15:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-20:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) ((-56:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_8 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (140/37:ℝ) (90/23:ℝ) ∧
    ∫ x in (140/37:ℝ)..(90/23:ℝ), innerR 7 6 (3/40) x / x^3 = (9449/254016:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (140/37:ℝ) (90/23:ℝ) (-(23/2:ℝ)) (29/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_8 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_9 (x : ℝ) (hl : (90/23:ℝ) < x) (hr : x < (4:ℝ)) :
    innerR 7 6 (3/40) x = (-7:ℝ) + (61/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (3:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) (-12:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-18:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-54:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((4:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-12:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-12:ℝ) * (((4:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((4:ℝ) + (-1:ℝ) * x))) ((-54:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_9 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (90/23:ℝ) (4:ℝ) ∧
    ∫ x in (90/23:ℝ)..(4:ℝ), innerR 7 6 (3/40) x / x^3 = (1559/64800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (90/23:ℝ) (4:ℝ) (-7:ℝ) (61/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_9 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_10 (x : ℝ) (hl : (4:ℝ) < x) (hr : x < (180/43:ℝ)) :
    innerR 7 6 (3/40) x = (-11:ℝ) + (21/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-4:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-18:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-54:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-24:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-4:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-24:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-4:ℝ) + (1:ℝ) * x))) ((-54:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_10 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (4:ℝ) (180/43:ℝ) ∧
    ∫ x in (4:ℝ)..(180/43:ℝ), innerR 7 6 (3/40) x / x^3 = (461/16200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (4:ℝ) (180/43:ℝ) (-11:ℝ) (21/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_10 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_11 (x : ℝ) (hl : (180/43:ℝ) < x) (hr : x < (160/37:ℝ)) :
    innerR 7 6 (3/40) x = (-11:ℝ) + (21/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (7:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-4:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-18:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-54:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-24:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-4:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-24:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-18:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-4:ℝ) + (1:ℝ) * x))) ((-54:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_11 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (180/43:ℝ) (160/37:ℝ) ∧
    ∫ x in (180/43:ℝ)..(160/37:ℝ), innerR 7 6 (3/40) x / x^3 = (84403/4147200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (180/43:ℝ) (160/37:ℝ) (-11:ℝ) (21/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_11 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_12 (x : ℝ) (hl : (160/37:ℝ) < x) (hr : x < (100/23:ℝ)) :
    innerR 7 6 (3/40) x = (-31:ℝ) + (79/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-4:ℝ) + (1:ℝ) * x) (-63:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-4:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-54:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-4:ℝ) + (1:ℝ) * x) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-63:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-63:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-54:ℝ) * ((1/2:ℝ)-((-4:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_12 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (160/37:ℝ) (100/23:ℝ) ∧
    ∫ x in (160/37:ℝ)..(100/23:ℝ), innerR 7 6 (3/40) x / x^3 = (4361/1280000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (160/37:ℝ) (100/23:ℝ) (-31:ℝ) (79/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_12 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_13 (x : ℝ) (hl : (100/23:ℝ) < x) (hr : x < (9/2:ℝ)) :
    innerR 7 6 (3/40) x = (-26:ℝ) + (349/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (10:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-21:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((-4:ℝ) + (1:ℝ) * x) (-60:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-4:ℝ) + (1:ℝ) * x) (1/2:ℝ) (-50:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((-4:ℝ) + (1:ℝ) * x) ((-21:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-60:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-4:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((-21:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-60:ℝ) * (((-4:ℝ) + (1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-50:ℝ) * ((1/2:ℝ)-((-4:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_13 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (100/23:ℝ) (9/2:ℝ) ∧
    ∫ x in (100/23:ℝ)..(9/2:ℝ), innerR 7 6 (3/40) x / x^3 = (35861/1620000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (100/23:ℝ) (9/2:ℝ) (-26:ℝ) (349/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_13 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_14 (x : ℝ) (hl : (9/2:ℝ) < x) (hr : x < (200/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(61/2:ℝ)) + (389/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (10:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (-21:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) ((5:ℝ) + (-1:ℝ) * x) (-60:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((5:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (-70:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) ((5:ℝ) + (-1:ℝ) * x) ((-21:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((-60:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((-21:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(-60:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-((0:ℝ) + (3/40:ℝ) * x))) ((-70:ℝ) * ((1/2:ℝ)-((5:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_14 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (9/2:ℝ) (200/43:ℝ) ∧
    ∫ x in (9/2:ℝ)..(200/43:ℝ), innerR 7 6 (3/40) x / x^3 = (286169/12960000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (9/2:ℝ) (200/43:ℝ) (-(61/2:ℝ)) (389/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_14 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_15 (x : ℝ) (hl : (200/43:ℝ) < x) (hr : x < (110/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(31/2:ℝ)) + (13/2:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (10:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) (-21:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-28:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-70:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-21:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-28:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-21:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-28:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) ((-70:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_15 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (200/43:ℝ) (110/23:ℝ) ∧
    ∫ x in (200/43:ℝ)..(110/23:ℝ), innerR 7 6 (3/40) x / x^3 = (367601/19360000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (200/43:ℝ) (110/23:ℝ) (-(31/2:ℝ)) (13/2:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_15 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_16 (x : ℝ) (hl : (110/23:ℝ) < x) (hr : x < (180/37:ℝ)) :
    innerR 7 6 (3/40) x = (-10:ℝ) + (107/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (11:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (8:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-66:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-16:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) ((-66:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_16 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (110/23:ℝ) (180/37:ℝ) ∧
    ∫ x in (110/23:ℝ)..(180/37:ℝ), innerR 7 6 (3/40) x / x^3 = (5677/490050:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (110/23:ℝ) (180/37:ℝ) (-10:ℝ) (107/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_16 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_17 (x : ℝ) (hl : (180/37:ℝ) < x) (hr : x < (5:ℝ)) :
    innerR 7 6 (3/40) x = (-19:ℝ) + (36/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (11:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (4:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) (-16:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-66:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((5:ℝ) + (-1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-16:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-16:ℝ) * (((5:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((5:ℝ) + (-1:ℝ) * x))) ((-66:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_17 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (180/37:ℝ) (5:ℝ) ∧
    ∫ x in (180/37:ℝ)..(5:ℝ), innerR 7 6 (3/40) x / x^3 = (241/12960:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (180/37:ℝ) (5:ℝ) (-19:ℝ) (36/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_17 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_18 (x : ℝ) (hl : (5:ℝ) < x) (hr : x < (220/43:ℝ)) :
    innerR 7 6 (3/40) x = (-24:ℝ) + (127/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (11:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (5:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (10:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-5:ℝ) + (1:ℝ) * x) (-32:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-5:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-66:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-5:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-32:ℝ) * (((-5:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-5:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-32:ℝ) * (((-5:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-5:ℝ) + (1:ℝ) * x))) ((-66:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_18 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (5:ℝ) (220/43:ℝ) ∧
    ∫ x in (5:ℝ)..(220/43:ℝ), innerR 7 6 (3/40) x / x^3 = (353/48400:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (5:ℝ) (220/43:ℝ) (-24:ℝ) (127/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_18 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_19 (x : ℝ) (hl : (220/43:ℝ) < x) (hr : x < (120/23:ℝ)) :
    innerR 7 6 (3/40) x = (-24:ℝ) + (127/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (11:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (5:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (10:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (9:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-5:ℝ) + (1:ℝ) * x) (-32:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-5:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) (-24:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (-66:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (4:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (5:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (-1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-5:ℝ) + (1:ℝ) * x) ((0:ℝ) + (3/40:ℝ) * x) ((-32:ℝ) * (((-5:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-5:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((0:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((-32:ℝ) * (((-5:ℝ) + (1:ℝ) * x)-(0:ℝ))+(-24:ℝ) * (((0:ℝ) + (3/40:ℝ) * x)-((-5:ℝ) + (1:ℝ) * x))) ((-66:ℝ) * ((1/2:ℝ)-((0:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_19 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (220/43:ℝ) (120/23:ℝ) ∧
    ∫ x in (220/43:ℝ)..(120/23:ℝ), innerR 7 6 (3/40) x / x^3 = (25/3872:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (220/43:ℝ) (120/23:ℝ) (-24:ℝ) (127/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_19 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
lemma chunk_0 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (3:ℝ) (120/23:ℝ) ∧
    ∫ x in (3:ℝ)..(120/23:ℝ), innerR 7 6 (3/40) x / x^3 = (10638527/22176000:ℝ) := by
  have h := i_0
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (70/23:ℝ) (120/37:ℝ) (97/5880:ℝ) (200141/2822400:ℝ) h i_1
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (120/37:ℝ) (140/43:ℝ) (35243/403200:ℝ) (1699/403200:ℝ) h i_2
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (140/43:ℝ) (10/3:ℝ) (6157/67200:ℝ) (289/11200:ℝ) h i_3
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (10/3:ℝ) (80/23:ℝ) (7891/67200:ℝ) (121/2560:ℝ) h i_4
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (80/23:ℝ) (7/2:ℝ) (44269/268800:ℝ) (4367/627200:ℝ) h i_5
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (7/2:ℝ) (160/43:ℝ) (40373/235200:ℝ) (344793/5017600:ℝ) h i_6
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (160/43:ℝ) (140/37:ℝ) (516893/2150400:ℝ) (18819/1003520:ℝ) h i_7
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (140/37:ℝ) (90/23:ℝ) (487567/1881600:ℝ) (9449/254016:ℝ) h i_8
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (90/23:ℝ) (4:ℝ) (2150587/7257600:ℝ) (1559/64800:ℝ) h i_9
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (4:ℝ) (180/43:ℝ) (51671/161280:ℝ) (461/16200:ℝ) h i_10
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (180/43:ℝ) (160/37:ℝ) (2531723/7257600:ℝ) (84403/4147200:ℝ) h i_11
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (160/37:ℝ) (100/23:ℝ) (1190857/3225600:ℝ) (4361/1280000:ℝ) h i_12
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (100/23:ℝ) (9/2:ℝ) (3755771/10080000:ℝ) (35861/1620000:ℝ) h i_13
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (9/2:ℝ) (200/43:ℝ) (7162031/18144000:ℝ) (286169/12960000:ℝ) h i_14
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (200/43:ℝ) (110/23:ℝ) (700247/1680000:ℝ) (367601/19360000:ℝ) h i_15
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (110/23:ℝ) (180/37:ℝ) (35435879/81312000:ℝ) (5677/490050:ℝ) h i_16
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (180/37:ℝ) (5:ℝ) (89291063/199584000:ℝ) (241/12960:ℝ) h i_17
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (5:ℝ) (220/43:ℝ) (10333607/22176000:ℝ) (353/48400:ℝ) h i_18
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (220/43:ℝ) (120/23:ℝ) (115448797/243936000:ℝ) (25/3872:ℝ) h i_19
  norm_num at h
  norm_num at h ⊢
  exact h
end MarginPieces
