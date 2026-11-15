import MarginPieces
/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
namespace MarginPieces
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_280 (x : ℝ) (hl : (1320/37:ℝ) < x) (hr : x < (1540/43:ℝ)) :
    innerR 7 6 (3/40) x = (-1355:ℝ) + (373/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (82:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (35:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (71:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((36:ℝ) + (-1:ℝ) * x) (1273:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((36:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1206:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1344:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((36:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1273:ℝ) * (((36:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((36:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1273:ℝ) * (((36:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((36:ℝ) + (-1:ℝ) * x))) ((1344:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_280 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1320/37:ℝ) (1540/43:ℝ) ∧
    ∫ x in (1320/37:ℝ)..(1540/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(1021/15523200:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1320/37:ℝ) (1540/43:ℝ) (-1355:ℝ) (373/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_280 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_281 (x : ℝ) (hl : (1540/43:ℝ) < x) (hr : x < (36:ℝ)) :
    innerR 7 6 (3/40) x = (-1355:ℝ) + (373/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (82:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (35:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (71:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((36:ℝ) + (-1:ℝ) * x) (1273:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((36:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1206:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1344:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((36:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1273:ℝ) * (((36:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((36:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1273:ℝ) * (((36:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((36:ℝ) + (-1:ℝ) * x))) ((1344:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_281 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1540/43:ℝ) (36:ℝ) ∧
    ∫ x in (1540/43:ℝ)..(36:ℝ), innerR 7 6 (3/40) x / x^3 = (-(1513/24012450:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1540/43:ℝ) (36:ℝ) (-1355:ℝ) (373/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_281 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_282 (x : ℝ) (hl : (36:ℝ) < x) (hr : x < (830/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1391:ℝ) + (729/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (82:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) (1139:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1206:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1344:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1139:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1139:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1206:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) ((1344:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_282 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (36:ℝ) (830/23:ℝ) ∧
    ∫ x in (36:ℝ)..(830/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(64013/446407200:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (36:ℝ) (830/23:ℝ) (-1391:ℝ) (729/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_282 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_283 (x : ℝ) (hl : (830/23:ℝ) < x) (hr : x < (1340/37:ℝ)) :
    innerR 7 6 (3/40) x = (-(2699/2:ℝ)) + (353/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (83:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) (1224:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1292:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1430:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1224:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1292:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1224:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1292:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) ((1430:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_283 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (830/23:ℝ) (1340/37:ℝ) ∧
    ∫ x in (830/23:ℝ)..(1340/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(9929513/49479553600:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (830/23:ℝ) (1340/37:ℝ) (-(2699/2:ℝ)) (353/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_283 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_284 (x : ℝ) (hl : (1340/37:ℝ) < x) (hr : x < (1560/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(2833/2:ℝ)) + (743/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (83:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) (1224:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1292:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1430:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1224:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1292:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1224:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1292:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-36:ℝ) + (1:ℝ) * x))) ((1430:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_284 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1340/37:ℝ) (1560/43:ℝ) ∧
    ∫ x in (1340/37:ℝ)..(1560/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(806239/8739544320:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1340/37:ℝ) (1560/43:ℝ) (-(2833/2:ℝ)) (743/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_284 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_285 (x : ℝ) (hl : (1560/43:ℝ) < x) (hr : x < (73/2:ℝ)) :
    innerR 7 6 (3/40) x = (-(2599/2:ℝ)) + (1357/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (83:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1224:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-36:ℝ) + (1:ℝ) * x) (1365:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-36:ℝ) + (1:ℝ) * x) (1/2:ℝ) (1430:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (35:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-36:ℝ) + (1:ℝ) * x) ((1224:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1365:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-36:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((1224:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1365:ℝ) * (((-36:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1430:ℝ) * ((1/2:ℝ)-((-36:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_285 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1560/43:ℝ) (73/2:ℝ) ∧
    ∫ x in (1560/43:ℝ)..(73/2:ℝ), innerR 7 6 (3/40) x / x^3 = (-(618355/2074984704:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1560/43:ℝ) (73/2:ℝ) (-(2599/2:ℝ)) (1357/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_285 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_286 (x : ℝ) (hl : (73/2:ℝ) < x) (hr : x < (840/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1336:ℝ) + (1397/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (83:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1224:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) (1365:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1300:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) ((1224:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1365:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1224:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1365:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1300:ℝ) * ((1/2:ℝ)-((37:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_286 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (73/2:ℝ) (840/23:ℝ) ∧
    ∫ x in (73/2:ℝ)..(840/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(102211/3760142400:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (73/2:ℝ) (840/23:ℝ) (-1336:ℝ) (1397/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_286 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_287 (x : ℝ) (hl : (840/23:ℝ) < x) (hr : x < (110/3:ℝ)) :
    innerR 7 6 (3/40) x = (-1294:ℝ) + (1351/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (84:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1311:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) (1452:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1386:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1386:ℝ) * ((1/2:ℝ)-((37:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_287 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (840/23:ℝ) (110/3:ℝ) ∧
    ∫ x in (840/23:ℝ)..(110/3:ℝ), innerR 7 6 (3/40) x / x^3 = (-(7327/42688800:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (840/23:ℝ) (110/3:ℝ) (-1294:ℝ) (1351/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_287 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_288 (x : ℝ) (hl : (110/3:ℝ) < x) (hr : x < (1580/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(2577/2:ℝ)) + (269/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (84:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1311:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) (1452:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1386:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1386:ℝ) * ((1/2:ℝ)-((37:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_288 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (110/3:ℝ) (1580/43:ℝ) ∧
    ∫ x in (110/3:ℝ)..(1580/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(102809/1208257600:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (110/3:ℝ) (1580/43:ℝ) (-(2577/2:ℝ)) (269/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_288 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_289 (x : ℝ) (hl : (1580/43:ℝ) < x) (hr : x < (1360/37:ℝ)) :
    innerR 7 6 (3/40) x = (-(2577/2:ℝ)) + (269/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (84:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (67:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1311:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) (1452:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1386:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((37:ℝ) + (-1:ℝ) * x) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1311:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1452:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1386:ℝ) * ((1/2:ℝ)-((37:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_289 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1580/43:ℝ) (1360/37:ℝ) ∧
    ∫ x in (1580/43:ℝ)..(1360/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(617039/46173414400:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1580/43:ℝ) (1360/37:ℝ) (-(2577/2:ℝ)) (269/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_289 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_290 (x : ℝ) (hl : (1360/37:ℝ) < x) (hr : x < (850/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(2917/2:ℝ)) + (153/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (84:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (68:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1311:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1242:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1386:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1311:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1242:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((37:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1311:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1242:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((37:ℝ) + (-1:ℝ) * x))) ((1386:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_290 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1360/37:ℝ) (850/23:ℝ) ∧
    ∫ x in (1360/37:ℝ)..(850/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(35973/184960000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1360/37:ℝ) (850/23:ℝ) (-(2917/2:ℝ)) (153/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_290 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_291 (x : ℝ) (hl : (850/23:ℝ) < x) (hr : x < (37:ℝ)) :
    innerR 7 6 (3/40) x = (-1416:ℝ) + (371/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (85:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (68:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) (1400:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((37:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1330:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1474:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((37:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1400:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1330:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((37:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1400:ℝ) * (((37:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1330:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((37:ℝ) + (-1:ℝ) * x))) ((1474:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_291 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (850/23:ℝ) (37:ℝ) ∧
    ∫ x in (850/23:ℝ)..(37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(37513/989102500:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (850/23:ℝ) (37:ℝ) (-1416:ℝ) (371/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_291 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_292 (x : ℝ) (hl : (37:ℝ) < x) (hr : x < (1600/43:ℝ)) :
    innerR 7 6 (3/40) x = (-1453:ℝ) + (145/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (85:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (68:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-37:ℝ) + (1:ℝ) * x) (1260:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-37:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1330:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1474:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-37:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1260:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1330:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-37:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1260:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1330:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-37:ℝ) + (1:ℝ) * x))) ((1474:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_292 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (37:ℝ) (1600/43:ℝ) ∧
    ∫ x in (37:ℝ)..(1600/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(3100707/7009280000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (37:ℝ) (1600/43:ℝ) (-1453:ℝ) (145/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_292 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_293 (x : ℝ) (hl : (1600/43:ℝ) < x) (hr : x < (1380/37:ℝ)) :
    innerR 7 6 (3/40) x = (-1333:ℝ) + (1321/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (85:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (68:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1260:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) (1407:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) (1474:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) ((1260:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1407:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((1260:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1407:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1474:ℝ) * ((1/2:ℝ)-((-37:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_293 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1600/43:ℝ) (1380/37:ℝ) ∧
    ∫ x in (1600/43:ℝ)..(1380/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(4261397/24376320000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1600/43:ℝ) (1380/37:ℝ) (-1333:ℝ) (1321/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_293 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_294 (x : ℝ) (hl : (1380/37:ℝ) < x) (hr : x < (860/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1402:ℝ) + (279/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (85:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (69:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1260:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) (1407:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) (1474:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) ((1260:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1407:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((1260:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1407:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1474:ℝ) * ((1/2:ℝ)-((-37:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_294 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1380/37:ℝ) (860/23:ℝ) ∧
    ∫ x in (1380/37:ℝ)..(860/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(316591/1760617800:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1380/37:ℝ) (860/23:ℝ) (-1402:ℝ) (279/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_294 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_295 (x : ℝ) (hl : (860/23:ℝ) < x) (hr : x < (75/2:ℝ)) :
    innerR 7 6 (3/40) x = (-1359:ℝ) + (1349/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (86:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (69:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1349:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) (1496:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) (1564:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (36:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((-37:ℝ) + (1:ℝ) * x) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1496:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-37:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1496:ℝ) * (((-37:ℝ) + (1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1564:ℝ) * ((1/2:ℝ)-((-37:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_295 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (860/23:ℝ) (75/2:ℝ) ∧
    ∫ x in (860/23:ℝ)..(75/2:ℝ), innerR 7 6 (3/40) x / x^3 = (-(11041/55470000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (860/23:ℝ) (75/2:ℝ) (-1359:ℝ) (1349/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_295 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_296 (x : ℝ) (hl : (75/2:ℝ) < x) (hr : x < (1620/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(2793/2:ℝ)) + (1389/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (86:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (69:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1349:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) (1496:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1428:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (38:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1496:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1496:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1428:ℝ) * ((1/2:ℝ)-((38:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_296 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (75/2:ℝ) (1620/43:ℝ) ∧
    ∫ x in (75/2:ℝ)..(1620/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(26231/87480000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (75/2:ℝ) (1620/43:ℝ) (-(2793/2:ℝ)) (1389/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_296 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_297 (x : ℝ) (hl : (1620/43:ℝ) < x) (hr : x < (870/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(2793/2:ℝ)) + (1389/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (86:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (69:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1349:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) (1496:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1428:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (38:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1496:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1349:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1496:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1428:ℝ) * ((1/2:ℝ)-((38:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_297 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1620/43:ℝ) (870/23:ℝ) ∧
    ∫ x in (1620/43:ℝ)..(870/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(28417/117713088:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1620/43:ℝ) (870/23:ℝ) (-(2793/2:ℝ)) (1389/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_297 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_298 (x : ℝ) (hl : (870/23:ℝ) < x) (hr : x < (1400/37:ℝ)) :
    innerR 7 6 (3/40) x = (-1353:ℝ) + (1343/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (87:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (69:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1440:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) (1587:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (1518:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (38:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) ((38:ℝ) + (-1:ℝ) * x) ((1440:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((1587:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((38:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1440:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(1587:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-((3:ℝ) + (-(3/40:ℝ)) * x))) ((1518:ℝ) * ((1/2:ℝ)-((38:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_298 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (870/23:ℝ) (1400/37:ℝ) ∧
    ∫ x in (870/23:ℝ)..(1400/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(59233/3296720000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (870/23:ℝ) (1400/37:ℝ) (-1353:ℝ) (1343/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_298 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_299 (x : ℝ) (hl : (1400/37:ℝ) < x) (hr : x < (38:ℝ)) :
    innerR 7 6 (3/40) x = (-1528:ℝ) + (191/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (87:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (70:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((38:ℝ) + (-1:ℝ) * x) (1440:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((38:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1368:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (38:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1518:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (37:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (38:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((38:ℝ) + (-1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1440:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1368:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((38:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1440:ℝ) * (((38:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1368:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((38:ℝ) + (-1:ℝ) * x))) ((1518:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_299 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1400/37:ℝ) (38:ℝ) ∧
    ∫ x in (1400/37:ℝ)..(38:ℝ), innerR 7 6 (3/40) x / x^3 = (-(41829/176890000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1400/37:ℝ) (38:ℝ) (-1528:ℝ) (191/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_299 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
lemma chunk_14 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1320/37:ℝ) (38:ℝ) ∧
    ∫ x in (1320/37:ℝ)..(38:ℝ), innerR 7 6 (3/40) x / x^3 = (-(4271842881623818948289/1341427252053562891176960:ℝ)) := by
  have h := i_280
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1540/43:ℝ) (36:ℝ) (-(1021/15523200:ℝ)) (-(1513/24012450:ℝ)) h i_281
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (36:ℝ) (830/23:ℝ) (-(4039/31363200:ℝ)) (-(64013/446407200:ℝ)) h i_282
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (830/23:ℝ) (1340/37:ℝ) (-(6534107/24006787200:ℝ)) (-(9929513/49479553600:ℝ)) h i_283
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1340/37:ℝ) (1560/43:ℝ) (-(613952839/1298391177600:ℝ)) (-(806239/8739544320:ℝ)) h i_284
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1560/43:ℝ) (73/2:ℝ) (-(411279189/727788089600:ℝ)) (-(618355/2074984704:ℝ)) h i_285
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (73/2:ℝ) (840/23:ℝ) (-(289686004351/335629274666400:ℝ)) (-(102211/3760142400:ℝ)) h i_286
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (840/23:ℝ) (110/3:ℝ) (-(401141292397/450570807086400:ℝ)) (-(7327/42688800:ℝ)) h i_287
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (110/3:ℝ) (1580/43:ℝ) (-(68353735829/64367258155200:ℝ)) (-(102809/1208257600:ℝ)) h i_288
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1580/43:ℝ) (1360/37:ℝ) (-(28798571231747/25107253634162700:ℝ)) (-(617039/46173414400:ℝ)) h i_289
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1360/37:ℝ) (850/23:ℝ) (-(345370403282741/297634201709644800:ℝ)) (-(35973/184960000:ℝ)) h i_290
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (850/23:ℝ) (37:ℝ) (-(2520359298269789/1860213760685280000:ℝ)) (-(37513/989102500:ℝ)) h i_291
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (37:ℝ) (1600/43:ℝ) (-(41728896912216257/29960383980919392000:ℝ)) (-(3100707/7009280000:ℝ)) h i_292
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1600/43:ℝ) (1380/37:ℝ) (-(237762259195644749/129558417214786560000:ℝ)) (-(4261397/24376320000:ℝ)) h i_293
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1380/37:ℝ) (860/23:ℝ) (-(688787843372376173/342682013533110451200:ℝ)) (-(316591/1760617800:ℝ)) h i_294
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (860/23:ℝ) (75/2:ℝ) (-(60326300595028377731/27548654044466140185600:ℝ)) (-(11041/55470000:ℝ)) h i_295
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (75/2:ℝ) (1620/43:ℝ) (-(38261458983812481569/16016659328177988480000:ℝ)) (-(26231/87480000:ℝ)) h i_296
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1620/43:ℝ) (870/23:ℝ) (-(16743312989961567571/6227277146795601921024:ℝ)) (-(28417/117713088:ℝ)) h i_297
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (870/23:ℝ) (1400/37:ℝ) (-(63149872530516667769/21552016791996301298688:ℝ)) (-(59233/3296720000:ℝ)) h i_298
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1320/37:ℝ) (1400/37:ℝ) (38:ℝ) (-(9585338822767968154291/3251381843620131661440000:ℝ)) (-(41829/176890000:ℝ)) h i_299
  norm_num at h
  norm_num at h ⊢
  exact h
end MarginPieces
