import MarginPieces
/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
namespace MarginPieces
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_200 (x : ℝ) (hl : (53/2:ℝ) < x) (hr : x < (1140/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(1495/2:ℝ)) + (949/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (459:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) (576:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (528:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) ((459:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((576:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((459:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(576:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((528:ℝ) * ((1/2:ℝ)-((27:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_200 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (53/2:ℝ) (1140/43:ℝ) ∧
    ∫ x in (53/2:ℝ)..(1140/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(1081847/14602305600:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (53/2:ℝ) (1140/43:ℝ) (-(1495/2:ℝ)) (949/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_200 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_201 (x : ℝ) (hl : (1140/43:ℝ) < x) (hr : x < (610/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(1495/2:ℝ)) + (949/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (459:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) (576:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (528:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) ((459:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((576:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((459:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(576:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((528:ℝ) * ((1/2:ℝ)-((27:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_201 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1140/43:ℝ) (610/23:ℝ) ∧
    ∫ x in (1140/43:ℝ)..(610/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(1241929/19343246400:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1140/43:ℝ) (610/23:ℝ) (-(1495/2:ℝ)) (949/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_201 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_202 (x : ℝ) (hl : (610/23:ℝ) < x) (hr : x < (80/3:ℝ)) :
    innerR 7 6 (3/40) x = (-717:ℝ) + (903/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (520:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) (637:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (588:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((27:ℝ) + (-1:ℝ) * x) ((520:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((637:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((520:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(637:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((588:ℝ) * ((1/2:ℝ)-((27:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_202 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (610/23:ℝ) (80/3:ℝ) ∧
    ∫ x in (610/23:ℝ)..(80/3:ℝ), innerR 7 6 (3/40) x / x^3 = (-(42807/47628800:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (610/23:ℝ) (80/3:ℝ) (-717:ℝ) (903/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_202 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_203 (x : ℝ) (hl : (80/3:ℝ) < x) (hr : x < (620/23:ℝ)) :
    innerR 7 6 (3/40) x = (-749:ℝ) + (279/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (736:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((27:ℝ) + (-1:ℝ) * x) (637:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (588:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((27:ℝ) + (-1:ℝ) * x) ((736:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((637:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((736:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(637:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((588:ℝ) * ((1/2:ℝ)-((27:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_203 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (80/3:ℝ) (620/23:ℝ) ∧
    ∫ x in (80/3:ℝ)..(620/23:ℝ), innerR 7 6 (3/40) x / x^3 = (6883/2460160:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (80/3:ℝ) (620/23:ℝ) (-749:ℝ) (279/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_203 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_204 (x : ℝ) (hl : (620/23:ℝ) < x) (hr : x < (1160/43:ℝ)) :
    innerR 7 6 (3/40) x = (-718:ℝ) + (1349/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (799:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((27:ℝ) + (-1:ℝ) * x) (700:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (650:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((27:ℝ) + (-1:ℝ) * x) ((799:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((700:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((799:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(700:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((650:ℝ) * ((1/2:ℝ)-((27:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_204 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (620/23:ℝ) (1160/43:ℝ) ∧
    ∫ x in (620/23:ℝ)..(1160/43:ℝ), innerR 7 6 (3/40) x / x^3 = (127649/646560800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (620/23:ℝ) (1160/43:ℝ) (-718:ℝ) (1349/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_204 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_205 (x : ℝ) (hl : (1160/43:ℝ) < x) (hr : x < (27:ℝ)) :
    innerR 7 6 (3/40) x = (-631:ℝ) + (61/2:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (26:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (53:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) (799:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((27:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (752:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (650:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((27:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((799:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((752:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((27:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((799:ℝ) * (((27:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(752:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((27:ℝ) + (-1:ℝ) * x))) ((650:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_205 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1160/43:ℝ) (27:ℝ) ∧
    ∫ x in (1160/43:ℝ)..(27:ℝ), innerR 7 6 (3/40) x / x^3 = (445969/1961884800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1160/43:ℝ) (27:ℝ) (-631:ℝ) (61/2:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_205 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_206 (x : ℝ) (hl : (27:ℝ) < x) (hr : x < (1000/37:ℝ)) :
    innerR 7 6 (3/40) x = (-658:ℝ) + (593/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (54:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-27:ℝ) + (1:ℝ) * x) (705:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-27:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (752:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (650:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-27:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((705:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((752:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-27:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((705:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-(0:ℝ))+(752:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-27:ℝ) + (1:ℝ) * x))) ((650:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_206 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (27:ℝ) (1000/37:ℝ) ∧
    ∫ x in (27:ℝ)..(1000/37:ℝ), innerR 7 6 (3/40) x / x^3 = (142879/729000000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (27:ℝ) (1000/37:ℝ) (-658:ℝ) (593/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_206 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_207 (x : ℝ) (hl : (1000/37:ℝ) < x) (hr : x < (630/23:ℝ)) :
    innerR 7 6 (3/40) x = (-783:ℝ) + (1371/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (54:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (50:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (705:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) (600:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) (650:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) ((705:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((600:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((705:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(600:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((650:ℝ) * ((1/2:ℝ)-((-27:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_207 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1000/37:ℝ) (630/23:ℝ) ∧
    ∫ x in (1000/37:ℝ)..(630/23:ℝ), innerR 7 6 (3/40) x / x^3 = (795181/294000000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1000/37:ℝ) (630/23:ℝ) (-783:ℝ) (1371/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_207 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_208 (x : ℝ) (hl : (630/23:ℝ) < x) (hr : x < (1180/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(1503/2:ℝ)) + (265/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (54:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (50:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (768:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) (663:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) (714:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((663:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(663:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((714:ℝ) * ((1/2:ℝ)-((-27:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_208 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (630/23:ℝ) (1180/43:ℝ) ∧
    ∫ x in (630/23:ℝ)..(1180/43:ℝ), innerR 7 6 (3/40) x / x^3 = (188809/491238720:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (630/23:ℝ) (1180/43:ℝ) (-(1503/2:ℝ)) (265/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_208 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_209 (x : ℝ) (hl : (1180/43:ℝ) < x) (hr : x < (55/2:ℝ)) :
    innerR 7 6 (3/40) x = (-(1503/2:ℝ)) + (265/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (54:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (50:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (768:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) (663:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) (714:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (26:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-27:ℝ) + (1:ℝ) * x) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((663:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-27:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(663:ℝ) * (((-27:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((714:ℝ) * ((1/2:ℝ)-((-27:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_209 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1180/43:ℝ) (55/2:ℝ) ∧
    ∫ x in (1180/43:ℝ)..(55/2:ℝ), innerR 7 6 (3/40) x / x^3 = (59903/134784320:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1180/43:ℝ) (55/2:ℝ) (-(1503/2:ℝ)) (265/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_209 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_210 (x : ℝ) (hl : (55/2:ℝ) < x) (hr : x < (1020/37:ℝ)) :
    innerR 7 6 (3/40) x = (-779:ℝ) + (273/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (55:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (50:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (768:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) (663:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (612:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((663:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(663:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((612:ℝ) * ((1/2:ℝ)-((28:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_210 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (55/2:ℝ) (1020/37:ℝ) ∧
    ∫ x in (55/2:ℝ)..(1020/37:ℝ), innerR 7 6 (3/40) x / x^3 = (818/1573605:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (55/2:ℝ) (1020/37:ℝ) (-779:ℝ) (273/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_210 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_211 (x : ℝ) (hl : (1020/37:ℝ) < x) (hr : x < (640/23:ℝ)) :
    innerR 7 6 (3/40) x = (-830:ℝ) + (1439/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (55:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (51:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (768:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) (663:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (612:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((663:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((768:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(663:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((612:ℝ) * ((1/2:ℝ)-((28:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_211 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1020/37:ℝ) (640/23:ℝ) ∧
    ∫ x in (1020/37:ℝ)..(640/23:ℝ), innerR 7 6 (3/40) x / x^3 = (2156759/1065369600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1020/37:ℝ) (640/23:ℝ) (-830:ℝ) (1439/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_211 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_212 (x : ℝ) (hl : (640/23:ℝ) < x) (hr : x < (1200/43:ℝ)) :
    innerR 7 6 (3/40) x = (-798:ℝ) + (1393/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (55:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (51:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (833:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) (728:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (676:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((28:ℝ) + (-1:ℝ) * x) ((833:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((728:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((28:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((833:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(728:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((676:ℝ) * ((1/2:ℝ)-((28:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_212 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (640/23:ℝ) (1200/43:ℝ) ∧
    ∫ x in (640/23:ℝ)..(1200/43:ℝ), innerR 7 6 (3/40) x / x^3 = (6601/10240000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (640/23:ℝ) (1200/43:ℝ) (-798:ℝ) (1393/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_212 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_213 (x : ℝ) (hl : (1200/43:ℝ) < x) (hr : x < (28:ℝ)) :
    innerR 7 6 (3/40) x = (-708:ℝ) + (158/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (27:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (55:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (51:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((28:ℝ) + (-1:ℝ) * x) (833:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((28:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (784:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (676:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((28:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((833:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((784:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((28:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((833:ℝ) * (((28:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(784:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((28:ℝ) + (-1:ℝ) * x))) ((676:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_213 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1200/43:ℝ) (28:ℝ) ∧
    ∫ x in (1200/43:ℝ)..(28:ℝ), innerR 7 6 (3/40) x / x^3 = (2927/3920000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1200/43:ℝ) (28:ℝ) (-708:ℝ) (158/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_213 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_214 (x : ℝ) (hl : (28:ℝ) < x) (hr : x < (1040/37:ℝ)) :
    innerR 7 6 (3/40) x = (-736:ℝ) + (123/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (56:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (51:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) (735:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-28:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (784:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (676:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((735:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((784:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-28:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((735:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-(0:ℝ))+(784:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-28:ℝ) + (1:ℝ) * x))) ((676:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_214 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (28:ℝ) (1040/37:ℝ) ∧
    ∫ x in (28:ℝ)..(1040/37:ℝ), innerR 7 6 (3/40) x / x^3 = (8217/13249600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (28:ℝ) (1040/37:ℝ) (-736:ℝ) (123/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_214 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_215 (x : ℝ) (hl : (1040/37:ℝ) < x) (hr : x < (650/23:ℝ)) :
    innerR 7 6 (3/40) x = (-866:ℝ) + (283/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (56:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (52:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (735:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) (624:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) (676:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) ((735:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((624:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((735:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(624:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((676:ℝ) * ((1/2:ℝ)-((-28:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_215 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1040/37:ℝ) (650/23:ℝ) ∧
    ∫ x in (1040/37:ℝ)..(650/23:ℝ), innerR 7 6 (3/40) x / x^3 = (24173/27040000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1040/37:ℝ) (650/23:ℝ) (-866:ℝ) (283/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_215 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_216 (x : ℝ) (hl : (650/23:ℝ) < x) (hr : x < (85/3:ℝ)) :
    innerR 7 6 (3/40) x = (-(1667/2:ℝ)) + (1369/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (56:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (52:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (800:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) (689:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) (742:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((742:ℝ) * ((1/2:ℝ)-((-28:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_216 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (650/23:ℝ) (85/3:ℝ) ∧
    ∫ x in (650/23:ℝ)..(85/3:ℝ), innerR 7 6 (3/40) x / x^3 = (105409/244205000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (650/23:ℝ) (85/3:ℝ) (-(1667/2:ℝ)) (1369/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_216 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_217 (x : ℝ) (hl : (85/3:ℝ) < x) (hr : x < (1220/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(1667/2:ℝ)) + (1369/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (56:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (52:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (800:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) (689:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) (742:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((742:ℝ) * ((1/2:ℝ)-((-28:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_217 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (85/3:ℝ) (1220/43:ℝ) ∧
    ∫ x in (85/3:ℝ)..(1220/43:ℝ), innerR 7 6 (3/40) x / x^3 = (80097/344118080:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (85/3:ℝ) (1220/43:ℝ) (-(1667/2:ℝ)) (1369/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_217 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_218 (x : ℝ) (hl : (1220/43:ℝ) < x) (hr : x < (57/2:ℝ)) :
    innerR 7 6 (3/40) x = (-(1667/2:ℝ)) + (1369/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (56:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (52:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (800:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) (689:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) (742:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (27:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-28:ℝ) + (1:ℝ) * x) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-28:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(689:ℝ) * (((-28:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((742:ℝ) * ((1/2:ℝ)-((-28:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_218 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1220/43:ℝ) (57/2:ℝ) ∧
    ∫ x in (1220/43:ℝ)..(57/2:ℝ), innerR 7 6 (3/40) x / x^3 = (15034019/19343246400:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1220/43:ℝ) (57/2:ℝ) (-(1667/2:ℝ)) (1369/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_218 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_219 (x : ℝ) (hl : (57/2:ℝ) < x) (hr : x < (1060/37:ℝ)) :
    innerR 7 6 (3/40) x = (-862:ℝ) + (1409/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (28:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (57:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (52:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (800:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((29:ℝ) + (-1:ℝ) * x) (689:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((29:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (636:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (28:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (29:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((29:ℝ) + (-1:ℝ) * x) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((689:ℝ) * (((29:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((29:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((800:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(689:ℝ) * (((29:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((636:ℝ) * ((1/2:ℝ)-((29:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_219 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (57/2:ℝ) (1060/37:ℝ) ∧
    ∫ x in (57/2:ℝ)..(1060/37:ℝ), innerR 7 6 (3/40) x / x^3 = (6723101/7301152800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (57/2:ℝ) (1060/37:ℝ) (-862:ℝ) (1409/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_219 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
lemma chunk_10 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (53/2:ℝ) (1060/37:ℝ) ∧
    ∫ x in (53/2:ℝ)..(1060/37:ℝ), innerR 7 6 (3/40) x / x^3 = (787606742817033263/57376010167572096000:ℝ) := by
  have h := i_200
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1140/43:ℝ) (610/23:ℝ) (-(1081847/14602305600:ℝ)) (-(1241929/19343246400:ℝ)) h i_201
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (610/23:ℝ) (80/3:ℝ) (-(144547/1045228900:ℝ)) (-(42807/47628800:ℝ)) h i_202
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (80/3:ℝ) (620/23:ℝ) (-(2274539/2193267200:ℝ)) (6883/2460160:ℝ) h i_203
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (620/23:ℝ) (1160/43:ℝ) (231946491/131733111200:ℝ) (127649/646560800:ℝ) h i_204
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1160/43:ℝ) (27:ℝ) (874756159/446723977900:ℝ) (445969/1961884800:ℝ) h i_205
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (27:ℝ) (1000/37:ℝ) (785352354647/359350929532800:ℝ) (142879/729000000:ℝ) h i_206
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1000/37:ℝ) (630/23:ℝ) (733695706577/308085502000000:ℝ) (795181/294000000:ℝ) h i_207
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (630/23:ℝ) (1180/43:ℝ) (921380550599/181154275176000:ℝ) (188809/491238720:ℝ) h i_208
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1180/43:ℝ) (55/2:ℝ) (369610483365869/67564074845106000:ℝ) (59903/134784320:ℝ) h i_209
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (55/2:ℝ) (1020/37:ℝ) (55565923595891/9394143126984000:ℝ) (818/1573605:ℝ) h i_210
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1020/37:ℝ) (640/23:ℝ) (529388787478003/82269920112072000:ℝ) (2156759/1065369600:ℝ) h i_211
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (640/23:ℝ) (1200/43:ℝ) (31440019310626457/3716664626239488000:ℝ) (6601/10240000:ℝ) h i_212
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1200/43:ℝ) (28:ℝ) (10573715238605401/1161457695699840000:ℝ) (2927/3920000:ℝ) h i_213
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (28:ℝ) (1040/37:ℝ) (16017339432373787/1626040773979776000:ℝ) (8217/13249600:ℝ) h i_214
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1040/37:ℝ) (650/23:ℝ) (411050505799875269/39257270114654592000:ℝ) (24173/27040000:ℝ) h i_215
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (650/23:ℝ) (85/3:ℝ) (2230727009487827797/196286350573272960000:ℝ) (105409/244205000:ℝ) h i_216
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (85/3:ℝ) (1220/43:ℝ) (605579841258992869/51336430149932928000:ℝ) (80097/344118080:ℝ) h i_217
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (1220/43:ℝ) (57/2:ℝ) (2215839066003257777/184207190537994624000:ℝ) (15034019/19343246400:ℝ) h i_218
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (53/2:ℝ) (57/2:ℝ) (1060/37:ℝ) (13960693552584341917/1090144193183869824000:ℝ) (6723101/7301152800:ℝ) h i_219
  norm_num at h
  norm_num at h ⊢
  exact h
end MarginPieces
