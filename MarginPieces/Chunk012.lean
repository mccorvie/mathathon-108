import MarginPieces
/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
namespace MarginPieces
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_240 (x : ℝ) (hl : (1340/43:ℝ) < x) (hr : x < (720/23:ℝ)) :
    innerR 7 6 (3/40) x = (-954:ℝ) + (131/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (71:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (57:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-31:ℝ) + (1:ℝ) * x) (896:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-31:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (952:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (30:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (826:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (30:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-31:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((896:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((952:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-31:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((896:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-(0:ℝ))+(952:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-31:ℝ) + (1:ℝ) * x))) ((826:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_240 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1340/43:ℝ) (720/23:ℝ) ∧
    ∫ x in (1340/43:ℝ)..(720/23:ℝ), innerR 7 6 (3/40) x / x^3 = (27587/86188800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1340/43:ℝ) (720/23:ℝ) (-954:ℝ) (131/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_240 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_241 (x : ℝ) (hl : (720/23:ℝ) < x) (hr : x < (1160/37:ℝ)) :
    innerR 7 6 (3/40) x = (-918:ℝ) + (158/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (57:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-31:ℝ) + (1:ℝ) * x) (969:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-31:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1026:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (30:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (900:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (30:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-31:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((969:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1026:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-31:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((969:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1026:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-31:ℝ) + (1:ℝ) * x))) ((900:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_241 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (720/23:ℝ) (1160/37:ℝ) ∧
    ∫ x in (720/23:ℝ)..(1160/37:ℝ), innerR 7 6 (3/40) x / x^3 = (5329/48441600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (720/23:ℝ) (1160/37:ℝ) (-918:ℝ) (158/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_241 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_242 (x : ℝ) (hl : (1160/37:ℝ) < x) (hr : x < (63/2:ℝ)) :
    innerR 7 6 (3/40) x = (-1063:ℝ) + (1449/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (62:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (58:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (969:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-31:ℝ) + (1:ℝ) * x) (840:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-31:ℝ) + (1:ℝ) * x) (1/2:ℝ) (900:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (30:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-31:ℝ) + (1:ℝ) * x) ((969:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((840:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-31:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((969:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(840:ℝ) * (((-31:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((900:ℝ) * ((1/2:ℝ)-((-31:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_242 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1160/37:ℝ) (63/2:ℝ) ∧
    ∫ x in (1160/37:ℝ)..(63/2:ℝ), innerR 7 6 (3/40) x / x^3 = (3856963/10681372800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1160/37:ℝ) (63/2:ℝ) (-1063:ℝ) (1449/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_242 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_243 (x : ℝ) (hl : (63/2:ℝ) < x) (hr : x < (1360/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(2189/2:ℝ)) + (1489/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (58:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (969:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((32:ℝ) + (-1:ℝ) * x) (840:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((32:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (780:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((32:ℝ) + (-1:ℝ) * x) ((969:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((840:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((969:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(840:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((780:ℝ) * ((1/2:ℝ)-((32:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_243 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (63/2:ℝ) (1360/43:ℝ) ∧
    ∫ x in (63/2:ℝ)..(1360/43:ℝ), innerR 7 6 (3/40) x / x^3 = (9610381/29364249600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (63/2:ℝ) (1360/43:ℝ) (-(2189/2:ℝ)) (1489/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_243 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_244 (x : ℝ) (hl : (1360/43:ℝ) < x) (hr : x < (95/3:ℝ)) :
    innerR 7 6 (3/40) x = (-(1985/2:ℝ)) + (34:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (58:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) (969:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (912:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (780:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((969:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((912:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((969:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(912:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) ((780:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_244 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1360/43:ℝ) (95/3:ℝ) ∧
    ∫ x in (1360/43:ℝ)..(95/3:ℝ), innerR 7 6 (3/40) x / x^3 = (54547/534164480:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1360/43:ℝ) (95/3:ℝ) (-(1985/2:ℝ)) (34:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_244 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_245 (x : ℝ) (hl : (95/3:ℝ) < x) (hr : x < (730/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(1985/2:ℝ)) + (34:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (72:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (58:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) (969:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (912:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (780:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((969:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((912:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((969:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(912:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) ((780:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_245 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (95/3:ℝ) (730/23:ℝ) ∧
    ∫ x in (95/3:ℝ)..(730/23:ℝ), innerR 7 6 (3/40) x / x^3 = (29889/153901520:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (95/3:ℝ) (730/23:ℝ) (-(1985/2:ℝ)) (34:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_245 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_246 (x : ℝ) (hl : (730/23:ℝ) < x) (hr : x < (1180/37:ℝ)) :
    innerR 7 6 (3/40) x = (-956:ℝ) + (657/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (58:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) (1044:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (986:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (854:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1044:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1044:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) ((854:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_246 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (730/23:ℝ) (1180/37:ℝ) ∧
    ∫ x in (730/23:ℝ)..(1180/37:ℝ), innerR 7 6 (3/40) x / x^3 = (3137277/7420099600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (730/23:ℝ) (1180/37:ℝ) (-956:ℝ) (657/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_246 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_247 (x : ℝ) (hl : (1180/37:ℝ) < x) (hr : x < (32:ℝ)) :
    innerR 7 6 (3/40) x = (-1015:ℝ) + (347/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (31:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (63:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (59:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) (1044:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (986:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (854:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((32:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1044:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1044:ℝ) * (((32:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((32:ℝ) + (-1:ℝ) * x))) ((854:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_247 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1180/37:ℝ) (32:ℝ) ∧
    ∫ x in (1180/37:ℝ)..(32:ℝ), innerR 7 6 (3/40) x / x^3 = (55271/178227200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1180/37:ℝ) (32:ℝ) (-1015:ℝ) (347/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_247 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_248 (x : ℝ) (hl : (32:ℝ) < x) (hr : x < (1380/43:ℝ)) :
    innerR 7 6 (3/40) x = (-1047:ℝ) + (677/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (59:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) (928:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (986:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (854:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((928:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((928:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))+(986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) ((854:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_248 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (32:ℝ) (1380/43:ℝ) ∧
    ∫ x in (32:ℝ)..(1380/43:ℝ), innerR 7 6 (3/40) x / x^3 = (347/3250176:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (32:ℝ) (1380/43:ℝ) (-1047:ℝ) (677/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_248 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_249 (x : ℝ) (hl : (1380/43:ℝ) < x) (hr : x < (740/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1047:ℝ) + (677/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (73:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (59:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) (928:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (986:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (854:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((928:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((928:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))+(986:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) ((854:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_249 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1380/43:ℝ) (740/23:ℝ) ∧
    ∫ x in (1380/43:ℝ)..(740/23:ℝ), innerR 7 6 (3/40) x / x^3 = (10783/108630150:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1380/43:ℝ) (740/23:ℝ) (-1047:ℝ) (677/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_249 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_250 (x : ℝ) (hl : (740/23:ℝ) < x) (hr : x < (1200/37:ℝ)) :
    innerR 7 6 (3/40) x = (-1010:ℝ) + (327/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (59:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) (1003:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1062:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (930:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1003:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1062:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1003:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1062:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-32:ℝ) + (1:ℝ) * x))) ((930:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_250 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (740/23:ℝ) (1200/37:ℝ) ∧
    ∫ x in (740/23:ℝ)..(1200/37:ℝ), innerR 7 6 (3/40) x / x^3 = (139997/394272000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (740/23:ℝ) (1200/37:ℝ) (-1010:ℝ) (327/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_250 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_251 (x : ℝ) (hl : (1200/37:ℝ) < x) (hr : x < (65/2:ℝ)) :
    innerR 7 6 (3/40) x = (-1160:ℝ) + (1493/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (64:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1003:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((-32:ℝ) + (1:ℝ) * x) (868:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-32:ℝ) + (1:ℝ) * x) (1/2:ℝ) (930:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (31:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((-32:ℝ) + (1:ℝ) * x) ((1003:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((868:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-32:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((1003:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(868:ℝ) * (((-32:ℝ) + (1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((930:ℝ) * ((1/2:ℝ)-((-32:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_251 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1200/37:ℝ) (65/2:ℝ) ∧
    ∫ x in (1200/37:ℝ)..(65/2:ℝ), innerR 7 6 (3/40) x / x^3 = (2489/24336000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1200/37:ℝ) (65/2:ℝ) (-1160:ℝ) (1493/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_251 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_252 (x : ℝ) (hl : (65/2:ℝ) < x) (hr : x < (1400/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(2385/2:ℝ)) + (1533/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1003:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) ((33:ℝ) + (-1:ℝ) * x) (868:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((33:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (806:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) ((33:ℝ) + (-1:ℝ) * x) ((1003:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((868:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((1003:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(868:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-((-2:ℝ) + (3/40:ℝ) * x))) ((806:ℝ) * ((1/2:ℝ)-((33:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_252 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (65/2:ℝ) (1400/43:ℝ) ∧
    ∫ x in (65/2:ℝ)..(1400/43:ℝ), innerR 7 6 (3/40) x / x^3 = (24249/264992000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (65/2:ℝ) (1400/43:ℝ) (-(2385/2:ℝ)) (1533/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_252 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_253 (x : ℝ) (hl : (1400/43:ℝ) < x) (hr : x < (750/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(2175/2:ℝ)) + (351/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (74:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) (1003:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (944:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (806:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1003:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((944:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1003:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(944:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) ((806:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_253 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1400/43:ℝ) (750/23:ℝ) ∧
    ∫ x in (1400/43:ℝ)..(750/23:ℝ), innerR 7 6 (3/40) x / x^3 = (1931/23520000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1400/43:ℝ) (750/23:ℝ) (-(2175/2:ℝ)) (351/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_253 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_254 (x : ℝ) (hl : (750/23:ℝ) < x) (hr : x < (1220/37:ℝ)) :
    innerR 7 6 (3/40) x = (-1050:ℝ) + (679/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (60:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) (1080:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1020:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (882:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1080:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1080:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) ((882:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_254 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (750/23:ℝ) (1220/37:ℝ) ∧
    ∫ x in (750/23:ℝ)..(1220/37:ℝ), innerR 7 6 (3/40) x / x^3 = (1519/2325625:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (750/23:ℝ) (1220/37:ℝ) (-1050:ℝ) (679/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_254 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_255 (x : ℝ) (hl : (1220/37:ℝ) < x) (hr : x < (33:ℝ)) :
    innerR 7 6 (3/40) x = (-1111:ℝ) + (179/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (32:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (65:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) (1080:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1020:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (882:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((33:ℝ) + (-1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1080:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1080:ℝ) * (((33:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((33:ℝ) + (-1:ℝ) * x))) ((882:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_255 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1220/37:ℝ) (33:ℝ) ∧
    ∫ x in (1220/37:ℝ)..(33:ℝ), innerR 7 6 (3/40) x / x^3 = (3103/58940640:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1220/37:ℝ) (33:ℝ) (-1111:ℝ) (179/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_255 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_256 (x : ℝ) (hl : (33:ℝ) < x) (hr : x < (1420/43:ℝ)) :
    innerR 7 6 (3/40) x = (-1144:ℝ) + (699/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (33:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) (960:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1020:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (882:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((960:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((960:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) ((882:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_256 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (33:ℝ) (1420/43:ℝ) ∧
    ∫ x in (33:ℝ)..(1420/43:ℝ), innerR 7 6 (3/40) x / x^3 = (1259/199623600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (33:ℝ) (1420/43:ℝ) (-1144:ℝ) (699/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_256 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_257 (x : ℝ) (hl : (1420/43:ℝ) < x) (hr : x < (760/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1144:ℝ) + (699/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (75:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (33:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) (960:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1020:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (882:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((960:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((960:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1020:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) ((882:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_257 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1420/43:ℝ) (760/23:ℝ) ∧
    ∫ x in (1420/43:ℝ)..(760/23:ℝ), innerR 7 6 (3/40) x / x^3 = (8589/1455840800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (1420/43:ℝ) (760/23:ℝ) (-1144:ℝ) (699/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_257 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_258 (x : ℝ) (hl : (760/23:ℝ) < x) (hr : x < (100/3:ℝ)) :
    innerR 7 6 (3/40) x = (-1106:ℝ) + (169/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (76:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (33:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) (1037:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) (1098:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (960:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) ((-2:ℝ) + (3/40:ℝ) * x) ((1037:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1098:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-2:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((1037:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1098:ℝ) * (((-2:ℝ) + (3/40:ℝ) * x)-((-33:ℝ) + (1:ℝ) * x))) ((960:ℝ) * ((1/2:ℝ)-((-2:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_258 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (760/23:ℝ) (100/3:ℝ) ∧
    ∫ x in (760/23:ℝ)..(100/3:ℝ), innerR 7 6 (3/40) x / x^3 = (1803/14440000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (760/23:ℝ) (100/3:ℝ) (-1106:ℝ) (169/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_258 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_259 (x : ℝ) (hl : (100/3:ℝ) < x) (hr : x < (770/23:ℝ)) :
    innerR 7 6 (3/40) x = (-1146:ℝ) + (35:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (76:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (33:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (2:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (66:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (61:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) (1037:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-33:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1098:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (1218:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (32:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (33:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (3:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-33:ℝ) + (1:ℝ) * x) ((3:ℝ) + (-(3/40:ℝ)) * x) ((1037:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((1098:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-33:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((3:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((1037:ℝ) * (((-33:ℝ) + (1:ℝ) * x)-(0:ℝ))+(1098:ℝ) * (((3:ℝ) + (-(3/40:ℝ)) * x)-((-33:ℝ) + (1:ℝ) * x))) ((1218:ℝ) * ((1/2:ℝ)-((3:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_259 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (100/3:ℝ) (770/23:ℝ) ∧
    ∫ x in (100/3:ℝ)..(770/23:ℝ), innerR 7 6 (3/40) x / x^3 = (5347/59290000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (100/3:ℝ) (770/23:ℝ) (-1146:ℝ) (35:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_259 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
lemma chunk_12 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1340/43:ℝ) (770/23:ℝ) ∧
    ∫ x in (1340/43:ℝ)..(770/23:ℝ), innerR 7 6 (3/40) x / x^3 = (44434560946127160537853/11341848971103380369640000:ℝ) := by
  have h := i_240
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (720/23:ℝ) (1160/37:ℝ) (27587/86188800:ℝ) (5329/48441600:ℝ) h i_241
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1160/37:ℝ) (63/2:ℝ) (46761941/108727171200:ℝ) (3856963/10681372800:ℝ) h i_242
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (63/2:ℝ) (1360/43:ℝ) (163516909/206675355600:ℝ) (9610381/29364249600:ℝ) h i_243
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1360/43:ℝ) (95/3:ℝ) (2714601751/2427090398208:ℝ) (54547/534164480:ℝ) h i_244
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (95/3:ℝ) (730/23:ℝ) (78635560147/64424973070080:ℝ) (29889/153901520:ℝ) h i_245
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (730/23:ℝ) (1180/37:ℝ) (1345497871867/951026818533120:ℝ) (3137277/7420099600:ℝ) h i_246
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1180/37:ℝ) (32:ℝ) (416670826243079/226748243514643200:ℝ) (55271/178227200:ℝ) h i_247
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (32:ℝ) (1380/43:ℝ) (13206479978827/6149104908871680:ℝ) (347/3250176:ℝ) h i_248
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1380/43:ℝ) (740/23:ℝ) (916689527893931/406609562099139840:ℝ) (10783/108630150:ℝ) h i_249
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (740/23:ℝ) (1200/37:ℝ) (12383769334093519/5261327887653331200:ℝ) (139997/394272000:ℝ) h i_250
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1200/37:ℝ) (65/2:ℝ) (40123724487901/14812296981006000:ℝ) (2489/24336000:ℝ) h i_251
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (65/2:ℝ) (1400/43:ℝ) (33777292210776089/12015735310992067200:ℝ) (24249/264992000:ℝ) h i_252
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1400/43:ℝ) (750/23:ℝ) (187798332610097861/64700113213034208000:ℝ) (1931/23520000:ℝ) h i_253
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (750/23:ℝ) (1220/37:ℝ) (17241985170690107/5776795822592340000:ℝ) (1519/2325625:ℝ) h i_254
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1220/37:ℝ) (33:ℝ) (78197351387366311283/21495457255866097140000:ℝ) (3103/58940640:ℝ) h i_255
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (33:ℝ) (1420/43:ℝ) (3576307614450667127/969057499239865035000:ℝ) (1259/199623600:ℝ) h i_256
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (1420/43:ℝ) (760/23:ℝ) (36117951721999857796589/9770037707336319282870000:ℝ) (8589/1455840800:ℝ) h i_257
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (760/23:ℝ) (100/3:ℝ) (5181269057248314487813/1399319028902365110540000:ℝ) (1803/14440000:ℝ) h i_258
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (1340/43:ℝ) (100/3:ℝ) (770/23:ℝ) (563788434143290753013/147296739884459485320000:ℝ) (5347/59290000:ℝ) h i_259
  norm_num at h
  norm_num at h ⊢
  exact h
end MarginPieces
