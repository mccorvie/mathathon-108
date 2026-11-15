import MarginPieces
/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
namespace MarginPieces
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_140 (x : ℝ) (hl : (820/43:ℝ) < x) (hr : x < (440/23:ℝ)) :
    innerR 7 6 (3/40) x = (-376:ℝ) + (413/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (43:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (35:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-19:ℝ) + (1:ℝ) * x) (204:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-19:ℝ) + (1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) (238:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (18:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (148:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (18:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-19:ℝ) + (1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) ((204:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((238:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((-19:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((204:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-(0:ℝ))+(238:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((-19:ℝ) + (1:ℝ) * x))) ((148:ℝ) * ((1/2:ℝ)-((-1:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_140 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/43:ℝ) (440/23:ℝ) ∧
    ∫ x in (820/43:ℝ)..(440/23:ℝ), innerR 7 6 (3/40) x / x^3 = (26091/162720800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (820/43:ℝ) (440/23:ℝ) (-376:ℝ) (413/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_140 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_141 (x : ℝ) (hl : (440/23:ℝ) < x) (hr : x < (720/37:ℝ)) :
    innerR 7 6 (3/40) x = (-354:ℝ) + (39/2:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (44:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (35:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-19:ℝ) + (1:ℝ) * x) (245:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-19:ℝ) + (1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) (280:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (18:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (190:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (18:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-19:ℝ) + (1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) ((245:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((280:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((-19:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((245:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-(0:ℝ))+(280:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((-19:ℝ) + (1:ℝ) * x))) ((190:ℝ) * ((1/2:ℝ)-((-1:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_141 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (440/23:ℝ) (720/37:ℝ) ∧
    ∫ x in (440/23:ℝ)..(720/37:ℝ), innerR 7 6 (3/40) x / x^3 = (21287/20908800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (440/23:ℝ) (720/37:ℝ) (-354:ℝ) (39/2:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_141 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_142 (x : ℝ) (hl : (720/37:ℝ) < x) (hr : x < (39/2:ℝ)) :
    innerR 7 6 (3/40) x = (-444:ℝ) + (193/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (44:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (245:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) ((-19:ℝ) + (1:ℝ) * x) (152:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-19:ℝ) + (1:ℝ) * x) (1/2:ℝ) (190:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (18:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) ((-19:ℝ) + (1:ℝ) * x) ((245:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((152:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-((-1:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-19:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((245:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(152:ℝ) * (((-19:ℝ) + (1:ℝ) * x)-((-1:ℝ) + (3/40:ℝ) * x))) ((190:ℝ) * ((1/2:ℝ)-((-19:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_142 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (720/37:ℝ) (39/2:ℝ) ∧
    ∫ x in (720/37:ℝ)..(39/2:ℝ), innerR 7 6 (3/40) x / x^3 = (1039/7300800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (720/37:ℝ) (39/2:ℝ) (-444:ℝ) (193/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_142 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_143 (x : ℝ) (hl : (39/2:ℝ) < x) (hr : x < (840/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(927/2:ℝ)) + (201/8:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (44:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (245:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) ((20:ℝ) + (-1:ℝ) * x) (152:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((20:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (114:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) ((20:ℝ) + (-1:ℝ) * x) ((245:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-(0:ℝ))) ((152:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-((-1:ℝ) + (3/40:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((20:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((245:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-(0:ℝ))+(152:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-((-1:ℝ) + (3/40:ℝ) * x))) ((114:ℝ) * ((1/2:ℝ)-((20:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_143 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (39/2:ℝ) (840/43:ℝ) ∧
    ∫ x in (39/2:ℝ)..(840/43:ℝ), innerR 7 6 (3/40) x / x^3 = (6683/52998400:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (39/2:ℝ) (840/43:ℝ) (-(927/2:ℝ)) (201/8:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_143 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_144 (x : ℝ) (hl : (840/43:ℝ) < x) (hr : x < (450/23:ℝ)) :
    innerR 7 6 (3/40) x = (-(801/2:ℝ)) + (219/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (44:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((20:ℝ) + (-1:ℝ) * x) (245:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((20:ℝ) + (-1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) (210:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (114:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((20:ℝ) + (-1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) ((245:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((210:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((20:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((245:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(210:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((20:ℝ) + (-1:ℝ) * x))) ((114:ℝ) * ((1/2:ℝ)-((-1:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_144 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (840/43:ℝ) (450/23:ℝ) ∧
    ∫ x in (840/43:ℝ)..(450/23:ℝ), innerR 7 6 (3/40) x / x^3 = (7919/70560000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (840/43:ℝ) (450/23:ℝ) (-(801/2:ℝ)) (219/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_144 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_145 (x : ℝ) (hl : (450/23:ℝ) < x) (hr : x < (20:ℝ)) :
    innerR 7 6 (3/40) x = (-378:ℝ) + (83/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (45:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (19:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (36:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((20:ℝ) + (-1:ℝ) * x) (288:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((20:ℝ) + (-1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) (252:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) (156:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((20:ℝ) + (-1:ℝ) * x) ((-1:ℝ) + (3/40:ℝ) * x) ((288:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((252:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((20:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-1:ℝ) + (3/40:ℝ) * x) (1/2:ℝ) ((288:ℝ) * (((20:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(252:ℝ) * (((-1:ℝ) + (3/40:ℝ) * x)-((20:ℝ) + (-1:ℝ) * x))) ((156:ℝ) * ((1/2:ℝ)-((-1:ℝ) + (3/40:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_145 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (450/23:ℝ) (20:ℝ) ∧
    ∫ x in (450/23:ℝ)..(20:ℝ), innerR 7 6 (3/40) x / x^3 = (41/22500:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (450/23:ℝ) (20:ℝ) (-378:ℝ) (83/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_145 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_146 (x : ℝ) (hl : (20:ℝ) < x) (hr : x < (470/23:ℝ)) :
    innerR 7 6 (3/40) x = (-436:ℝ) + (109/5:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (46:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (40:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-20:ℝ) + (1:ℝ) * x) (259:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-20:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (296:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (374:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-20:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((259:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((296:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-20:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((259:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-(0:ℝ))+(296:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-20:ℝ) + (1:ℝ) * x))) ((374:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_146 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (20:ℝ) (470/23:ℝ) ∧
    ∫ x in (20:ℝ)..(470/23:ℝ), innerR 7 6 (3/40) x / x^3 = (109/441800:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (20:ℝ) (470/23:ℝ) (-436:ℝ) (109/5:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_146 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_147 (x : ℝ) (hl : (470/23:ℝ) < x) (hr : x < (880/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(825/2:ℝ)) + (413/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (47:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (40:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-20:ℝ) + (1:ℝ) * x) (304:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-20:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (342:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (420:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-20:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((304:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((342:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-20:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((304:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-(0:ℝ))+(342:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-20:ℝ) + (1:ℝ) * x))) ((420:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_147 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (470/23:ℝ) (880/43:ℝ) ∧
    ∫ x in (470/23:ℝ)..(880/43:ℝ), innerR 7 6 (3/40) x / x^3 = (21603/622054400:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (470/23:ℝ) (880/43:ℝ) (-(825/2:ℝ)) (413/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_147 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_148 (x : ℝ) (hl : (880/43:ℝ) < x) (hr : x < (41/2:ℝ)) :
    innerR 7 6 (3/40) x = (-(693/2:ℝ)) + (697/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (47:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (40:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (304:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((-20:ℝ) + (1:ℝ) * x) (385:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-20:ℝ) + (1:ℝ) * x) (1/2:ℝ) (420:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (19:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((-20:ℝ) + (1:ℝ) * x) ((304:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((385:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-20:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((304:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(385:ℝ) * (((-20:ℝ) + (1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((420:ℝ) * ((1/2:ℝ)-((-20:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_148 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (880/43:ℝ) (41/2:ℝ) ∧
    ∫ x in (880/43:ℝ)..(41/2:ℝ), innerR 7 6 (3/40) x / x^3 = (20001/473369600:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (880/43:ℝ) (41/2:ℝ) (-(693/2:ℝ)) (697/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_148 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_149 (x : ℝ) (hl : (41/2:ℝ) < x) (hr : x < (760/37:ℝ)) :
    innerR 7 6 (3/40) x = (-367:ℝ) + (737/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (47:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (41:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (37:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (304:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((21:ℝ) + (-1:ℝ) * x) (385:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((21:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (350:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((21:ℝ) + (-1:ℝ) * x) ((304:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((385:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((304:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(385:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((350:ℝ) * ((1/2:ℝ)-((21:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_149 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (41/2:ℝ) (760/37:ℝ) ∧
    ∫ x in (41/2:ℝ)..(760/37:ℝ), innerR 7 6 (3/40) x / x^3 = (101001/1941891200:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (41/2:ℝ) (760/37:ℝ) (-367:ℝ) (737/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_149 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_150 (x : ℝ) (hl : (760/37:ℝ) < x) (hr : x < (480/23:ℝ)) :
    innerR 7 6 (3/40) x = (-462:ℝ) + (461/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (47:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (41:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) (304:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (266:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (350:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((304:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((266:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((304:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(266:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) ((350:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_150 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (760/37:ℝ) (480/23:ℝ) ∧
    ∫ x in (760/37:ℝ)..(480/23:ℝ), innerR 7 6 (3/40) x / x^3 = (1043/1848320:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (760/37:ℝ) (480/23:ℝ) (-462:ℝ) (461/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_150 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_151 (x : ℝ) (hl : (480/23:ℝ) < x) (hr : x < (900/43:ℝ)) :
    innerR 7 6 (3/40) x = (-438:ℝ) + (219/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (48:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (41:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) (351:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (312:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (396:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((351:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((351:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) ((396:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_151 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (480/23:ℝ) (900/43:ℝ) ∧
    ∫ x in (480/23:ℝ)..(900/43:ℝ), innerR 7 6 (3/40) x / x^3 = (2263/17280000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (480/23:ℝ) (900/43:ℝ) (-438:ℝ) (219/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_151 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_152 (x : ℝ) (hl : (900/43:ℝ) < x) (hr : x < (21:ℝ)) :
    innerR 7 6 (3/40) x = (-438:ℝ) + (219/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (48:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (20:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (41:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) (351:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (312:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (396:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((21:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((351:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((351:ℝ) * (((21:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((21:ℝ) + (-1:ℝ) * x))) ((396:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_152 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (900/43:ℝ) (21:ℝ) ∧
    ∫ x in (900/43:ℝ)..(21:ℝ), innerR 7 6 (3/40) x / x^3 = (2117/13230000:ℝ) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (900/43:ℝ) (21:ℝ) (-438:ℝ) (219/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_152 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_153 (x : ℝ) (hl : (21:ℝ) < x) (hr : x < (780/37:ℝ)) :
    innerR 7 6 (3/40) x = (-459:ℝ) + (421/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (48:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (42:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (38:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) (273:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (312:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (396:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((273:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((273:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))+(312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) ((396:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_153 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (21:ℝ) (780/37:ℝ) ∧
    ∫ x in (21:ℝ)..(780/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(557/3974880:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (21:ℝ) (780/37:ℝ) (-459:ℝ) (421/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_153 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_154 (x : ℝ) (hl : (780/37:ℝ) < x) (hr : x < (490/23:ℝ)) :
    innerR 7 6 (3/40) x = (-498:ℝ) + (229/10:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (48:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (42:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) (273:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (312:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (396:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((273:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((273:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))+(312:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) ((396:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_154 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (780/37:ℝ) (490/23:ℝ) ∧
    ∫ x in (780/37:ℝ)..(490/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(9671/32461520:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (780/37:ℝ) (490/23:ℝ) (-498:ℝ) (229/10:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_154 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_155 (x : ℝ) (hl : (490/23:ℝ) < x) (hr : x < (920/43:ℝ)) :
    innerR 7 6 (3/40) x = (-(947/2:ℝ)) + (87/4:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (42:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) (320:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (360:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (444:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((320:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))) ((360:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((320:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-(0:ℝ))+(360:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((-21:ℝ) + (1:ℝ) * x))) ((444:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_155 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (490/23:ℝ) (920/43:ℝ) ∧
    ∫ x in (490/23:ℝ)..(920/43:ℝ), innerR 7 6 (3/40) x / x^3 = (-(694989/8128825600:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (490/23:ℝ) (920/43:ℝ) (-(947/2:ℝ)) (87/4:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_155 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_156 (x : ℝ) (hl : (920/43:ℝ) < x) (hr : x < (43/2:ℝ)) :
    innerR 7 6 (3/40) x = (-(809/2:ℝ)) + (741/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (42:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (320:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((-21:ℝ) + (1:ℝ) * x) (407:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((-21:ℝ) + (1:ℝ) * x) (1/2:ℝ) (444:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (20:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((-21:ℝ) + (1:ℝ) * x) ((320:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((407:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((-21:ℝ) + (1:ℝ) * x) (1/2:ℝ) ((320:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(407:ℝ) * (((-21:ℝ) + (1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((444:ℝ) * ((1/2:ℝ)-((-21:ℝ) + (1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_right]; rotate_left; linarith)
  ring
lemma i_156 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (920/43:ℝ) (43/2:ℝ) ∧
    ∫ x in (920/43:ℝ)..(43/2:ℝ), innerR 7 6 (3/40) x / x^3 = (-(95409/1251994880:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (920/43:ℝ) (43/2:ℝ) (-(809/2:ℝ)) (741/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_156 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_157 (x : ℝ) (hl : (43/2:ℝ) < x) (hr : x < (800/37:ℝ)) :
    innerR 7 6 (3/40) x = (-426:ℝ) + (781/40:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (43:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (39:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (320:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((22:ℝ) + (-1:ℝ) * x) (407:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((22:ℝ) + (-1:ℝ) * x) (1/2:ℝ) (370:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (22:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) ((22:ℝ) + (-1:ℝ) * x) ((320:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))) ((407:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((22:ℝ) + (-1:ℝ) * x) (1/2:ℝ) ((320:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-(0:ℝ))+(407:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-((2:ℝ) + (-(3/40:ℝ)) * x))) ((370:ℝ) * ((1/2:ℝ)-((22:ℝ) + (-1:ℝ) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_157 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (43/2:ℝ) (800/37:ℝ) ∧
    ∫ x in (43/2:ℝ)..(800/37:ℝ), innerR 7 6 (3/40) x / x^3 = (-(72207/1183360000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (43/2:ℝ) (800/37:ℝ) (-426:ℝ) (781/40:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_157 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_158 (x : ℝ) (hl : (800/37:ℝ) < x) (hr : x < (65/3:ℝ)) :
    innerR 7 6 (3/40) x = (-526:ℝ) + (483/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (43:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (40:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((22:ℝ) + (-1:ℝ) * x) (320:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((22:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (280:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (22:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (370:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (22:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((22:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((320:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((280:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((22:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((320:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(280:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((22:ℝ) + (-1:ℝ) * x))) ((370:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_158 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (800/37:ℝ) (65/3:ℝ) ∧
    ∫ x in (800/37:ℝ)..(65/3:ℝ), innerR 7 6 (3/40) x / x^3 = (-(1583/108160000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (800/37:ℝ) (65/3:ℝ) (-526:ℝ) (483/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_158 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_159 (x : ℝ) (hl : (65/3:ℝ) < x) (hr : x < (500/23:ℝ)) :
    innerR 7 6 (3/40) x = (-526:ℝ) + (483/20:ℝ) * x := by
  have hT : (⌊2 * Hc 6 (3/40) * x⌋ : ℤ) = (49:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hx : (⌊x⌋ : ℤ) = (21:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have ha : (⌊(3/40:ℝ) * x⌋ : ℤ) = (1:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hq : (⌊2 * x⌋ : ℤ) = (43:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hL : (⌊2 * ((1-(3/40:ℝ))*x)⌋ : ℤ) = (40:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num [Hc] <;> linarith
  have hI0 := const_piece_open (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((22:ℝ) + (-1:ℝ) * x) (320:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI1 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((22:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) (280:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (22:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hI2 := const_piece_open (gammaIntegrand 7 6 (3/40) x) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) (370:ℝ) (by linarith) (by
    intro z hz
    obtain ⟨hzl,hzr⟩ := hz
    have hz0 : (⌊x-z⌋ : ℤ) = (21:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz1 : (⌊x+z⌋ : ℤ) = (22:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz2 : (⌊(3/40:ℝ)*x-z⌋ : ℤ) = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    have hz3 : (⌊(3/40:ℝ)*x+z⌋ : ℤ) = (2:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num [Hc] <;> linarith
    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((22:ℝ) + (-1:ℝ) * x) ((2:ℝ) + (-(3/40:ℝ)) * x) ((320:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-(0:ℝ))) ((280:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((22:ℝ) + (-1:ℝ) * x))) hI0 hI1
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x) (0:ℝ) ((2:ℝ) + (-(3/40:ℝ)) * x) (1/2:ℝ) ((320:ℝ) * (((22:ℝ) + (-1:ℝ) * x)-(0:ℝ))+(280:ℝ) * (((2:ℝ) + (-(3/40:ℝ)) * x)-((22:ℝ) + (-1:ℝ) * x))) ((370:ℝ) * ((1/2:ℝ)-((2:ℝ) + (-(3/40:ℝ)) * x))) hc1 hI2
  have hG := hc2.2
  unfold innerR innerGamma
  rw [hG]
  unfold innerN Jfun sigmaC Tc nplus
  simp only [hT,hx,ha,hq,hL]
  norm_num [Hc]
  try (rw [max_eq_left]; rotate_left; linarith)
  ring
lemma i_159 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (65/3:ℝ) (500/23:ℝ) ∧
    ∫ x in (65/3:ℝ)..(500/23:ℝ), innerR 7 6 (3/40) x / x^3 = (-(281/21125000:ℝ)) := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) (65/3:ℝ) (500/23:ℝ) (-526:ℝ) (483/20:ℝ) (by norm_num) (by norm_num)
    (fun x hx => r_159 x hx.1 hx.2)
  norm_num at h ⊢
  exact h
lemma chunk_7 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/43:ℝ) (500/23:ℝ) ∧
    ∫ x in (820/43:ℝ)..(500/23:ℝ), innerR 7 6 (3/40) x / x^3 = (979579827467648203/249665666466216000000:ℝ) := by
  have h := i_140
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (440/23:ℝ) (720/37:ℝ) (26091/162720800:ℝ) (21287/20908800:ℝ) h i_141
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (720/37:ℝ) (39/2:ℝ) (3765373/3195244800:ℝ) (1039/7300800:ℝ) h i_142
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (39/2:ℝ) (840/43:ℝ) (237732211/179998790400:ℝ) (6683/52998400:ℝ) h i_143
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (840/43:ℝ) (450/23:ℝ) (245404933/169614244800:ℝ) (7919/70560000:ℝ) h i_144
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (450/23:ℝ) (20:ℝ) (3777726611/2423060640000:ℝ) (41/22500:ℝ) h i_145
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (20:ℝ) (470/23:ℝ) (182068479/53845792000:ℝ) (109/441800:ℝ) h i_146
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (470/23:ℝ) (880/43:ℝ) (431535226751/118945354528000:ℝ) (21603/622054400:ℝ) h i_147
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (880/43:ℝ) (41/2:ℝ) (37077958927/10123008896000:ℝ) (20001/473369600:ℝ) h i_148
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (41/2:ℝ) (760/37:ℝ) (4688210039/1265376112000:ℝ) (101001/1941891200:ℝ) h i_149
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (760/37:ℝ) (480/23:ℝ) (858101397157/228400388216000:ℝ) (1043/1848320:ℝ) h i_150
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (480/23:ℝ) (900/43:ℝ) (831146841423/192337169024000:ℝ) (2263/17280000:ℝ) h i_151
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (900/43:ℝ) (21:ℝ) (28901321158771/6491379454560000:ℝ) (2117/13230000:ℝ) h i_152
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (21:ℝ) (780/37:ℝ) (1552446518659/336590045792000:ℝ) (-(557/3974880:ℝ)) h i_153
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (780/37:ℝ) (490/23:ℝ) (8386560835643/1875287397984000:ℝ) (-(9671/32461520:ℝ)) h i_154
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (490/23:ℝ) (920/43:ℝ) (206535379309073/49478736731424000:ℝ) (-(694989/8128825600:ℝ)) h i_155
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (920/43:ℝ) (43/2:ℝ) (273008672259331/66771050333988000:ℝ) (-(95409/1251994880:ℝ)) h i_156
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (43/2:ℝ) (800/37:ℝ) (172307728241845249/42942494632189152000:ℝ) (-(72207/1183360000:ℝ)) h i_157
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (800/37:ℝ) (65/3:ℝ) (78924388961963849/19973253317297280000:ℝ) (-(1583/108160000:ℝ)) h i_158
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (820/43:ℝ) (65/3:ℝ) (500/23:ℝ) (102221685698614523/25965229312486464000:ℝ) (-(281/21125000:ℝ)) h i_159
  norm_num at h
  norm_num at h ⊢
  exact h
end MarginPieces
