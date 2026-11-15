import MarginPieces

/- E213/U18, Codex. CONJECTURE: supporting periodic reduction; parent gate pending. -/
noncomputable section
open MeasureTheory Set Mathathon.P108
namespace U18

theorem ell_add_integer (x z : ℝ) (n : ℤ) :
    ell (x + n) z = ell x z + 2 * n := by
  unfold ell
  rw [show x + n - z = (x-z) + n by ring,
    show x + n + z = (x+z) + n by ring, Int.floor_add_intCast, Int.floor_add_intCast]
  push_cast
  ring

theorem innerR_period40 (x : ℝ) :
    innerR 7 6 (3/40) (x+40) - innerR 7 6 (3/40) x =
      222 + 74 * ((x-(⌊x⌋:ℝ)) - 6*((3/40:ℝ)*x-(⌊(3/40:ℝ)*x⌋:ℝ))) := by
  have hT : Tc 6 (3/40) (x+40) = Tc 6 (3/40) x + 92 := by
    unfold Tc
    rw [show 2*Hc 6 (3/40)*(x+40) = 2*Hc 6 (3/40)*x+(92:ℤ) by norm_num [Hc]; ring,
      Int.floor_add_intCast]
    push_cast
    ring
  have hq : (⌊2*(x+40)⌋:ℝ) = (⌊2*x⌋:ℝ)+80 := by
    rw [show 2*(x+40) = 2*x+(80:ℤ) by push_cast; ring, Int.floor_add_intCast]
    push_cast
    ring
  have hx : (⌊x+40⌋:ℝ) = (⌊x⌋:ℝ)+40 := by
    rw [show x+40 = x+(40:ℤ) by norm_num, Int.floor_add_intCast]
    push_cast
    ring
  have ha : (⌊(3/40:ℝ)*(x+40)⌋:ℝ) = (⌊(3/40:ℝ)*x⌋:ℝ)+3 := by
    rw [show (3/40:ℝ)*(x+40) = (3/40:ℝ)*x+(3:ℤ) by push_cast; ring,
      Int.floor_add_intCast]
    push_cast
    ring
  have hL : (⌊2*((1-(3/40:ℝ))*(x+40))⌋:ℝ) =
      (⌊2*((1-(3/40:ℝ))*x)⌋:ℝ)+74 := by
    rw [show 2*((1-(3/40:ℝ))*(x+40)) = 2*((1-(3/40:ℝ))*x)+(74:ℤ) by push_cast; ring,
      Int.floor_add_intCast]
    push_cast
    ring
  have hsigma : sigmaC 6 (3/40) (x+40) = sigmaC 6 (3/40) x := by
    unfold sigmaC
    rw [hT]
    norm_num [Hc]
    ring
  have hnplus : nplus (x+40) = nplus x := by
    unfold nplus
    rw [hq]
    ring
  have hgd (z : ℝ) : gammaIntegrand 7 6 (3/40) (x+40) z - gammaIntegrand 7 6 (3/40) x z =
      (104*Tc 6 (3/40) x+1702) + 132*ell ((3/40:ℝ)*x) z - 74*ell x z := by
    have he := ell_add_integer x z 40
    have he' := ell_add_integer ((3/40:ℝ)*x) z 3
    norm_num at he he'
    unfold gammaIntegrand
    rw [show (3/40:ℝ)*(x+40) = (3/40:ℝ)*x+3 by ring]
    rw [hT, he, he']
    ring
  have hI : (∫ z in (0:ℝ)..(1/2), gammaIntegrand 7 6 (3/40) (x+40) z) -
      (∫ z in (0:ℝ)..(1/2), gammaIntegrand 7 6 (3/40) x z) =
      52*Tc 6 (3/40) x + 132*((3/40:ℝ)*x) - 74*x + 851 := by
    rw [← intervalIntegral.integral_sub (gammaIntegrand_integrable _ _ _ _) (gammaIntegrand_integrable _ _ _ _)]
    simp_rw [hgd]
    rw [intervalIntegral.integral_sub
        (intervalIntegrable_const.add ((ell_intervalIntegrable ((3/40:ℝ)*x) 0 (1/2)).const_mul 132))
        ((ell_intervalIntegrable x 0 (1/2)).const_mul 74),
      intervalIntegral.integral_add intervalIntegrable_const
        ((ell_intervalIntegrable ((3/40:ℝ)*x) 0 (1/2)).const_mul 132),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_ell, integral_ell]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hG : innerGamma 7 6 (3/40) (x+40) - innerGamma 7 6 (3/40) x = (111/2:ℝ)*x+851 := by
    calc
      _ = ((∫ z in (0:ℝ)..(1/2), gammaIntegrand 7 6 (3/40) (x+40) z) -
          (∫ z in (0:ℝ)..(1/2), gammaIntegrand 7 6 (3/40) x z)) +
          104*sigmaC 6 (3/40) x := by
        unfold innerGamma
        rw [hsigma, hT, hq, hnplus]
        ring
      _ = _ := by rw [hI]; unfold sigmaC; norm_num [Hc]; ring
  have hN : innerN 6 (3/40) (x+40) - innerN 6 (3/40) x =
      74*(⌊x⌋:ℝ) - 444*(⌊(3/40:ℝ)*x⌋:ℝ) - (481/5:ℝ)*x -1073 := by
    unfold innerN Jfun
    rw [hx, ha, hL]
    ring
  unfold innerR
  linear_combination -hG -hN

end U18
#print axioms U18.innerR_period40
