import PackageTail.Primitive
import Mathlib.Analysis.Calculus.Deriv.ZPow
/-!
E608 numerical closing tail. Codex lane C, 2026-11-14.
PROOF-DRAFT: all declarations until final gate. Extracted second primitive
from lane U E253 ShortArithmeticFloor.lean:52-134; Q bound from E248
CompactClosingLite.lean:99-132. No old numerical chunks imported.
Fauzan re-derivation using Firsching mo271/Zeta5 (Apache-2.0),
Paul-Lez Comparator metadata. Only numerical tail certificate changes.
-/
noncomputable section
open MeasureTheory Set Real Filter Topology Mathathon.P108
namespace SplitTail
theorem Q_upper (x : ℝ) : U22.Q x ≤ 7 := by
  have hs := U22.sigma_range x
  have hn := U22.nplus_range x
  have hsn : 0 ≤ sigmaC 6 U22.alpha x * nplus x := mul_nonneg hs.1 hn.1
  have hsq : (∫ z in (0:ℝ)..(1/2), U22.delta (U22.alpha*x) z * U22.delta (U22.alpha*x) z) ≤ 1/2 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
      (U22.delta_mul_integrable (U22.alpha*x) (U22.alpha*x))
      (intervalIntegrable_const (c := (1:ℝ))) ?_
    · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using h
    · intro z _
      have ha := U22.delta_abs (U22.alpha*x) z
      rw [abs_le] at ha
      nlinarith [sq_nonneg (U22.delta (U22.alpha*x) z)]
  have hcross : (-1/2:ℝ) ≤ ∫ z in (0:ℝ)..(1/2), U22.delta (U22.alpha*x) z * U22.delta x z := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
      (intervalIntegrable_const (c := (-1:ℝ)))
      (U22.delta_mul_integrable (U22.alpha*x) x) ?_
    · norm_num only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
      linarith only [h]
    · intro z _
      have ha := U22.delta_abs (U22.alpha*x) z
      have hb := U22.delta_abs x z
      have hab : |U22.delta (U22.alpha*x) z * U22.delta x z| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg (U22.delta (U22.alpha*x) z), abs_nonneg (U22.delta x z)]
      exact (abs_le.mp hab).1
  have hf := U22.frac_range (2*U22.lam*x)
  have hp : U22.frac (2*U22.lam*x) - (U22.frac (2*U22.lam*x))^2 ≤ 1/4 := by
    nlinarith [sq_nonneg (U22.frac (2*U22.lam*x)-1/2)]
  have hs2 : (sigmaC 6 U22.alpha x)^2 ≤ 1/4 := by
    nlinarith [sq_nonneg (sigmaC 6 U22.alpha x)]
  rw [U22.Q_centered]
  linarith [le_max_right (sigmaC 6 U22.alpha x - nplus x) (0:ℝ)]



def C (t : ℝ) : ℝ := t^3/6-t^2/4+t/12
/-- PROOF-DRAFT: periodic extension through the fractional part. -/
def D (x : ℝ) : ℝ := C (U22.frac x)
/-- PROOF-DRAFT: second primitive for the actual periodic term. -/
def H (x : ℝ) : ℝ := 2*U22.lam*D x-(12*U22.lam/U22.alpha^2)*D (U22.alpha*x)
/-- PROOF-DRAFT: the exact mean removed by the second primitive. -/
def mu : ℝ := U22.lam/U22.alpha-U22.lam/6

lemma C_deriv (t : ℝ) : HasDerivAt C (U22.P t+1/12) t := by
  have h := ((((hasDerivAt_id t).pow 3).div_const 6).sub
    (((hasDerivAt_id t).pow 2).div_const 4)).add ((hasDerivAt_id t).div_const 12)
  exact h.congr_deriv (by dsimp [U22.P]; ring)

lemma C_left_range (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1/2) : 0 ≤ C t ∧ C t ≤ 1/96 := by
  have h1 : 0 ≤ t*(1-2*t) := mul_nonneg ht.1 (by linarith)
  have h2 : t*(1-t)*(1-2*t) ≤ t*(1-2*t) := by
    nlinarith [mul_nonneg ht.1 h1]
  have he : C t = t*(1-t)*(1-2*t)/12 := by unfold C; ring
  rw [he]
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg ht.1 (by linarith)) (by linarith)) (by norm_num)
  · nlinarith [sq_nonneg (t-1/4)]

lemma C_range (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : (-1:ℝ)/96 ≤ C t ∧ C t ≤ 1/96 := by
  by_cases h : t ≤ 1/2
  · have hc := C_left_range t ⟨ht.1,h⟩
    constructor <;> linarith
  · have hc := C_left_range (1-t) (by constructor <;> linarith)
    have he : C (1-t) = -C t := by unfold C; ring
    rw [he] at hc
    constructor <;> linarith

lemma D_continuous : Continuous D := by
  have h : ContinuousOn C (Icc (0:ℝ) 1) := by unfold C; fun_prop
  have hc := h.comp_fract'' (show C 0 = C 1 by norm_num [C])
  change Continuous (fun x=>C (U22.frac x))
  simpa only [U22.frac,Int.fract,Function.comp_def] using hc

lemma D_range (x : ℝ) : (-1:ℝ)/96 ≤ D x ∧ D x ≤ 1/96 :=
  C_range _ (U22.frac_range x)

lemma D_right (x : ℝ) : HasDerivWithinAt D (U22.B x+1/12) (Ici x) x := by
  have hd := (C_deriv (x-(⌊x⌋:ℝ))).comp x ((hasDerivAt_id x).sub_const (⌊x⌋:ℝ))
  have hf : ∀ᶠ y in 𝓝[≥] x,(⌊y⌋:ℤ)=⌊x⌋ :=
    tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have h : HasDerivWithinAt (fun y=>C (y-(⌊x⌋:ℝ))) (U22.B x+1/12) (Ici x) x := by
    convert! hd.hasDerivWithinAt (s:=Ici x) using 1 <;> simp only [Function.comp_def,id_eq,mul_one,U22.B,U22.frac]
  apply h.congr_of_eventuallyEq
  · filter_upwards [hf] with y hy
    unfold D U22.frac
    rw [hy]
  · rfl

lemma H_continuous : Continuous H :=
  (D_continuous.const_mul _).sub
    ((D_continuous.comp (continuous_const.mul continuous_id)).const_mul _)

lemma H_range (x : ℝ) : -21 ≤ H x ∧ H x ≤ 21 := by
  have h1 := D_range x
  have h2 := D_range (U22.alpha*x)
  unfold H
  norm_num [U22.lam,U22.alpha] at *
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

lemma mu_value : mu = (2923:ℝ)/240 := by norm_num [mu,U22.lam,U22.alpha]

lemma H_right (x : ℝ) : HasDerivWithinAt H (U22.G x-mu) (Ioi x) x := by
  have hc : HasDerivWithinAt (fun y : ℝ=>U22.alpha*y) U22.alpha (Ici x) x :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul U22.alpha).hasDerivWithinAt (s:=Ici x)
  have hcomp := (D_right (U22.alpha*x)).comp x hc
    (show MapsTo (fun y : ℝ=>U22.alpha*y) (Ici x) (Ici (U22.alpha*x)) by
      intro y hy
      change U22.alpha*x≤U22.alpha*y
      exact mul_le_mul_of_nonneg_left (show x≤y from hy) (by norm_num [U22.alpha]))
  have h := ((D_right x).const_mul (2*U22.lam)).sub (hcomp.const_mul (12*U22.lam/U22.alpha^2))
  change HasDerivWithinAt H _ (Ici x) x at h
  have hd : 2*U22.lam*(U22.B x+1/12)-(12*U22.lam/U22.alpha^2)*((U22.B (U22.alpha*x)+1/12)*U22.alpha)=U22.G x-mu := by
    unfold U22.G mu
    norm_num [U22.lam,U22.alpha]
    ring
  exact (h.congr_deriv hd).mono (fun y (hy : x<y)=>show x≤y from le_of_lt hy)


/-- PROOF-DRAFT: exact endpoint primitives used by the new cutoff. -/
lemma G21 : U22.G 21 = (14467:ℝ)/800 := by
  norm_num [U22.G,U22.B,U22.P,U22.frac,U22.lam,U22.alpha]
lemma H21 : H 21 = (14467:ℝ)/2400 := by
  norm_num [H,D,C,U22.frac,U22.lam,U22.alpha]
lemma GM : U22.G 1000000 = 0 := by
  norm_num [U22.G,U22.B,U22.P,U22.frac,U22.lam,U22.alpha]
lemma HM : H 1000000 = 0 := by
  norm_num [H,D,C,U22.frac,U22.lam,U22.alpha]

lemma power_cont (n : ℤ) :
    ContinuousOn (fun x : ℝ => x^n) (uIcc (21:ℝ) 1000000) := by
  apply ContinuousOn.zpow₀ continuousOn_id
  intro x hx
  rw [uIcc_of_le (by norm_num : (21:ℝ) ≤ 1000000)] at hx
  left
  change x ≠ 0
  linarith [hx.1]

lemma power_integral2 :
    (∫ x in (21:ℝ)..1000000,x^(-2:ℤ)) = 1/21-(1000000:ℝ)^(-1:ℤ) := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
  · rw [uIcc_of_le (by norm_num : (21:ℝ) ≤ 1000000)]
    intro h
    linarith [h.1]
lemma power_integral3 :
    (∫ x in (21:ℝ)..1000000,x^(-3:ℤ)) = (1/21^2-(1000000:ℝ)^(-2:ℤ))/2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
  · rw [uIcc_of_le (by norm_num : (21:ℝ) ≤ 1000000)]
    intro h
    linarith [h.1]
lemma power_integral4 :
    (∫ x in (21:ℝ)..1000000,x^(-4:ℤ)) = (1/21^3-(1000000:ℝ)^(-3:ℤ))/3 := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
  · rw [uIcc_of_le (by norm_num : (21:ℝ) ≤ 1000000)]
    intro h
    linarith [h.1]

/-- PROOF-DRAFT: upper integration-by-parts bound for the second primitive. -/
theorem centered_G_upper :
    (∫ x in (21:ℝ)..1000000,(U22.G x-mu)*x^(-3:ℤ)) ≤
      -(14467/2400:ℝ)/21^3 + 21*(1/21^3-1/(1000000:ℝ)^3) := by
  have hv := power_cont (-3)
  have hw := power_cont (-4)
  have hg0 : IntervalIntegrable U22.G volume 21 1000000 :=
    U22.G_continuous.intervalIntegrable (21:ℝ) 1000000
  have hD := (hg0.sub (intervalIntegrable_const (c:=mu))).mul_continuousOn hv
  have hH : IntervalIntegrable (fun x => H x*x^(-4:ℤ)) volume 21 1000000 :=
    (H_continuous.intervalIntegrable 21 1000000).mul_continuousOn hw
  have hvd : ∀ x∈Ioo (min (21:ℝ) 1000000) (max (21:ℝ) 1000000),
      HasDerivWithinAt (fun y : ℝ => y^(-3:ℤ)) ((-3:ℝ)*x^(-4:ℤ)) (Ioi x) x := by
    intro x hx
    norm_num only [min_eq_left (by norm_num : (21:ℝ) ≤ 1000000),
      max_eq_right (by norm_num : (21:ℝ) ≤ 1000000)] at hx
    have hx0 : x≠0 := by linarith [hx.1]
    simpa using (hasDerivAt_zpow (-3:ℤ) x (Or.inl hx0)).hasDerivWithinAt (s:=Ioi x)
  have hbp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u:=H) (u':=fun x => U22.G x-mu) (v:=fun x : ℝ => x^(-3:ℤ))
    (v':=fun x : ℝ => (-3:ℝ)*x^(-4:ℤ))
    H_continuous.continuousOn hv (fun x _ => H_right x) hvd
    (hg0.sub (intervalIntegrable_const (c:=mu))) (hw.intervalIntegrable.const_mul (-3))
  have he (x : ℝ) : (U22.G x-mu)*x^(-3:ℤ)+H x*((-3:ℝ)*x^(-4:ℤ)) =
      (U22.G x-mu)*x^(-3:ℤ)-3*(H x*x^(-4:ℤ)) := by ring
  simp_rw [he] at hbp
  rw [intervalIntegral.integral_sub hD (hH.const_mul 3),
    intervalIntegral.integral_const_mul,HM,H21] at hbp
  have hb : (∫ x in (21:ℝ)..1000000,H x*x^(-4:ℤ)) ≤
      21*(∫ x in (21:ℝ)..1000000,x^(-4:ℤ)) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) hH (hw.intervalIntegrable.const_mul 21)
    intro x hx
    exact mul_le_mul_of_nonneg_right (H_range x).2 (zpow_nonneg (by linarith [hx.1]) _)
  rw [power_integral4] at hb
  norm_num at hbp hb ⊢
  linarith

lemma weighted_G_upper :
    (∫ x in (21:ℝ)..1000000,U22.G x*x^(-3:ℤ)) ≤
      mu*(1/21^2-1/(1000000:ℝ)^2)/2 -(14467/2400:ℝ)/21^3 +
        21*(1/21^3-1/(1000000:ℝ)^3) := by
  have h := centered_G_upper
  have hg : IntervalIntegrable (fun x => U22.G x*x^(-3:ℤ)) volume 21 1000000 :=
    (U22.G_continuous.intervalIntegrable 21 1000000).mul_continuousOn (power_cont (-3))
  have he (x : ℝ) : (U22.G x-mu)*x^(-3:ℤ) = U22.G x*x^(-3:ℤ)-mu*x^(-3:ℤ) := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_sub hg ((power_cont (-3)).intervalIntegrable.const_mul mu),
    intervalIntegral.integral_const_mul,power_integral3] at h
  norm_num at h ⊢
  linarith

/-- PROOF-DRAFT: retain the exact first and second primitive endpoint corrections. -/
theorem weighted_F_upper :
    (∫ x in (21:ℝ)..1000000,U22.F x*x^(-2:ℤ)) ≤
      U22.lam*(1/21-1/1000000) -(14467/800:ℝ)/21^2 +
        mu*(1/21^2-1/(1000000:ℝ)^2) -2*(14467/2400:ℝ)/21^3 +
          42*(1/21^3-1/(1000000:ℝ)^3) := by
  have hv := power_cont (-2)
  have hw := power_cont (-3)
  have hD := ((U22.F_integrable 21 1000000).sub
    (intervalIntegrable_const (c:=U22.lam))).mul_continuousOn hv
  have hG : IntervalIntegrable (fun x => U22.G x*x^(-3:ℤ)) volume 21 1000000 :=
    (U22.G_continuous.intervalIntegrable 21 1000000).mul_continuousOn hw
  have hvd : ∀ x∈Ioo (min (21:ℝ) 1000000) (max (21:ℝ) 1000000),
      HasDerivWithinAt (fun y : ℝ => y^(-2:ℤ)) ((-2:ℝ)*x^(-3:ℤ)) (Ioi x) x := by
    intro x hx
    norm_num only [min_eq_left (by norm_num : (21:ℝ) ≤ 1000000),
      max_eq_right (by norm_num : (21:ℝ) ≤ 1000000)] at hx
    have hx0 : x≠0 := by linarith [hx.1]
    simpa using (hasDerivAt_zpow (-2:ℤ) x (Or.inl hx0)).hasDerivWithinAt (s:=Ioi x)
  have hbp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u:=U22.G) (u':=fun x => U22.F x-U22.lam) (v:=fun x : ℝ => x^(-2:ℤ))
    (v':=fun x : ℝ => (-2:ℝ)*x^(-3:ℤ))
    U22.G_continuous.continuousOn hv (fun x _ => U22.G_right x) hvd
    ((U22.F_integrable 21 1000000).sub (intervalIntegrable_const (c:=U22.lam)))
    (hw.intervalIntegrable.const_mul (-2))
  have he (x : ℝ) : (U22.F x-U22.lam)*x^(-2:ℤ)+U22.G x*((-2:ℝ)*x^(-3:ℤ)) =
      (U22.F x-U22.lam)*x^(-2:ℤ)-2*(U22.G x*x^(-3:ℤ)) := by ring
  simp_rw [he] at hbp
  rw [intervalIntegral.integral_sub hD (hG.const_mul 2),
    intervalIntegral.integral_const_mul,GM,G21] at hbp
  have hF := (U22.F_integrable 21 1000000).mul_continuousOn hv
  have he2 (x : ℝ) : (U22.F x-U22.lam)*x^(-2:ℤ) =
      U22.F x*x^(-2:ℤ)-U22.lam*x^(-2:ℤ) := by ring
  simp_rw [he2] at hbp
  rw [intervalIntegral.integral_sub hF (hv.intervalIntegrable.const_mul U22.lam),
    intervalIntegral.integral_const_mul,power_integral2] at hbp
  have hg := weighted_G_upper
  norm_num at hbp hg ⊢
  linarith

/-- PROOF-DRAFT: the concrete new numerical tail certificate. -/
theorem tail21_upper :
    (∫ x in (21:ℝ)..1000000,innerR 7 6 (3/40) x/x^3) ≤
      (37/40:ℝ)*(1/21-1/1000000) -(14467/800:ℝ)/21^2 +
        (2923/240+7/2:ℝ)*(1/21^2-1/(1000000:ℝ)^2) -2*(14467/2400:ℝ)/21^3 +
          42*(1/21^3-1/(1000000:ℝ)^3) := by
  have hF := (U22.F_integrable 21 1000000).mul_continuousOn (power_cont (-2))
  have h3 : IntervalIntegrable (fun x : ℝ => x^(-3:ℤ)) volume 21 1000000 :=
    (power_cont (-3)).intervalIntegrable
  have hR : IntervalIntegrable (fun x => innerR 7 6 U22.alpha x/x^3) volume 21 1000000 :=
    (innerR_div_intervalIntegrable 7 6 U22.alpha 21 (by norm_num)).symm.trans
      (innerR_div_intervalIntegrable 7 6 U22.alpha 1000000 (by norm_num))
  have hmono : (∫ x in (21:ℝ)..1000000,innerR 7 6 U22.alpha x/x^3) ≤
      ∫ x in (21:ℝ)..1000000,U22.F x*x^(-2:ℤ)+7*x^(-3:ℤ) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hR (hF.add (h3.const_mul 7))
    intro x hx
    have hx0 : x≠0 := by linarith [hx.1]
    have hq := Q_upper x
    unfold U22.Q at hq
    calc
      _ ≤ (x*U22.F x+7)/x^3 :=
        div_le_div_of_nonneg_right (by linarith) (pow_nonneg (by linarith [hx.1]) 3)
      _ = _ := by rw [zpow_neg,zpow_ofNat,zpow_neg,zpow_ofNat];field_simp
  rw [intervalIntegral.integral_add hF (h3.const_mul 7),
    intervalIntegral.integral_const_mul,power_integral3] at hmono
  have hf := weighted_F_upper
  norm_num [U22.alpha,U22.lam,mu_value] at hmono hf ⊢
  linarith

#print axioms tail21_upper
end SplitTail
