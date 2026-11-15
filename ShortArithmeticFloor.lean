import AnalyticHelpers

/-!
E253/U58, Codex (GPT-6), event work Sat Nov 14 2026.
Every mathematical declaration in this module is PROOF-DRAFT.
This is a research proof of the same frozen U18 actual arithmetic floor.
The overall research claim remains CONJECTURE; no report prose or submission project.
-/
noncomputable section
open MeasureTheory Set Real Filter Topology Mathathon.P108
namespace U58

/-- PROOF-DRAFT: the non-covariance centered term is bounded below sharply. -/
lemma elementary_remainder_lower (s n : ℝ) (hs : 0 ≤ s ∧ s ≤ 1/2)
    (hn : 0 ≤ n ∧ n ≤ 1/2) :
    (-1:ℝ)/8 ≤ 2*s^2-2*s*n-max (s-n) 0 := by
  by_cases h : s ≤ n
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (s-1/4), mul_nonneg hs.1 (sub_nonneg.mpr hn.2)]
  · rw [max_eq_left (by linarith)]
    have hp : 0 ≤ (1-2*s)*n := mul_nonneg (by linarith [hs.2]) hn.1
    nlinarith [sq_nonneg (s-1/4)]

/-- PROOF-DRAFT: centered covariance costs at most one eighth. -/
lemma covariance_lower (x : ℝ) :
    (-1:ℝ)/8 ≤ 9*(∫ z in (0:ℝ)..(1/2), U22.delta (U22.alpha*x) z*U22.delta (U22.alpha*x) z)
      -3*(∫ z in (0:ℝ)..(1/2), U22.delta (U22.alpha*x) z*U22.delta x z) := by
  have hA := (U22.delta_mul_integrable (U22.alpha*x) (U22.alpha*x)).const_mul 9
  have hB := (U22.delta_mul_integrable (U22.alpha*x) x).const_mul 3
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
    (intervalIntegrable_const (c := (-1/4:ℝ))) (hA.sub hB) ?_
  · rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hmono
    norm_num only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    linarith only [hmono]
  · intro z _
    have h := U22.delta_abs x z
    rw [abs_le] at h
    have hb : (U22.delta x z)^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (3*U22.delta (U22.alpha*x) z-U22.delta x z/2)]

/-- PROOF-DRAFT: the exact package remainder has a uniform quarter lower bound. -/
theorem Q_lower_quarter (x : ℝ) : (-1:ℝ)/4 ≤ U22.Q x := by
  have hn := elementary_remainder_lower _ _ (U22.sigma_range x) (U22.nplus_range x)
  have hc := covariance_lower x
  have hf := U22.frac_range (2*U22.lam*x)
  have hp : 0 ≤ U22.frac (2*U22.lam*x)-(U22.frac (2*U22.lam*x))^2 := by nlinarith
  rw [U22.Q_centered]
  linarith

/-- PROOF-DRAFT: a periodic primitive of the centered quadratic Bernoulli polynomial. -/
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

lemma H40 : H 40 = 0 := by norm_num [H,D,C,U22.frac,U22.lam,U22.alpha]
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

/-- PROOF-DRAFT: exact fourth inverse-power integral from the smaller prefix. -/
lemma power_integral4 {M : ℝ} (hM : 40 ≤ M) :
    (∫ x in (40:ℝ)..M,x^(-4:ℤ)) = (1/64000-M^(-3:ℤ))/3 := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
    ring
  · rw [uIcc_of_le hM]
    intro h
    linarith [h.1]

/-- PROOF-DRAFT: second centering removes the first primitive's mean exactly. -/
theorem centered_G_lower {M : ℝ} (hM : 40 ≤ M) :
    (-21:ℝ)/64000 ≤ ∫ x in (40:ℝ)..M,(U22.G x-mu)*x^(-3:ℤ) := by
  have hv := U53.power_cont (-3) hM
  have hw := U53.power_cont (-4) hM
  have hg0 : IntervalIntegrable U22.G volume 40 M := U22.G_continuous.intervalIntegrable 40 M
  have hD := (hg0.sub (intervalIntegrable_const (c:=mu))).mul_continuousOn hv
  have hH : IntervalIntegrable (fun x=>H x*x^(-4:ℤ)) volume 40 M :=
    (H_continuous.intervalIntegrable 40 M).mul_continuousOn hw
  have hvd : ∀ x∈Ioo (min (40:ℝ) M) (max (40:ℝ) M),
      HasDerivWithinAt (fun y : ℝ=>y^(-3:ℤ)) ((-3:ℝ)*x^(-4:ℤ)) (Ioi x) x := by
    intro x hx
    rw [min_eq_left hM,max_eq_right hM] at hx
    have hx0 : x≠0 := by linarith [hx.1]
    simpa using (hasDerivAt_zpow (-3:ℤ) x (Or.inl hx0)).hasDerivWithinAt (s:=Ioi x)
  have hbp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u:=H) (u':=fun x=>U22.G x-mu) (v:=fun x : ℝ=>x^(-3:ℤ))
    (v':=fun x : ℝ=>(-3:ℝ)*x^(-4:ℤ))
    H_continuous.continuousOn hv (fun x _=>H_right x) hvd
    (hg0.sub (intervalIntegrable_const (c:=mu)))
    (hw.intervalIntegrable.const_mul (-3))
  have he (x : ℝ) : (U22.G x-mu)*x^(-3:ℤ)+H x*((-3:ℝ)*x^(-4:ℤ))=
      (U22.G x-mu)*x^(-3:ℤ)-3*(H x*x^(-4:ℤ)) := by ring
  simp_rw [he] at hbp
  rw [intervalIntegral.integral_sub hD (hH.const_mul 3),
    intervalIntegral.integral_const_mul,H40,zero_mul,sub_zero] at hbp
  have hbound : (-21:ℝ)*(∫ x in (40:ℝ)..M,x^(-4:ℤ)) ≤
      ∫ x in (40:ℝ)..M,H x*x^(-4:ℤ) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hM (hw.intervalIntegrable.const_mul (-21)) hH
    intro x hx
    exact mul_le_mul_of_nonneg_right (H_range x).1 (zpow_nonneg (by linarith [hx.1]) _)
  have hpoint : (-21:ℝ)*M^(-3:ℤ) ≤ H M*M^(-3:ℤ) :=
    mul_le_mul_of_nonneg_right (H_range M).1 (zpow_nonneg (by linarith) _)
  rw [power_integral4 hM] at hbound
  linarith

/-- PROOF-DRAFT: weighted primitive lower bound with its exact mean retained. -/
lemma weighted_G_lower {M : ℝ} (hM : 40 ≤ M) :
    mu*(1/1600-M^(-2:ℤ))/2-21/64000 ≤ ∫ x in (40:ℝ)..M,U22.G x*x^(-3:ℤ) := by
  have h := centered_G_lower hM
  have hg : IntervalIntegrable (fun x=>U22.G x*x^(-3:ℤ)) volume 40 M :=
    (U22.G_continuous.intervalIntegrable 40 M).mul_continuousOn (U53.power_cont (-3) hM)
  have he (x : ℝ) : (U22.G x-mu)*x^(-3:ℤ)=U22.G x*x^(-3:ℤ)-mu*x^(-3:ℤ) := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_sub hg ((U53.power_cont (-3) hM).intervalIntegrable.const_mul mu),
    intervalIntegral.integral_const_mul,U53.power_integral3 hM] at h
  linarith

/-- PROOF-DRAFT: two integrations by parts for the actual periodic coefficient. -/
theorem weighted_F_lower {M : ℝ} (hM : 40 ≤ M) :
    U22.lam*(1/40-1/M)+U22.G M*M^(-2:ℤ)+mu*(1/1600-M^(-2:ℤ))-42/64000 ≤
      ∫ x in (40:ℝ)..M,U22.F x*x^(-2:ℤ) := by
  have hv := U53.power_cont (-2) hM
  have hw := U53.power_cont (-3) hM
  have hD := ((U22.F_integrable 40 M).sub (intervalIntegrable_const (c:=U22.lam))).mul_continuousOn hv
  have hG : IntervalIntegrable (fun x=>U22.G x*x^(-3:ℤ)) volume 40 M :=
    (U22.G_continuous.intervalIntegrable 40 M).mul_continuousOn hw
  have hvd : ∀ x∈Ioo (min (40:ℝ) M) (max (40:ℝ) M),
      HasDerivWithinAt (fun y : ℝ=>y^(-2:ℤ)) ((-2:ℝ)*x^(-3:ℤ)) (Ioi x) x := by
    intro x hx
    rw [min_eq_left hM,max_eq_right hM] at hx
    have hx0 : x≠0 := by linarith [hx.1]
    simpa using (hasDerivAt_zpow (-2:ℤ) x (Or.inl hx0)).hasDerivWithinAt (s:=Ioi x)
  have hbp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u:=U22.G) (u':=fun x=>U22.F x-U22.lam) (v:=fun x : ℝ=>x^(-2:ℤ))
    (v':=fun x : ℝ=>(-2:ℝ)*x^(-3:ℤ))
    U22.G_continuous.continuousOn hv (fun x _=>U22.G_right x) hvd
    ((U22.F_integrable 40 M).sub (intervalIntegrable_const (c:=U22.lam))) (hw.intervalIntegrable.const_mul (-2))
  have he (x : ℝ) : (U22.F x-U22.lam)*x^(-2:ℤ)+U22.G x*((-2:ℝ)*x^(-3:ℤ))=
      (U22.F x-U22.lam)*x^(-2:ℤ)-2*(U22.G x*x^(-3:ℤ)) := by ring
  simp_rw [he] at hbp
  rw [intervalIntegral.integral_sub hD (hG.const_mul 2),
    intervalIntegral.integral_const_mul,U53.G40,zero_mul,sub_zero] at hbp
  have hF := (U22.F_integrable 40 M).mul_continuousOn hv
  have he2 (x : ℝ) : (U22.F x-U22.lam)*x^(-2:ℤ)=U22.F x*x^(-2:ℤ)-U22.lam*x^(-2:ℤ) := by ring
  simp_rw [he2] at hbp
  rw [intervalIntegral.integral_sub hF (hv.intervalIntegrable.const_mul U22.lam),
    intervalIntegral.integral_const_mul,U53.power_integral2 hM,zpow_neg_one] at hbp
  have hg := weighted_G_lower hM
  simp only [one_div] at hbp ⊢
  linarith

/-- PROOF-DRAFT: lower tail for the literal package integrand, from cutoff40. -/
theorem tail_integral_lower {M : ℝ} (hM : 40 ≤ M) :
    U22.lam*(1/40-1/M)+U22.G M*M^(-2:ℤ)+mu*(1/1600-M^(-2:ℤ))
      -42/64000-1/12800 ≤ ∫ x in (40:ℝ)..M,innerR 7 6 U22.alpha x/x^3 := by
  have hF := (U22.F_integrable 40 M).mul_continuousOn (U53.power_cont (-2) hM)
  have h3 : IntervalIntegrable (fun x : ℝ=>x^(-3:ℤ)) volume 40 M := (U53.power_cont (-3) hM).intervalIntegrable
  have hmono : (∫ x in (40:ℝ)..M,U22.F x*x^(-2:ℤ)-(1/4:ℝ)*x^(-3:ℤ)) ≤
      ∫ x in (40:ℝ)..M,innerR 7 6 U22.alpha x/x^3 := by
    apply intervalIntegral.integral_mono_on hM (hF.sub (h3.const_mul (1/4))) (U53.R_tail_integrable hM)
    intro x hx
    have hx0 : x≠0 := by linarith [hx.1]
    have hq := Q_lower_quarter x
    unfold U22.Q at hq
    calc
      _=(x*U22.F x-1/4)/x^3 := by rw [zpow_neg,zpow_ofNat,zpow_neg,zpow_ofNat]; field_simp <;> ring
      _≤_ := div_le_div_of_nonneg_right (by linarith) (pow_nonneg (by linarith [hx.1]) 3)
  rw [intervalIntegral.integral_sub hF (h3.const_mul (1/4)),
    intervalIntegral.integral_const_mul,U53.power_integral3 hM] at hmono
  have h0 : 0≤M^(-2:ℤ) := zpow_nonneg (by linarith) _
  have hf := weighted_F_lower hM
  linarith

/-- PROOF-DRAFT: exact cutoff40 input from the existing kernel certificates. -/
theorem arithmetic40_lower : (244541:ℝ)/100000 < thetaPkg 7 6 (3/40) 40 0 := by
  unfold thetaPkg
  rw [Iout_7_6,U53.innerIntegral40_value]
  norm_num

/-- PROOF-DRAFT: positive remaining boundary correction for every real cutoff. -/
lemma boundary_nonnegative {M : ℝ} (hM : 40 ≤ M) :
    0 ≤ 7*U22.lam*(1/M)+(U22.G M-mu)*M^(-2:ℤ) := by
  have hMpos : 0 < M := by linarith
  have hG := (U22.G_range M).1
  have hnum : 0 ≤ 7*U22.lam*M+U22.G M-mu := by
    rw [mu_value]
    norm_num [U22.lam] at *
    linarith
  calc
    _ = (7*U22.lam*M+U22.G M-mu)/M^2 := by
      rw [zpow_neg,zpow_ofNat]
      field_simp
      <;> ring
    _ ≥ 0 := div_nonneg hnum (sq_nonneg M)

/-- PROOF-DRAFT: same actual frozen arithmetic floor, proved using only cutoff40 cells. -/
theorem arithmetic_allM_strict (M : ℝ) (hM : 40 ≤ M) :
    (229:ℝ)/100 < Mathathon.P108.thetaPkg 7 6 (3/40) M 0 := by
  have ht := tail_integral_lower hM
  have hc := intervalIntegral.integral_add_adjacent_intervals
    (innerR_div_intervalIntegrable 7 6 U22.alpha 40 (by norm_num)) (U53.R_tail_integrable hM)
  have hA := arithmetic40_lower
  have hb := boundary_nonnegative hM
  unfold thetaPkg at hA ⊢
  rw [mu_value] at ht hb
  norm_num [U22.lam,U22.alpha] at ht hc hA hb ⊢
  simp only [div_eq_mul_inv] at ht hA hb hc ⊢
  linarith

/-- PROOF-DRAFT: the original package consequence for arbitrary analytic input above -139/100. -/
theorem theta_allM_gt (M U : ℝ) (hM : 40 ≤ M) (hU : (-139:ℝ)/100 < U) :
    (9:ℝ)/10 < Mathathon.P108.thetaPkg 7 6 (3/40) M U := by
  have hA := arithmetic_allM_strict M hM
  unfold thetaPkg at hA ⊢
  linarith

#print axioms Q_lower_quarter
#print axioms C_range
#print axioms H_range
#print axioms H_right
#print axioms centered_G_lower
#print axioms weighted_F_lower
#print axioms tail_integral_lower
#print axioms arithmetic40_lower
#print axioms arithmetic_allM_strict
#print axioms theta_allM_gt
end U58
