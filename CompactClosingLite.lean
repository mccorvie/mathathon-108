import MarginPieces.Chunk000
import MarginPieces.Chunk001
import MarginPieces.Chunk002
import MarginPieces.Chunk003
import MarginPieces.Chunk004
import MarginPieces.Chunk005
import MarginPieces.Chunk006
import MarginPieces.Chunk007
import MarginPieces.Chunk008
import MarginPieces.Chunk009
import MarginPieces.Chunk010
import MarginPieces.Chunk011
import MarginPieces.Chunk012
import MarginPieces.Chunk013
import MarginPieces.Chunk014
import MarginPieces.Chunk015
import PackageTail.Primitive
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
E248/U53, Codex (GPT-6), event work Sat Nov 14 2026.
All mathematical claims in this module are PROOF-DRAFT.
Overall compact zeta(5) route remains CONJECTURE pending parent gate and human comparison.
Uses only first 16 pre-existing U18 chunk modules, without UPackageMargin or E245 imports.
Q/upper-tail proof adapted from frozen E245/U50 and U22; exact source map is supplied.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
open MeasureTheory Set Real Mathathon.P108
namespace U53

/-- PROOF-DRAFT: exact recombination of the existing kernel cell integrals on [3,40]. -/
theorem innerIntegral40_value :
    (∫ x in (3:ℝ)..40, innerR 7 6 (3/40) x / x^3) = (326882988539734810408990473093139159093973/575013403956391564243577805652060235520000:ℝ) := by
  have h := MarginPieces.chunk_0
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (120/23:ℝ) (15/2:ℝ) (10638527/22176000:ℝ) (1536908029/19603584000:ℝ) h MarginPieces.chunk_1
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (15/2:ℝ) (420/43:ℝ) (142095661/254592000:ℝ) (-(1012095961/66853248000:ℝ)) h MarginPieces.chunk_2
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (420/43:ℝ) (280/23:ℝ) (707864960911/1303638336000:ℝ) (-(1323874307579/26456189760000:ℝ)) h MarginPieces.chunk_3
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (280/23:ℝ) (29/2:ℝ) (55426887071363/112438806480000:ℝ) (7502365765669/1134439676370000:ℝ) h MarginPieces.chunk_4
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (29/2:ℝ) (620/37:ℝ) (704386958141411/1410001021520000:ℝ) (224727991002371393/5140650573805824000:ℝ) h MarginPieces.chunk_5
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (620/37:ℝ) (820/43:ℝ) (143974498445671176211/265009400270334720000:ℝ) (12950950551423942019/638203380967536384000:ℝ) h MarginPieces.chunk_6
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (820/43:ℝ) (500/23:ℝ) (174123087934668374996129/308962491608719428480000:ℝ) (979579827467648203/249665666466216000000:ℝ) h MarginPieces.chunk_7
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (500/23:ℝ) (24:ℝ) (817999449793403651326793/1441416048486510096000000:ℝ) (-(602616348580518599/106077330401328000000:ℝ)) h MarginPieces.chunk_8
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (24:ℝ) (53/2:ℝ) (6151863371936428875787211/10949957248335855029280000:ℝ) (-(1294421636369589671/94728034034395776000:ℝ)) h MarginPieces.chunk_9
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (53/2:ℝ) (1060/37:ℝ) (75075973856485574817976628023/136962065262184874706234240000:ℝ) (787606742817033263/57376010167572096000:ℝ) h MarginPieces.chunk_10
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1060/37:ℝ) (1340/43:ℝ) (3678934239787421280916455623/6547559546232975985172640000:ℝ) (10885859801910186908376367/995928600453513453264384000:ℝ) h MarginPieces.chunk_11
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1340/43:ℝ) (770/23:ℝ) (345345133762448793893089714104707843/602897470454987856446325852464640000:ℝ) (44434560946127160537853/11341848971103380369640000:ℝ) h MarginPieces.chunk_12
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (770/23:ℝ) (1320/37:ℝ) (4167295985667445642424572506361176739/7225771175751570876513427754165760000:ℝ) (-(1717781788098414095879/16787176225516097050890240:ℝ)) h MarginPieces.chunk_13
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1320/37:ℝ) (38:ℝ) (13344242064584817314460223870286706007/23141996873690841861265978077530880000:ℝ) (-(4271842881623818948289/1341427252053562891176960:ℝ)) h MarginPieces.chunk_14
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (38:ℝ) (1640/43:ℝ) (70393003838171878234130594706554200937563/122755670507544266523909868622349937920000:ℝ) (-(70767/194189120:ℝ)) h MarginPieces.i_300
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1640/43:ℝ) (880/23:ℝ) (151804159069048633559653204236173816873057/264893815305753417235805505974544602880000:ℝ) (-(790101/2603532800:ℝ)) h MarginPieces.i_301
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (880/23:ℝ) (115/3:ℝ) (40706377596302483012812351885745739879647/71069072399104575355947818676097332480000:ℝ) (-(28783/163863040:ℝ)) h MarginPieces.i_302
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (115/3:ℝ) (1420/37:ℝ) (85087233150631908306868720543088765064671/148598969561764112107890893595476240640000:ℝ) (-(22857/213335120:ℝ)) h MarginPieces.i_303
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1420/37:ℝ) (77/2:ℝ) (262611441592919357488629270515134377930767/458718558212402259115663193272991873280000:ℝ) (-(137259/487968800:ℝ)) h MarginPieces.i_304
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (77/2:ℝ) (1660/43:ℝ) (40666288917999571010928530087818952021747/71069072399104575355947818676097332480000:ℝ) (-(2171727/9335972800:ℝ)) h MarginPieces.i_305
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1660/43:ℝ) (890/23:ℝ) (306720892849053724170784145346640422294491/536248455375061795867606268192370781440000:ℝ) (-(17044407/87308430400:ℝ)) h MarginPieces.i_306
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (890/23:ℝ) (1440/37:ℝ) (29261529739888860375155856625882777657842217/51176192952118849217678424703033360961280000:ℝ) (-(9671/21386700:ℝ)) h MarginPieces.i_307
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1440/37:ℝ) (39:ℝ) (328521213738708210492135425579503635279953/575013403956391564243577805652060235520000:ℝ) (-(9041/58406400:ℝ)) h MarginPieces.i_308
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (39:ℝ) (1680/43:ℝ) (4269618661396749797265743485938795594512489/7475174251433090335166511473476783061760000:ℝ) (-(67927/317990400:ℝ)) h MarginPieces.i_309
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1680/43:ℝ) (900/23:ℝ) (328309374173569616036124124348556320513553/575013403956391564243577805652060235520000:ℝ) (-(8579/47040000:ℝ)) h MarginPieces.i_310
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (900/23:ℝ) (1460/37:ℝ) (328204505126109116817806827282342693286501/575013403956391564243577805652060235520000:ℝ) (-(450079/479610000:ℝ)) h MarginPieces.i_311
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1460/37:ℝ) (79/2:ℝ) (23919537480318706964710068063575997794276429/41975978488816584189781179812600397192960000:ℝ) (-(365241/3325828900:ℝ)) h MarginPieces.i_312
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (79/2:ℝ) (1700/43:ℝ) (25880538193367782917116981487194828207165867/45426058912554933575242646646512758606080000:ℝ) (-(6742029/72145960000:ℝ)) h MarginPieces.i_313
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1700/43:ℝ) (910/23:ℝ) (222732649770175701146747095664687430915997/391009114690346263685632907843400960153600:ℝ) (-(7703211/95728360000:ℝ)) h MarginPieces.i_314
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (910/23:ℝ) (40:ℝ) (4257522663425214478730536678629259076863649/7475174251433090335166511473476783061760000:ℝ) (-(5703/5299840:ℝ)) h MarginPieces.i_315
  norm_num at h
  exact h.2
/-- PROOF-DRAFT: a coarse global upper bound for the exact centered remainder. -/
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



/-- PROOF-DRAFT: primitive vanishes at the smaller period boundary. -/
lemma G40 : U22.G 40 = 0 := by
  norm_num [U22.G,U22.B,U22.P,U22.frac,U22.lam,U22.alpha]

lemma power_cont (n : ℤ) {M : ℝ} (hM : 40≤M) :
    ContinuousOn (fun x : ℝ=>x^n) (uIcc (40:ℝ) M) := by
  apply ContinuousOn.zpow₀ continuousOn_id
  intro x hx
  rw [uIcc_of_le hM] at hx
  left
  change x≠0
  linarith [hx.1]

lemma power_integral2 {M : ℝ} (hM : 40≤M) :
    (∫ x in (40:ℝ)..M,x^(-2:ℤ))=1/40-M^(-1:ℤ) := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
    ring
  · rw [uIcc_of_le hM]
    intro h
    linarith [h.1]

lemma power_integral3 {M : ℝ} (hM : 40≤M) :
    (∫ x in (40:ℝ)..M,x^(-3:ℤ))=(1/1600-M^(-2:ℤ))/2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
    ring
  · rw [uIcc_of_le hM]
    intro h
    linarith [h.1]

/-- PROOF-DRAFT: integrability of the literal package tail from40. -/
lemma R_tail_integrable {M : ℝ} (hM : 40 ≤ M) :
    IntervalIntegrable (fun x=>innerR 7 6 U22.alpha x/x^3) volume 40 M := by
  exact (innerR_div_intervalIntegrable 7 6 U22.alpha 40 (by norm_num)).symm.trans
    (innerR_div_intervalIntegrable 7 6 U22.alpha M (by linarith))

/-- PROOF-DRAFT: upper counterpart of U22's integration by parts bound. -/
theorem centered_weighted_upper {M : ℝ} (hM : 40 ≤ M) :
    (∫ x in (40:ℝ)..M, (U22.F x-U22.lam)*x^(-2:ℤ)) ≤ (20:ℝ)/1600 := by
  have hv := power_cont (-2) hM
  have hw := power_cont (-3) hM
  have hD := ((U22.F_integrable 40 M).sub (intervalIntegrable_const (c:=U22.lam))).mul_continuousOn hv
  have hH : IntervalIntegrable (fun x=>U22.G x*x^(-3:ℤ)) volume 40 M :=
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
  rw [intervalIntegral.integral_sub hD (hH.const_mul 2),
    intervalIntegral.integral_const_mul,G40,zero_mul,sub_zero] at hbp
  have hbound : (∫ x in (40:ℝ)..M,U22.G x*x^(-3:ℤ)) ≤
      (20:ℝ)*(∫ x in (40:ℝ)..M,x^(-3:ℤ)) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hM hH (hw.intervalIntegrable.const_mul 20)
    intro x hx
    exact mul_le_mul_of_nonneg_right (U22.G_range x).2 (zpow_nonneg (by linarith [hx.1]) _)
  have hpoint : U22.G M*M^(-2:ℤ) ≤ (20:ℝ)*M^(-2:ℤ) :=
    mul_le_mul_of_nonneg_right (U22.G_range M).2 (zpow_nonneg (by linarith) _)
  rw [power_integral3 hM] at hbound
  linarith

/-- PROOF-DRAFT: weighted periodic term upper bound. -/
theorem weighted_F_upper {M : ℝ} (hM : 40 ≤ M) :
    (∫ x in (40:ℝ)..M,U22.F x*x^(-2:ℤ)) ≤ U22.lam*(1/40-1/M)+20/1600 := by
  have h := centered_weighted_upper hM
  have hF := (U22.F_integrable 40 M).mul_continuousOn (power_cont (-2) hM)
  have he (x : ℝ) : (U22.F x-U22.lam)*x^(-2:ℤ)=U22.F x*x^(-2:ℤ)-U22.lam*x^(-2:ℤ) := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_sub hF ((power_cont (-2) hM).intervalIntegrable.const_mul U22.lam),
    intervalIntegral.integral_const_mul,power_integral2 hM,zpow_neg_one] at h
  simp only [one_div] at h ⊢
  linarith

/-- PROOF-DRAFT: upper tail derived from the exact package integrand. -/
theorem tail_integral_upper {M : ℝ} (hM : 40 ≤ M) :
    (∫ x in (40:ℝ)..M, innerR 7 6 U22.alpha x / x^3) ≤
      U22.lam*(1/40-1/M)+47/3200 := by
  have hF := (U22.F_integrable 40 M).mul_continuousOn (power_cont (-2) hM)
  have h3 : IntervalIntegrable (fun x : ℝ=>x^(-3:ℤ)) volume 40 M := (power_cont (-3) hM).intervalIntegrable
  have hmono : (∫ x in (40:ℝ)..M, innerR 7 6 U22.alpha x / x^3) ≤
      ∫ x in (40:ℝ)..M, U22.F x*x^(-2:ℤ)+7*x^(-3:ℤ) := by
    apply intervalIntegral.integral_mono_on hM (R_tail_integrable hM) (hF.add (h3.const_mul 7))
    intro x hx
    have hx0 : x≠0 := by linarith [hx.1]
    have hq := Q_upper x
    unfold U22.Q at hq
    calc
      _ ≤ (x*U22.F x+7)/x^3 :=
        div_le_div_of_nonneg_right (by linarith) (pow_nonneg (by linarith [hx.1]) 3)
      _ = _ := by rw [zpow_neg,zpow_ofNat,zpow_neg,zpow_ofNat]; field_simp
  rw [intervalIntegral.integral_add hF (h3.const_mul 7),
    intervalIntegral.integral_const_mul,power_integral3 hM] at hmono
  have h0 : 0≤M^(-2:ℤ) := zpow_nonneg (by linarith) _
  have hf := weighted_F_upper hM
  linarith

/-- PROOF-DRAFT: exact finite cell integrals give this rational upper bound at40. -/
theorem arithmetic40_upper : thetaPkg 7 6 (3/40) 40 0 < (244542:ℝ)/100000 := by
  unfold thetaPkg
  rw [Iout_7_6, innerIntegral40_value]
  norm_num

/-- PROOF-DRAFT: the actual arithmetic package at400 has a coarse upper bound. -/
theorem compact_arithmetic400_upper : thetaPkg 5 6 (3/40) 400 0 < (1337:ℝ)/1000 := by
  have ht := tail_integral_upper (M := 400) (by norm_num)
  have hc := intervalIntegral.integral_add_adjacent_intervals
    (innerR_div_intervalIntegrable 7 6 U22.alpha 40 (by norm_num))
    (R_tail_integrable (M := 400) (by norm_num))
  have hA := arithmetic40_upper
  have hs := theta_sstep_7_6 400 0 (by norm_num)
  unfold thetaPkg at hA hs ⊢
  norm_num [U22.lam, U22.alpha] at ht hc hA hs ⊢
  linarith

/-- PROOF-DRAFT: exact bridge scalar target, without caller-supplied hypotheses. -/
theorem compact_zeta5_margin_neg :
    Mathathon.P108.thetaPkg (5:ℝ) 6 (3/40) 400 (-2678491/2000000) < 0 := by
  have hA := compact_arithmetic400_upper
  unfold thetaPkg at hA ⊢
  linarith

#print axioms innerIntegral40_value
#print axioms Q_upper
#print axioms G40
#print axioms power_cont
#print axioms power_integral2
#print axioms power_integral3
#print axioms R_tail_integrable
#print axioms centered_weighted_upper
#print axioms weighted_F_upper
#print axioms tail_integral_upper
#print axioms arithmetic40_upper
#print axioms compact_arithmetic400_upper
#print axioms compact_zeta5_margin_neg
#check compact_zeta5_margin_neg
end U53
