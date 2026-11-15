import Apery.Gaussian

/-! E223/U28, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
General-measure adaptation of prior Apery/ZeroMass.lean:133-209 via the 1D convolution identity.
Whole E201 remains CONJECTURE. No compactness or non-atomicity is used for Gaussian positivity. -/
noncomputable section
namespace U28
open MeasureTheory Set Real

def gauss (t x y : ℝ) : ℝ := Real.exp (-t*(x-y)^2)
def feature (μ : Measure ℝ) (t u : ℝ) : ℝ := ∫ x,gauss (2*t) x u ∂μ
def gaussianPair (μ ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ p : ℝ×ℝ,gauss t p.1 p.2 ∂μ.prod ν

lemma gauss_le_one {t : ℝ} (ht : 0≤t) (x y : ℝ) : gauss t x y≤1 := by
  unfold gauss
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x-y)])

lemma gauss_pair_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0≤t) : Integrable (fun p : ℝ×ℝ=>gauss t p.1 p.2) (μ.prod ν) := by
  refine (integrable_const (1:ℝ)).mono' (by unfold gauss;fun_prop) ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_of_pos (show 0<gauss t p.1 p.2 by unfold gauss;positivity)]
  exact gauss_le_one ht _ _

lemma gauss_product_integrable {t : ℝ} (ht : 0<t) (x y : ℝ) :
    Integrable (fun u=>gauss (2*t) x u*gauss (2*t) y u) := by
  have he : (fun u=>gauss (2*t) x u*gauss (2*t) y u)=
      (fun u=>Real.exp (-(4*t)*(u-(x+y)/2)^2)*Real.exp (-t*(x-y)^2)) := by
    funext u
    unfold gauss
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (Apery.integrable_gaussian_sub (by linarith : 0<4*t) ((x+y)/2)).mul_const _

lemma gauss_triple_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0<t) :
    Integrable (fun p : (ℝ×ℝ)×ℝ=>gauss (2*t) p.1.1 p.2*gauss (2*t) p.1.2 p.2)
      ((μ.prod ν).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : (ℝ×ℝ)×ℝ=>gauss (2*t) p.1.1 p.2*gauss (2*t) p.1.2 p.2)
      ((μ.prod ν).prod volume) := by unfold gauss;fun_prop
  rw [integrable_prod_iff hm]
  constructor
  · exact Filter.Eventually.of_forall (fun p=>gauss_product_integrable ht p.1 p.2)
  · have he (p : ℝ×ℝ) :
        (∫ u,‖gauss (2*t) p.1 u*gauss (2*t) p.2 u‖)=
          Real.sqrt (π/(4*t))*gauss t p.1 p.2 := by
      unfold gauss
      simp_rw [Real.norm_eq_abs,abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
      exact Apery.gaussian_conv_one t p.1 p.2
    simp_rw [he]
    exact (gauss_pair_integrable μ ν ht.le).const_mul _

/-- PROOF-DRAFT: exact Gaussian factorization for arbitrary finite positive Borel measures. -/
theorem gaussian_factorization (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0<t) :
    Real.sqrt (π/(4*t))*gaussianPair μ ν t=
      ∫ u,feature μ t u*feature ν t u := by
  have h := integral_integral_swap (μ:=μ.prod ν) (ν:=volume)
    (f:=fun (p : ℝ×ℝ) (u : ℝ)=>gauss (2*t) p.1 u*gauss (2*t) p.2 u)
    (gauss_triple_integrable μ ν ht)
  have he (p : ℝ×ℝ) : (∫ u,gauss (2*t) p.1 u*gauss (2*t) p.2 u)=
      Real.sqrt (π/(4*t))*gauss t p.1 p.2 := Apery.gaussian_conv_one t p.1 p.2
  simp_rw [he] at h
  rw [integral_const_mul] at h
  have hf (u : ℝ) : (∫ p : ℝ×ℝ,gauss (2*t) p.1 u*gauss (2*t) p.2 u ∂μ.prod ν)=
      feature μ t u*feature ν t u := by
    simpa only [feature] using (integral_prod_mul (μ:=μ) (ν:=ν)
      (fun x : ℝ=>gauss (2*t) x u) (fun y : ℝ=>gauss (2*t) y u))
  simpa only [hf,gaussianPair] using h

lemma feature_product_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0<t) : Integrable (fun u=>feature μ t u*feature ν t u) := by
  have h := (gauss_triple_integrable μ ν ht).integral_prod_right
  have hf (u : ℝ) : (∫ p : ℝ×ℝ,gauss (2*t) p.1 u*gauss (2*t) p.2 u ∂μ.prod ν)=
      feature μ t u*feature ν t u := by
    simpa only [feature] using (integral_prod_mul (μ:=μ) (ν:=ν)
      (fun x : ℝ=>gauss (2*t) x u) (fun y : ℝ=>gauss (2*t) y u))
  simpa only [hf] using h

/-- PROOF-DRAFT: Gaussian positive definiteness for the difference of arbitrary finite measures. -/
theorem gaussian_difference_nonneg (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0<t) :
    0≤gaussianPair μ μ t+gaussianPair ν ν t-2*gaussianPair μ ν t := by
  have hμμ := feature_product_integrable μ μ ht
  have hνν := feature_product_integrable ν ν ht
  have hμν := feature_product_integrable μ ν ht
  have he (u : ℝ) : (feature μ t u-feature ν t u)^2=
      feature μ t u*feature μ t u+feature ν t u*feature ν t u-
        2*(feature μ t u*feature ν t u) := by ring
  have hn : 0≤∫ u,(feature μ t u-feature ν t u)^2 := integral_nonneg (fun _=>sq_nonneg _)
  simp_rw [he] at hn
  have hsub := integral_sub (hμμ.add hνν) (hμν.const_mul 2)
  have hadd := integral_add hμμ hνν
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub,hadd,integral_const_mul,←gaussian_factorization μ μ ht,
    ←gaussian_factorization ν ν ht,←gaussian_factorization μ ν ht] at hn
  have hp : 0<Real.sqrt (π/(4*t)) := Real.sqrt_pos.mpr (by positivity)
  nlinarith

end U28
#print axioms U28.gaussian_factorization
#print axioms U28.gaussian_difference_nonneg
