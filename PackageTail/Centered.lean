import PeriodShift

/-! E217/U22, Codex. All new mathematical declarations have status PROOF-DRAFT.
The overall package statement remains CONJECTURE pending parent gate and human comparison. -/
noncomputable section
namespace U22
open MeasureTheory Set Real Mathathon.P108

def lam : ℝ := 37/40
def alpha : ℝ := 3/40
def frac (x : ℝ) : ℝ := x-(⌊x⌋:ℝ)
def F (x : ℝ) : ℝ := lam*(6+2*frac x-12*frac (alpha*x))
def Q (x : ℝ) : ℝ := innerR 7 6 alpha x-x*F x

def delta (y z : ℝ) : ℝ := ell y z-2*y

lemma delta_abs (y z : ℝ) : |delta y z|≤1 := by
  have h1 := Int.floor_le (y-z)
  have h2 := Int.lt_floor_add_one (y-z)
  have h3 := Int.floor_le (y+z)
  have h4 := Int.lt_floor_add_one (y+z)
  rw [abs_le]
  unfold delta ell
  constructor <;> linarith

lemma delta_integrable (y : ℝ) : IntervalIntegrable (delta y) volume 0 (1/2) :=
  (ell_intervalIntegrable y 0 (1/2)).sub intervalIntegrable_const

lemma delta_integral (y : ℝ) : (∫ z in (0:ℝ)..(1/2),delta y z)=0 := by
  unfold delta
  rw [intervalIntegral.integral_sub (ell_intervalIntegrable _ _ _) intervalIntegrable_const,
    integral_ell,intervalIntegral.integral_const]
  simp
  <;> ring

lemma delta_mul_integrable (y w : ℝ) :
    IntervalIntegrable (fun z=>delta y z*delta w z) volume 0 (1/2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine Integrable.mul_bdd (c:=1) (delta_integrable y).1 ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold delta ell
    fun_prop
  · exact Filter.Eventually.of_forall (fun z=>by simpa only [Real.norm_eq_abs] using delta_abs w z)

lemma gamma_centered (x : ℝ) :
    (∫ z in (0:ℝ)..(1/2),gammaIntegrand 7 6 alpha x z)=
      (Tc 6 alpha x-6*alpha*x)*(Tc 6 alpha x+6*alpha*x-2*x-7)/2
      -9*(∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta (alpha*x) z)
      +3*(∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta x z) := by
  let A : ℝ := (Tc 6 alpha x-6*alpha*x)*(Tc 6 alpha x+6*alpha*x-2*x-7)
  let B : ℝ := 6*x+21-36*alpha*x
  let C : ℝ := 6*alpha*x-Tc 6 alpha x
  have he (z : ℝ) : gammaIntegrand 7 6 alpha x z=
      A+B*delta (alpha*x) z+C*delta x z
      -9*(delta (alpha*x) z*delta (alpha*x) z)+3*(delta (alpha*x) z*delta x z) := by
    unfold gammaIntegrand delta A B C
    norm_num
    ring
  simp_rw [he]
  have h0 : IntervalIntegrable (fun _ : ℝ=>A) volume 0 (1/2) := intervalIntegrable_const
  have h1 := (delta_integrable (alpha*x)).const_mul B
  have h2 := (delta_integrable x).const_mul C
  have h3 := (delta_mul_integrable (alpha*x) (alpha*x)).const_mul 9
  have h4 := (delta_mul_integrable (alpha*x) x).const_mul 3
  rw [intervalIntegral.integral_add (((h0.add h1).add h2).sub h3) h4,
    intervalIntegral.integral_sub ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul,delta_integral,mul_zero,add_zero,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  dsimp [A]
  ring

/-- PROOF-DRAFT: exact centered-floor remainder identity. -/
theorem Q_centered (x : ℝ) :
    Q x=2*(sigmaC 6 alpha x)^2-2*sigmaC 6 alpha x*nplus x
      -max (sigmaC 6 alpha x-nplus x) 0
      +9*(∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta (alpha*x) z)
      -3*(∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta x z)
      +(frac (2*lam*x)-(frac (2*lam*x))^2)/2 := by
  unfold Q innerR innerGamma
  rw [gamma_centered]
  unfold F innerN Jfun sigmaC nplus Hc lam alpha frac
  norm_num
  unfold Int.fract
  ring

lemma frac_range (x : ℝ) : 0≤frac x ∧ frac x≤1 := by
  unfold frac
  constructor <;> linarith [Int.floor_le x,Int.lt_floor_add_one x]

lemma sigma_range (x : ℝ) : 0≤sigmaC 6 alpha x ∧ sigmaC 6 alpha x≤1/2 := by
  unfold sigmaC Tc
  constructor <;> linarith [Int.floor_le (2*Hc 6 alpha*x),Int.lt_floor_add_one (2*Hc 6 alpha*x)]

lemma nplus_range (x : ℝ) : 0≤nplus x ∧ nplus x≤1/2 := by
  unfold nplus
  constructor <;> linarith [Int.floor_le (2*x),Int.lt_floor_add_one (2*x)]

/-- PROOF-DRAFT: a uniform global lower bound on the exact remainder. -/
theorem Q_lower (x : ℝ) : (-5:ℝ)/2≤Q x := by
  have hs := sigma_range x
  have hn := nplus_range x
  have hm : max (sigmaC 6 alpha x-nplus x) 0≤1/2 := max_le (by linarith) (by norm_num)
  have hsn : sigmaC 6 alpha x*nplus x≤1/4 := by nlinarith [mul_nonneg hs.1 hn.1,mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hn.2)]
  have hsq : 0≤∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta (alpha*x) z := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro z _
    nlinarith [sq_nonneg (delta (alpha*x) z)]
  have hcross : (∫ z in (0:ℝ)..(1/2),delta (alpha*x) z*delta x z)≤1/2 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1/2)
      (delta_mul_integrable (alpha*x) x) (intervalIntegrable_const (c:=(1:ℝ))) ?_
    · simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] using h
    · intro z _
      have ha := delta_abs (alpha*x) z
      have hb := delta_abs x z
      calc delta (alpha*x) z*delta x z≤|delta (alpha*x) z*delta x z| := le_abs_self _
           _≤1 := by rw [abs_mul];nlinarith [abs_nonneg (delta (alpha*x) z),abs_nonneg (delta x z)]
  have hf := frac_range (2*lam*x)
  have hp : 0≤frac (2*lam*x)-(frac (2*lam*x))^2 := by nlinarith
  rw [Q_centered]
  linarith [sq_nonneg (sigmaC 6 alpha x)]

end U22
#check U22.Q_lower
#print axioms U22.Q_lower
