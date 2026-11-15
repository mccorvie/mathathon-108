import PackageTail.Centered
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! E217/U22. All new mathematical declarations have status PROOF-DRAFT. -/
noncomputable section
namespace U22
open MeasureTheory Set Real Filter Topology Mathathon.P108

def P (t : ℝ) : ℝ := (t^2-t)/2
def B (x : ℝ) : ℝ := P (frac x)
def G (x : ℝ) : ℝ := 2*lam*B x-(12*lam/alpha)*B (alpha*x)

lemma P_deriv (t : ℝ) : HasDerivAt P (t-1/2) t := by
  have h := (((hasDerivAt_id t).pow 2).sub (hasDerivAt_id t)).div_const 2
  exact h.congr_deriv (by dsimp;ring)

lemma B_continuous : Continuous B := by
  have h : ContinuousOn P (Icc (0:ℝ) 1) := by unfold P;fun_prop
  have hc := h.comp_fract'' (show P 0=P 1 by norm_num [P])
  change Continuous (fun x=>P (frac x))
  simpa only [frac,Int.fract,Function.comp_def] using hc

lemma B_range (x : ℝ) : (-1:ℝ)/8≤B x ∧ B x≤0 := by
  have hf := frac_range x
  unfold B P
  constructor <;> nlinarith [sq_nonneg (frac x-1/2)]

lemma B_right (x : ℝ) : HasDerivWithinAt B (frac x-1/2) (Ici x) x := by
  have hd := (P_deriv (x-(⌊x⌋:ℝ))).comp x ((hasDerivAt_id x).sub_const (⌊x⌋:ℝ))
  have hf : ∀ᶠ y in 𝓝[≥] x,(⌊y⌋:ℤ)=⌊x⌋ :=
    tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have h : HasDerivWithinAt (fun y=>P (y-(⌊x⌋:ℝ))) (frac x-1/2) (Ici x) x := by
    convert! hd.hasDerivWithinAt (s:=Ici x) using 1 <;> simp only [Function.comp_def,id_eq,mul_one,frac]
  apply h.congr_of_eventuallyEq
  · filter_upwards [hf] with y hy
    unfold B frac
    rw [hy]
  · rfl

lemma G_continuous : Continuous G := by
  exact (B_continuous.const_mul _).sub
    ((B_continuous.comp (continuous_const.mul continuous_id)).const_mul _)

lemma G_range (x : ℝ) : -20≤G x ∧ G x≤20 := by
  have h1 := B_range x
  have h2 := B_range (alpha*x)
  unfold G
  norm_num [lam,alpha] at *
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

lemma G200 : G 200=0 := by norm_num [G,B,P,frac,lam,alpha]

lemma G_right (x : ℝ) : HasDerivWithinAt G (F x-lam) (Ioi x) x := by
  have hc : HasDerivWithinAt (fun y : ℝ=>alpha*y) alpha (Ici x) x :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul alpha).hasDerivWithinAt (s:=Ici x)
  have hcomp := (B_right (alpha*x)).comp x hc (show MapsTo (fun y : ℝ=>alpha*y) (Ici x) (Ici (alpha*x)) by
    intro y hy
    change alpha*x≤alpha*y
    exact mul_le_mul_of_nonneg_left (show x≤y from hy) (by norm_num [alpha]))
  have h := ((B_right x).const_mul (2*lam)).sub (hcomp.const_mul (12*lam/alpha))
  change HasDerivWithinAt G _ (Ici x) x at h
  have hd : 2*lam*(frac x-1/2)-(12*lam/alpha)*((frac (alpha*x)-1/2)*alpha)=F x-lam := by
    unfold F
    norm_num [lam,alpha]
    ring
  exact (h.congr_deriv hd).mono (fun y (hy : x<y)=>show x≤y from le_of_lt hy)

lemma F_integrable (a b : ℝ) : IntervalIntegrable F volume a b := by
  have hi : IntervalIntegrable (fun x : ℝ=>x) volume a b := continuous_id.intervalIntegrable _ _
  have hf := intervalIntegrable_floor a b
  have ha : IntervalIntegrable (fun x : ℝ=>alpha*x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hfa : IntervalIntegrable (fun x : ℝ=>(⌊alpha*x⌋:ℝ)) volume a b :=
    Monotone.intervalIntegrable (fun x y h=>by
      exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_left h (by norm_num [alpha])))
  exact ((intervalIntegrable_const.add ((hi.sub hf).const_mul 2)).sub
    ((ha.sub hfa).const_mul 12)).const_mul lam

end U22
#check U22.G_right
#print axioms U22.G_right
