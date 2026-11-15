import ArcBridge.Identification
import FieldAverage.EndpointPotential

/-! E211 / [108/U16], Codex, event work.
Every new mathematical declaration in this file carries status PROOF-DRAFT.
The whole E201 analytic result remains CONJECTURE. -/

noncomputable section
namespace U16
open Real MeasureTheory

def node (b θ : ℝ) : ℝ := b*(1+Real.cos θ)/2

def angularLog (b u : ℝ) : ℝ :=
  (2*π)⁻¹*(∫ θ in (0:ℝ)..2*π, Real.log (node b θ+u^2))

lemma node_nonneg {b : ℝ} (hb : 0≤b) (θ : ℝ) : 0≤node b θ := by
  unfold node
  have hc := Real.neg_one_le_cos θ
  have hp : 0≤1+Real.cos θ := by linarith
  exact div_nonneg (mul_nonneg hb hp) (by norm_num)

lemma omega_neg_sq {b : ℝ} (hb : 0<b) {u : ℝ} (hu : 0≤u) :
    Apery.Uω 0 b (-u^2)=2*Real.log ((u+Real.sqrt (u^2+b))/2) := by
  rw [Apery.Uω_of_le hb (by nlinarith : -u^2≤0)]
  have hroot : Real.sqrt ((-u^2-0)*(-u^2-b))=u*Real.sqrt (u^2+b) := by
    rw [show (-u^2-0)*(-u^2-b)=u^2*(u^2+b) by ring,
      Real.sqrt_mul (sq_nonneg u),Real.sqrt_sq hu]
  rw [hroot]
  have hs := Real.sq_sqrt (by linarith [sq_nonneg u] : 0≤u^2+b)
  have he : ((0+b)/2-(-u^2)+u*Real.sqrt (u^2+b))/2=
      ((u+Real.sqrt (u^2+b))/2)^2 := by nlinarith
  rw [he,Real.log_pow]
  norm_num

lemma angularLog_eq_angularMean {b : ℝ} (hb : 0<b) (u : ℝ) :
    angularLog b u=U14.angularMean 0 b (-u^2) := by
  unfold angularLog U14.angularMean
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  congr 1
  have he : -u^2-((0+b)/2+(b-0)/2*Real.cos θ)=-(node b θ+u^2) := by
    unfold node
    ring
  rw [he,abs_neg,abs_of_nonneg (by nlinarith [node_nonneg hb.le θ])]

/-- PROOF-DRAFT: the one-log average, including the endpoint u=0. -/
theorem angularLog_eq {b : ℝ} (hb : 0<b) {u : ℝ} (hu : 0≤u) :
    angularLog b u=2*Real.log ((u+Real.sqrt (u^2+b))/2) := by
  rw [angularLog_eq_angularMean hb,
    U14.angularMean_eq_closed hb,←U14.omega_eq_closed hb,omega_neg_sq hb hu]

end U16
#check U16.angularLog_eq
#print axioms U16.angularLog_eq
