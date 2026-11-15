import FieldAverage.SqrtMean

/-! E211/U16. Every new mathematical declaration has status PROOF-DRAFT.
The explicit integrability premise in the reduction is not an established fact here. -/
noncomputable section
namespace U16
open Real Set MeasureTheory

def J (a t : ℝ) : ℝ := ∫ u in (0:ℝ)..a,Real.log (t+u^2)

def angularAverage (b : ℝ) (f : ℝ→ℝ) : ℝ :=
  (2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,f (node b θ))

def jointIntegrable (a b : ℝ) : Prop :=
  IntegrableOn (fun p : ℝ×ℝ=>Real.log (node b p.1+p.2^2))
    (uIoc (0:ℝ) (2*π) ×ˢ uIoc (0:ℝ) a)

/-- PROOF-DRAFT conditional reduction: the precise product integrability premise is explicit. -/
theorem J_angular_mean_of_integrable {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (hf : jointIntegrable a b) : angularAverage b (J a)=T a b := by
  unfold jointIntegrable at hf
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F:=fun θ u : ℝ=>Real.log (node b θ+u^2)) (a:=0) (b:=2*π) (c:=0) (d:=a) hf
  unfold angularAverage J
  rw [hswap,
    ←intervalIntegral.integral_const_mul]
  change (∫ u in (0:ℝ)..a,angularLog b u)=T a b
  calc
    _=(∫ u in (0:ℝ)..a,2*Real.log ((u+Real.sqrt (u^2+b))/2)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ha] at hu
      exact angularLog_eq hb hu.1
    _=T a b := integral_log_root hb a

end U16
#check U16.J_angular_mean_of_integrable
#print axioms U16.J_angular_mean_of_integrable
