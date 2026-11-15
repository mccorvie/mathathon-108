import FieldAverage.EndpointIntegrability

/-! E211/U16. Every new mathematical declaration has status PROOF-DRAFT.
These are angular averages; the whole E201 analytic claim remains CONJECTURE. -/
noncomputable section
namespace U16
open Real Set MeasureTheory

lemma J_curve_intervalIntegrable {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    IntervalIntegrable (fun θ=>J a (node b θ)) volume 0 (2*π) := by
  have hf := joint_integrable ha hb
  unfold jointIntegrable IntegrableOn at hf
  rw [uIoc_of_le (by positivity : (0:ℝ)≤2*π),uIoc_of_le ha,
    Measure.volume_eq_prod,←Measure.prod_restrict] at hf
  have hi := hf.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ)≤2*π)]
  simpa only [IntegrableOn,J,intervalIntegral.integral_of_le ha] using hi

def V6 (t : ℝ) : ℝ := 2*π*Real.sqrt t+J 1 t-6*J (3/40) t

def W (b : ℝ) : ℝ := 4*Real.sqrt b+T 1 b-6*T (3/40) b

/-- PROOF-DRAFT: the original external-field angular average equals the finite expression. -/
theorem V6_angular_mean {b : ℝ} (hb : 0<b) : angularAverage b V6=W b := by
  have hi1 := J_curve_intervalIntegrable (by norm_num : (0:ℝ)≤1) hb
  have hia := J_curve_intervalIntegrable (by norm_num : (0:ℝ)≤3/40) hb
  have his : IntervalIntegrable (fun θ=>Real.sqrt (node b θ)) volume 0 (2*π) :=
    (by unfold node; fun_prop : Continuous (fun θ : ℝ=>Real.sqrt (node b θ))).intervalIntegrable _ _
  have h1 := J_angular_mean (by norm_num : (0:ℝ)≤1) hb
  have ha := J_angular_mean (by norm_num : (0:ℝ)≤3/40) hb
  have hs := sqrt_angular_mean hb
  unfold angularAverage at h1 ha ⊢
  unfold V6 W
  rw [intervalIntegral.integral_sub ((his.const_mul _).add hi1) (hia.const_mul _),
    intervalIntegral.integral_add (his.const_mul _) hi1,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  calc
    _=2*π*((2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,Real.sqrt (node b θ)))
      +(2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,J 1 (node b θ))
      -6*((2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,J (3/40) (node b θ))) := by ring
    _=2*π*(2*Real.sqrt b/π)+T 1 b-6*T (3/40) b := by rw [hs,h1,ha]
    _=4*Real.sqrt b+T 1 b-6*T (3/40) b := by field_simp; ring

end U16
#check U16.V6_angular_mean
#print axioms U16.V6_angular_mean
