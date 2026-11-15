import IntegralWitness.Measure

/-! E215/U20. Every new mathematical declaration carries status PROOF-DRAFT. -/
set_option maxHeartbeats 0
noncomputable section
namespace U20
open MeasureTheory Set Real Finset

lemma width_antitone : Antitone U11.width := by
  intro i j hij
  unfold U11.width
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤49/64) (by norm_num) hij) (by norm_num)

lemma max_width (i j : Fin 15) : max (U11.width i) (U11.width j)=U11.width (min i j) := by
  rcases le_total i j with h | h
  · rw [min_eq_left h,max_eq_left (width_antitone h)]
  · rw [min_eq_right h,max_eq_right (width_antitone h)]

lemma log_width (j : Fin 15) :
    Real.log (U11.width j/4)=Real.log (25/144)+(j.val:ℝ)*Real.log (49/64) := by
  have he : U11.width j/4=(25/144:ℝ)*(49/64)^j.val := by unfold U11.width;ring
  rw [he,Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)),Real.log_pow]

lemma coefficient0 : (∑ i : Fin 15,∑ j : Fin 15,U11.mass i*U11.mass j)=U11.lam^2 := by
  simp_rw [←Finset.mul_sum]
  rw [U11.mass_sum,←Finset.sum_mul,U11.mass_sum]
  ring

lemma coefficient1 :
    (∑ i : Fin 15,∑ j : Fin 15,U11.mass i*U11.mass j*((min i j).val:ℝ))=
      (233486993:ℝ)/100000000 := by
  norm_num [Fin.sum_univ_succ,U11.mass]

/-- PROOF-DRAFT: actual Borel energy equals the two-log expression of E206. -/
theorem energy_eq_logs : energy=U11.lam^2*Real.log (25/144)+
    (233486993/100000000)*Real.log (49/64) := by
  have hk (i j : Fin 15) : kernel (U11.width i) (U11.width j)=
      Real.log (25/144)+((min i j).val:ℝ)*Real.log (49/64) := by
    rw [kernel_eq (width_pos i) (width_pos j),max_width,log_width]
  rw [energy_eq_sum]
  simp_rw [hk]
  calc
    _=∑ i : Fin 15,∑ j : Fin 15,
      (U11.mass i*U11.mass j*Real.log (25/144)+
       U11.mass i*U11.mass j*((min i j).val:ℝ)*Real.log (49/64)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=(∑ i : Fin 15,∑ j : Fin 15,U11.mass i*U11.mass j)*Real.log (25/144)+
      (∑ i : Fin 15,∑ j : Fin 15,U11.mass i*U11.mass j*((min i j).val:ℝ))*Real.log (49/64) := by
      simp only [Finset.sum_add_distrib,←Finset.sum_mul]
    _=_ := by rw [coefficient0,coefficient1]

/-- The actual iterated Borel-integral witness of the explicit fifteen-atom trial. -/
def integralWitness : ℝ := energy-(∫ t,U16.V6 t ∂sigma)+U11.C6

/-- PROOF-DRAFT: complete identification with E206's literal finite expression. -/
theorem integralWitness_eq : integralWitness=U11.lb6Square15 := by
  unfold integralWitness U11.lb6Square15
  rw [energy_eq_logs,sigma_field_integral]

/-- PROOF-DRAFT: a bound for this explicit trial witness, not universal weak duality. -/
theorem integralWitness_gt : (-139:ℝ)/100 < integralWitness := by
  rw [integralWitness_eq]
  exact U11.lb6Square15_gt

end U20
#check U20.integralWitness_eq
#print axioms U20.integralWitness_eq
#check U20.integralWitness_gt
#print axioms U20.integralWitness_gt
