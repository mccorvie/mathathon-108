import IntegralWitness.Kernel

/-! E215/U20. Every new mathematical declaration has status PROOF-DRAFT. -/
noncomputable section
namespace U20
open MeasureTheory Set Real Finset
open Mathathon.P108.ArcMeasure

lemma width_pos (j : Fin 15) : 0<U11.width j := by
  unfold U11.width
  positivity

def atom (j : Fin 15) : Measure ℝ := arcsineMeasure 0 (U11.width j)

instance atom_probability (j : Fin 15) : IsProbabilityMeasure (atom j) := by
  unfold atom
  infer_instance

def sigma : Measure ℝ := ∑ j : Fin 15,ENNReal.ofReal (U11.mass j) • atom j

lemma sigma_mass : sigma Set.univ=ENNReal.ofReal U11.lam := by
  simp only [sigma,Measure.finsetSum_apply,Measure.smul_apply,atom,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j _=>(U11.mass_pos j).le),U11.mass_sum]

instance sigma_finite : IsFiniteMeasure sigma where
  measure_univ_lt_top := by rw [sigma_mass];exact ENNReal.ofReal_lt_top

lemma integrable_sigma (f : ℝ→ℝ) (hf : ∀ j,Integrable f (atom j)) : Integrable f sigma := by
  unfold sigma
  exact integrable_finsetSum_measure.mpr (fun j _=>(hf j).smul_measure ENNReal.ofReal_ne_top)

lemma integral_sigma (f : ℝ→ℝ) (hf : ∀ j,Integrable f (atom j)) :
    (∫ x,f x ∂sigma)=∑ j : Fin 15,U11.mass j*(∫ x,f x ∂atom j) := by
  unfold sigma
  rw [integral_finsetSum_measure (fun j _=>(hf j).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_measure,ENNReal.toReal_ofReal (U11.mass_pos j).le,smul_eq_mul]

lemma sigma_field_integrable : Integrable U16.V6 sigma :=
  integrable_sigma U16.V6 (fun j=>V6_integrable (width_pos j))

/-- PROOF-DRAFT: the actual field integral of the explicit fifteen-atom measure. -/
theorem sigma_field_integral :
    (∫ t,U16.V6 t ∂sigma)=∑ j : Fin 15,U11.mass j*U11.W (U11.width j) := by
  rw [integral_sigma U16.V6 (fun j=>V6_integrable (width_pos j))]
  apply Finset.sum_congr rfl
  intro j _
  unfold atom
  rw [field_integral (width_pos j),W_eq_U11]

def energy : ℝ := ∫ x,∫ y,Real.log |x-y| ∂sigma ∂sigma

lemma sigma_pair_integrable :
    Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (sigma.prod sigma) := by
  unfold sigma
  rw [←Measure.sum_fintype,Measure.prod_sum,Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij _
  rw [Measure.prod_smul_left,Measure.prod_smul_right]
  exact ((pair_integrable (width_pos ij.1) (width_pos ij.2)).smul_measure
    ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top

lemma log_atom_integrable (j : Fin 15) (x : ℝ) :
    Integrable (fun y=>Real.log |x-y|) (atom j) := log_integrable (width_pos j) x

lemma potential_atom_integrable (i j : Fin 15) :
    Integrable (fun x=>∫ y,Real.log |x-y| ∂atom j) (atom i) :=
  (pair_integrable (width_pos i) (width_pos j)).integral_prod_left

/-- PROOF-DRAFT: finite expansion of the actual iterated Borel logarithmic energy. -/
theorem energy_eq_sum : energy=
    ∑ i : Fin 15,∑ j : Fin 15,U11.mass i*U11.mass j*kernel (U11.width i) (U11.width j) := by
  have hin (x : ℝ) : (∫ y,Real.log |x-y| ∂sigma)=
      ∑ j : Fin 15,U11.mass j*(∫ y,Real.log |x-y| ∂atom j) :=
    integral_sigma _ (fun j=>log_atom_integrable j x)
  have hout (i : Fin 15) :
      Integrable (fun x=>∑ j : Fin 15,U11.mass j*(∫ y,Real.log |x-y| ∂atom j)) (atom i) := by
    apply integrable_finsetSum
    intro j _
    exact (potential_atom_integrable i j).const_mul _
  unfold energy
  simp_rw [hin]
  rw [integral_sigma _ hout]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>(potential_atom_integrable i j).const_mul _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  unfold kernel atom
  ring

end U20
#check U20.sigma_field_integral
#print axioms U20.sigma_field_integral
#check U20.energy_eq_sum
#print axioms U20.energy_eq_sum
