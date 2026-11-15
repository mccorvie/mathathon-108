import FiniteComparison.Kernel

/-! E220/U25, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT. -/
noncomputable section
namespace U25
open MeasureTheory Set Real Finset
open Mathathon.P108.ArcMeasure
open Mathathon.P108.FiniteDuality
variable {ι : Type*} [Fintype ι]

def rho (a b c : ι→ℝ) : Measure ℝ :=
  ∑ i,ENNReal.ofReal (c i) • arcsineMeasure (a i) (b i)

instance rho_finite (a b c : ι→ℝ) : IsFiniteMeasure (rho a b c) := by
  haveI (i : ι) : IsFiniteMeasure (ENNReal.ofReal (c i) • arcsineMeasure (a i) (b i)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold rho
  infer_instance

lemma rho_mass (a b c : ι→ℝ) (hc : ∀ i,0≤c i) (hmass : (∑ i,c i)=U11.lam) :
    rho a b c Set.univ=ENNReal.ofReal U11.lam := by
  simp only [rho,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _=>hc i),hmass]

lemma log_rho_integrable (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (x : ℝ) :
    Integrable (fun y=>Real.log |x-y|) (rho a b c) := by
  unfold rho
  exact integrable_finsetSum_measure.mpr (fun i _=>
    (log_integrable (hab i) x).smul_measure ENNReal.ofReal_ne_top)

lemma integral_rho (a b c : ι→ℝ) (hc : ∀ i,0≤c i) (f : ℝ→ℝ)
    (hf : ∀ i,Integrable f (arcsineMeasure (a i) (b i))) :
    (∫ x,f x ∂rho a b c)=∑ i,c i*(∫ x,f x ∂arcsineMeasure (a i) (b i)) := by
  unfold rho
  rw [integral_finsetSum_measure (fun i _=>(hf i).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,ENNReal.toReal_ofReal (hc i),smul_eq_mul]

lemma rho_pair_integrable (a b c : ι→ℝ) (hab : ∀ i,a i<b i) :
    Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|)
      ((rho a b c).prod (rho a b c)) := by
  unfold rho
  rw [←Measure.sum_fintype,Measure.prod_sum,Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij _
  rw [Measure.prod_smul_left,Measure.prod_smul_right]
  exact ((pair_integrable (hab ij.1) (hab ij.2)).smul_measure
    ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top

lemma potential_rho (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (hc : ∀ i,0≤c i) (x : ℝ) :
    (∫ y,Real.log |x-y| ∂rho a b c)=
      ∑ i,c i*(∫ y,Real.log |x-y| ∂arcsineMeasure (a i) (b i)) :=
  integral_rho a b c hc _ (fun i=>log_integrable (hab i) x)

lemma potential_rho_integrable (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (hc : ∀ i,0≤c i)
    {l r : ℝ} (hlr : l<r) :
    Integrable (fun x=>∫ y,Real.log |x-y| ∂rho a b c) (arcsineMeasure l r) := by
  simp_rw [potential_rho a b c hab hc]
  exact integrable_finsetSum _ (fun i _=>((pair_integrable hlr (hab i)).integral_prod_left).const_mul _)

lemma mutualEnergy_rho (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (hc : ∀ i,0≤c i)
    {l r : ℝ} (hlr : l<r) :
    (∫ x,∫ y,Real.log |x-y| ∂rho a b c ∂arcsineMeasure l r)=
      ∑ i,c i*mutualEnergy l r (a i) (b i) := by
  simp_rw [potential_rho a b c hab hc]
  rw [integral_finsetSum _ (fun i _=>((pair_integrable hlr (hab i)).integral_prod_left).const_mul _)]
  simp only [integral_const_mul,mutualEnergy]

/-- PROOF-DRAFT: actual finite-mixture Borel energy, with integrability derived. -/
theorem energy_rho (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (hc : ∀ i,0≤c i) :
    (∫ x,∫ y,Real.log |x-y| ∂rho a b c ∂rho a b c)=quadratic (K a b) c := by
  rw [integral_rho a b c hc _ (fun i=>potential_rho_integrable a b c hab hc (hab i))]
  unfold quadratic bilinear
  apply Finset.sum_congr rfl
  intro i _
  rw [mutualEnergy_rho a b c hab hc (hab i),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [kernel_eq a b hab]
  ring

/-- PROOF-DRAFT: the admissible pointwise majorant is averaged only against each trial atom. -/
theorem trial_row (a b c : ι→ℝ) (hab : ∀ i,a i<b i) (hc : ∀ i,0≤c i)
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂rho a b c)-U16.V6 t≤H)
    (j : Fin 15) :
    2*(∑ i,c i*mutualEnergy 0 (U11.width j) (a i) (b i))-U11.W (U11.width j)≤H := by
  have hp := potential_rho_integrable a b c hab hc (U20.width_pos j)
  have hv := U20.V6_integrable (U20.width_pos j)
  have hm : (∫ t,2*(∫ y,Real.log |t-y| ∂rho a b c)-U16.V6 t
      ∂arcsineMeasure 0 (U11.width j))≤∫ t,H ∂arcsineMeasure 0 (U11.width j) := by
    apply integral_mono_ae ((hp.const_mul 2).sub hv) (integrable_const H)
    filter_upwards [arcsineMeasure_ae_mem (U20.width_pos j).le] with t ht
    exact hfield t ht.1
  rw [integral_sub (hp.const_mul 2) hv,integral_const_mul,
    mutualEnergy_rho a b c hab hc (U20.width_pos j),U20.field_integral (U20.width_pos j)] at hm
  simpa only [integral_const,probReal_univ,one_smul,U20.W_eq_U11] using hm

end U25
#print axioms U25.energy_rho
#print axioms U25.rho_pair_integrable
#print axioms U25.trial_row
