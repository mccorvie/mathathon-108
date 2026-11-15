import LocalMass
import BorelWeakDuality

/-!
E227/U32, Codex (GPT-6), lane U. Every new mathematical declaration has status PROOF-DRAFT.
Uniform explicit-trial lower bound for arbitrary bounded finite Borel comparison measures.
Frozen E225/E226/E215 support is reused with attribution; ArcMeasure has the documented L API proof patch.
Whole E201 remains CONJECTURE. No infimum, valuation, or irrationality conclusion is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace U32
open MeasureTheory Set Real

/-- PROOF-DRAFT: product diagonal nullness follows from atomlessness of the second measure. -/
theorem product_ae_ne (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂μ.prod ν,p.1≠p.2 := by
  have hmeas : MeasurableSet {p : ℝ×ℝ | p.1≠p.2} := by
    change MeasurableSet ({p : ℝ×ℝ | p.1=p.2}ᶜ)
    exact (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [] with x
  rw [ae_iff]
  have hs : {y : ℝ | ¬x≠y}={x} := by ext y;simp [eq_comm]
  rw [hs,measure_singleton]

/-- PROOF-DRAFT: uniform witness lower bound, before any strict numerical floor is taken. -/
theorem uniform_witness_lower (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    U20.integralWitness≤U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 := by
  haveI : NullSingletonClass U20.sigma := U30.sigma_noAtoms
  have hm : U20.sigma univ=ρ univ := U20.sigma_mass.trans hmass.symm
  have hs : U20.sigma.real univ=U11.lam := by
    change (U20.sigma univ).toReal=U11.lam
    rw [U20.sigma_mass,ENNReal.toReal_ofReal (by norm_num [U11.lam])]
  have hf : ∀ᵐ x ∂U20.sigma,2*(∫ y,Real.log |x-y| ∂ρ)-U16.V6 x≤H := by
    filter_upwards [U30.sigma_ae_nonnegative] with x hx
    exact hfield x hx
  have hd := U31.borel_weak_duality U20.sigma ρ hm
    U20.sigma_pair_integrable (U30.sigma_prod_mu_integrable ρ hR) hlog
    (product_ae_ne U20.sigma U20.sigma) (product_ae_ne U20.sigma ρ) (product_ae_ne ρ ρ)
    U16.V6 U20.sigma_field_integrable H hf
  rw [hs] at hd
  unfold U20.integralWitness U20.energy
  linarith

/-- PROOF-DRAFT: every comparison satisfying the displayed hypotheses has the strict floor. -/
theorem energy_floor (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (-139:ℝ)/100<U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 :=
  U20.integralWitness_gt.trans_le (uniform_witness_lower ρ hR hmass hlog H hfield)

/-- PROOF-DRAFT: a local square-root mass bound can replace the atomlessness assumption. -/
theorem uniform_witness_lower_of_sqrt_bound (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (C : ℝ) (hsmall : ∀ x e : ℝ,0<e→
      ρ (Icc (x-e) (x+e))≤ENNReal.ofReal (C*Real.sqrt e))
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    U20.integralWitness≤U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 := by
  haveI := U30.noAtoms_of_local_sqrt_bound ρ C hsmall
  exact uniform_witness_lower ρ hR hmass hlog H hfield

/-- PROOF-DRAFT: strict numerical consequence under the local square-root mass bound. -/
theorem energy_floor_of_sqrt_bound (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (C : ℝ) (hsmall : ∀ x e : ℝ,0<e→
      ρ (Icc (x-e) (x+e))≤ENNReal.ofReal (C*Real.sqrt e))
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (-139:ℝ)/100<U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 :=
  U20.integralWitness_gt.trans_le
    (uniform_witness_lower_of_sqrt_bound ρ C hsmall hR hmass hlog H hfield)

end U32
#print axioms U32.product_ae_ne
#print axioms U32.uniform_witness_lower
#print axioms U32.energy_floor
#print axioms U32.uniform_witness_lower_of_sqrt_bound
#print axioms U32.energy_floor_of_sqrt_bound
