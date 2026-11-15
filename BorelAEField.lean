import BorelPackageMargin

/-!
E231/U36, Codex (GPT-6), lane U. Every new mathematical declaration has status PROOF-DRAFT.
The field input is sigma-a.e. pointwise, or pointwise only when the comparison-log section is integrable.
No classical extended-potential identity is asserted. Whole E201/I4 remain CONJECTURE.
-/
set_option autoImplicit false
noncomputable section
namespace U36
open MeasureTheory Set Real Mathathon.P108

/-- PROOF-DRAFT: mixed product integrability discharges the integrability qualification sigma-a.e. -/
theorem field_ae_of_integrability_qualified (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (H : ℝ) (hfieldInt : ∀ t,0≤t→
      Integrable (fun y=>Real.log |t-y|) ρ→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    ∀ᵐ t ∂U20.sigma,2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H := by
  have hi := (U30.sigma_prod_mu_integrable ρ hR).prod_right_ae
  filter_upwards [U30.sigma_ae_nonnegative,hi] with t ht hit
  exact hfieldInt t ht hit

/-- PROOF-DRAFT: uniform actual witness bound under a sigma-a.e. pointwise majorant. -/
theorem uniform_witness_lower_ae (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldAE : ∀ᵐ t ∂U20.sigma,2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    U20.integralWitness≤U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 := by
  haveI : NullSingletonClass U20.sigma := U30.sigma_noAtoms
  have hm : U20.sigma univ=ρ univ := U20.sigma_mass.trans hmass.symm
  have hs : U20.sigma.real univ=U11.lam := by
    change (U20.sigma univ).toReal=U11.lam
    rw [U20.sigma_mass,ENNReal.toReal_ofReal (by norm_num [U11.lam])]
  have hd := U31.borel_weak_duality U20.sigma ρ hm
    U20.sigma_pair_integrable (U30.sigma_prod_mu_integrable ρ hR) hlog
    (U32.product_ae_ne U20.sigma U20.sigma) (U32.product_ae_ne U20.sigma ρ) (U32.product_ae_ne ρ ρ)
    U16.V6 U20.sigma_field_integrable H hfieldAE
  rw [hs] at hd
  unfold U20.integralWitness U20.energy
  linarith

/-- PROOF-DRAFT: uniform bound with a majorant required only at integrable nonnegative sections. -/
theorem uniform_witness_lower_on_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldInt : ∀ t,0≤t→
      Integrable (fun y=>Real.log |t-y|) ρ→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    U20.integralWitness≤U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 :=
  uniform_witness_lower_ae ρ hR hmass hlog H
    (field_ae_of_integrability_qualified ρ hR H hfieldInt)

/-- PROOF-DRAFT: strict numerical floor under a sigma-a.e. pointwise field bound. -/
theorem energy_floor_ae (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldAE : ∀ᵐ t ∂U20.sigma,2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (-139:ℝ)/100<U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 :=
  U20.integralWitness_gt.trans_le (uniform_witness_lower_ae ρ hR hmass hlog H hfieldAE)

/-- PROOF-DRAFT: strict numerical floor from the integrability-qualified pointwise majorant. -/
theorem energy_floor_on_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldInt : ∀ t,0≤t→
      Integrable (fun y=>Real.log |t-y|) ρ→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (-139:ℝ)/100<U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6 :=
  U20.integralWitness_gt.trans_le
    (uniform_witness_lower_on_integrable ρ hR hmass hlog H hfieldInt)

/-- PROOF-DRAFT: actual all-real-cutoff package margin under the core sigma-a.e. premise. -/
theorem package_margin_ae (M : ℝ) (hM : 40≤M)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldAE : ∀ᵐ t ∂U20.sigma,2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (9:ℝ)/10<thetaPkg 7 6 (3/40) M
      (U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6) :=
  U18.theta_allM_gt M _ hM (energy_floor_ae ρ hR hmass hlog H hfieldAE)

/-- PROOF-DRAFT: actual all-real-cutoff margin from the integrability-qualified pointwise premise. -/
theorem package_margin_on_integrable (M : ℝ) (hM : 40≤M)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] [NullSingletonClass ρ]
    {R : ℝ} (hR : ∀ᵐ x ∂ρ, |x|≤R)
    (hmass : ρ univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ρ.prod ρ))
    (H : ℝ) (hfieldInt : ∀ t,0≤t→
      Integrable (fun y=>Real.log |t-y|) ρ→2*(∫ y,Real.log |t-y| ∂ρ)-U16.V6 t≤H) :
    (9:ℝ)/10<thetaPkg 7 6 (3/40) M
      (U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂ρ ∂ρ)+U11.C6) :=
  U18.theta_allM_gt M _ hM (energy_floor_on_integrable ρ hR hmass hlog H hfieldInt)

end U36
#print axioms U36.uniform_witness_lower_ae
#print axioms U36.uniform_witness_lower_on_integrable
#print axioms U36.energy_floor_ae
#print axioms U36.energy_floor_on_integrable
#print axioms U36.package_margin_ae
#print axioms U36.package_margin_on_integrable
