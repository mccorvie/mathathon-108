import ExtendedFieldMargin
/-! E237/U42, Codex driver for Ryan, lane U, event work.
Every mathematical declaration has status PROOF-DRAFT pending the local gate
and human statement comparison. Explicit Borel comparison class only;
no equality with the paper's admissibility class or E13 is asserted.
Overall E201/I4 remain CONJECTURE. -/
set_option autoImplicit false
noncomputable section
namespace U42
open MeasureTheory Set Real

/-- PROOF-DRAFT: actual extended field values on the nonnegative real halfline. -/
def fieldValues (rho : Measure ℝ) : Set EReal :=
  (fun t : ℝ => (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)) '' Ici 0

/-- PROOF-DRAFT: complete-order supremum; +infinity is allowed. -/
def fieldSup (rho : Measure ℝ) : EReal := sSup (fieldValues rho)

/-- PROOF-DRAFT: the actual real nested logarithmic self-energy. -/
def selfEnergy (rho : Measure ℝ) : ℝ :=
  ∫ x,∫ y,Real.log |x-y| ∂rho ∂rho

/-- PROOF-DRAFT: the optimized extended-real cost for the fixed nu=6 package. -/
def optimizedEnergy (rho : Measure ℝ) : EReal :=
  (U11.lam:EReal)*fieldSup rho-(selfEnergy rho:EReal)+(U11.C6:EReal)

/-- PROOF-DRAFT: exact explicit comparison class, without a supplied field majorant. -/
def ComparisonClass (rho : Measure ℝ) : Prop :=
  IsFiniteMeasure rho ∧ NullSingletonClass rho ∧
    (∃ R : ℝ,∀ᵐ x ∂rho,|x|≤R) ∧
    rho univ=ENNReal.ofReal U11.lam ∧
    Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)

/-- PROOF-DRAFT: every actual field value is below its complete supremum. -/
lemma field_le_sup (rho : Measure ℝ) (t : ℝ) (ht : 0≤t) :
    (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal) ≤ fieldSup rho :=
  le_sSup ⟨t,ht,rfl⟩

/-- PROOF-DRAFT: arbitrary real upper bounds majorize the actual supremum. -/
lemma fieldSup_le (rho : Measure ℝ) (H : ℝ)
    (h : ∀ t,0≤t→(2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤(H:EReal)) :
    fieldSup rho≤(H:EReal) := by
  apply sSup_le
  rintro _ ⟨t,ht,rfl⟩
  exact h t ht

/-- PROOF-DRAFT: the actual field supremum cannot be negative infinity in the explicit class. -/
theorem fieldSup_ne_bot (rho : Measure ℝ) [IsFiniteMeasure rho] [NullSingletonClass rho]
    {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)) :
    fieldSup rho≠⊥ := by
  intro hbot
  let H : ℝ := (selfEnergy rho-U11.C6+U20.integralWitness-1)/U11.lam
  have hf : ∀ t,0≤t→(2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤(H:EReal) := by
    intro t ht
    exact (field_le_sup rho t ht).trans (by rw [hbot];exact bot_le)
  have hw := U39.uniform_witness_lower_extended rho hR hmass hlog H hf
  change U20.integralWitness≤U11.lam*H-selfEnergy rho+U11.C6 at hw
  have he : U11.lam*H-selfEnergy rho+U11.C6=U20.integralWitness-1 := by
    dsimp [H]
    norm_num [U11.lam]
    ring
  rw [he] at hw
  linarith

/-- PROOF-DRAFT: uniform trial-witness bound for the actual optimized extended-real cost. -/
theorem uniform_witness_lower_optimized (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)) :
    (U20.integralWitness:EReal)≤optimizedEnergy rho := by
  by_cases htop : fieldSup rho=⊤
  · have hl : 0<U11.lam := by norm_num [U11.lam]
    simp [optimizedEnergy,htop,EReal.coe_mul_top_of_pos hl]
  · have hbot := fieldSup_ne_bot rho hR hmass hlog
    have hreal := EReal.coe_toReal htop hbot
    have hf : ∀ t,0≤t→(2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤
        ((fieldSup rho).toReal:EReal) := by
      intro t ht
      rw [hreal]
      exact field_le_sup rho t ht
    have hw := U39.uniform_witness_lower_extended rho hR hmass hlog (fieldSup rho).toReal hf
    have hw' := EReal.coe_le_coe hw
    change (U20.integralWitness:EReal)≤
      (U11.lam:EReal)*((fieldSup rho).toReal:EReal)-(selfEnergy rho:EReal)+(U11.C6:EReal) at hw'
    rw [hreal] at hw'
    exact hw'

/-- PROOF-DRAFT: strict numerical floor with no supplied H or supremum-finiteness premise. -/
theorem optimized_energy_floor (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)) :
    (((-139:ℝ)/100):EReal)<optimizedEnergy rho :=
  (EReal.coe_lt_coe_iff.mpr U20.integralWitness_gt).trans_le
    (uniform_witness_lower_optimized rho hR hmass hlog)

/-- PROOF-DRAFT: real floor at the actual finite field supremum; no supplied H. -/
theorem optimized_energy_floor_real (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho))
    (hfinite : fieldSup rho≠⊤) :
    (-139:ℝ)/100<U11.lam*(fieldSup rho).toReal-selfEnergy rho+U11.C6 := by
  apply U39.energy_floor_extended rho hR hmass hlog
  intro t ht
  exact (field_le_sup rho t ht).trans (EReal.le_coe_toReal hfinite)

/-- PROOF-DRAFT: all-real-cutoff package margin at the actual finite field supremum. -/
theorem package_margin_at_finite_sup (M : ℝ) (hM : 40≤M)
    (rho : Measure ℝ) [IsFiniteMeasure rho] [NullSingletonClass rho]
    {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho))
    (hfinite : fieldSup rho≠⊤) :
    (9:ℝ)/10<Mathathon.P108.thetaPkg 7 6 (3/40) M
      (U11.lam*(fieldSup rho).toReal-selfEnergy rho+U11.C6) := by
  apply U39.package_margin_extended M hM rho hR hmass hlog
  intro t ht
  exact (field_le_sup rho t ht).trans (EReal.le_coe_toReal hfinite)

/-- PROOF-DRAFT: optimized costs of exactly the displayed comparison class. -/
def objectiveValues : Set EReal := {z|∃ rho : Measure ℝ,ComparisonClass rho ∧ z=optimizedEnergy rho}

/-- PROOF-DRAFT: the actual square15 trial belongs to the displayed comparison class. -/
theorem sigma_comparison_class : ComparisonClass U20.sigma := by
  let R : ℝ := ∑ j : Fin 15,|U11.width j|
  have hb : ∀ᵐ x ∂U20.sigma,|x|≤R := by
    rw [U20.sigma,←Measure.sum_fintype,Measure.ae_sum_iff]
    intro j
    apply Measure.ae_smul_measure
    change ∀ᵐ x ∂Mathathon.P108.ArcMeasure.arcsineMeasure 0 (U11.width j),|x|≤R
    filter_upwards [Mathathon.P108.ArcMeasure.arcsineMeasure_ae_mem (U20.width_pos j).le] with x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2.trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _=>abs_nonneg (U11.width i)) (Finset.mem_univ j)))
  exact ⟨inferInstance,U30.sigma_noAtoms,⟨R,hb⟩,U20.sigma_mass,U20.sigma_pair_integrable⟩

/-- PROOF-DRAFT: the optimized objective set is nonempty, witnessed by the actual trial. -/
theorem objectiveValues_nonempty : objectiveValues.Nonempty :=
  ⟨optimizedEnergy U20.sigma,U20.sigma,sigma_comparison_class,rfl⟩

/-- PROOF-DRAFT: complete-order infimum of those explicit optimized costs. -/
def optimalEnergy : EReal := sInf objectiveValues

/-- PROOF-DRAFT: the same uniform witness bounds the infimum, even if the explicit class is empty. -/
theorem uniform_witness_lower_infimum : (U20.integralWitness:EReal)≤optimalEnergy := by
  apply le_sInf
  rintro _ ⟨rho,⟨hfinite,hatom,⟨R,hR⟩,hmass,hlog⟩,rfl⟩
  letI : IsFiniteMeasure rho := hfinite
  letI : NullSingletonClass rho := hatom
  exact uniform_witness_lower_optimized rho hR hmass hlog

/-- PROOF-DRAFT: strict infimum floor for this exact Borel class, with no nonemptiness or H premise. -/
theorem optimal_energy_floor : (((-139:ℝ)/100):EReal)<optimalEnergy :=
  (EReal.coe_lt_coe_iff.mpr U20.integralWitness_gt).trans_le uniform_witness_lower_infimum

end U42
#print axioms U42.fieldSup_ne_bot
#print axioms U42.uniform_witness_lower_optimized
#print axioms U42.optimized_energy_floor
#print axioms U42.uniform_witness_lower_infimum
#print axioms U42.optimal_energy_floor
#print axioms U42.optimized_energy_floor_real
#print axioms U42.package_margin_at_finite_sup
#print axioms U42.sigma_comparison_class
#print axioms U42.objectiveValues_nonempty
