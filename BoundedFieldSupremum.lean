import PositiveEnvelope
import FieldCoercivity
/-! E239/U44, Codex driver for Ryan. All mathematical declarations have status
PROOF-DRAFT pending gate and human comparison. The actual finite fieldSup is
derived, not assumed. Overall E201/I4 remain CONJECTURE. -/
set_option autoImplicit false
noncomputable section
namespace U44
open MeasureTheory Set Real

/-- PROOF-DRAFT: explicit global majorant for the actual extended field. -/
theorem field_explicit_majorant (rho : Measure ℝ) {R : ℝ}
    (hR : ∀ᵐ y ∂rho,|y|≤R) (hmass : rho univ=ENNReal.ofReal U11.lam)
    {t : ℝ} (ht : 0≤t) :
    (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤
      ((4*U11.lam*Real.sqrt (max R 0)+3:ℝ):EReal) := by
  have hs : Real.sqrt (t+max R 0)≤Real.sqrt t+Real.sqrt (max R 0) := by
    apply (Real.sqrt_le_left (by positivity : 0≤Real.sqrt t+Real.sqrt (max R 0))).2
    nlinarith [Real.sq_sqrt ht,Real.sq_sqrt (le_max_right R 0),
      mul_nonneg (Real.sqrt_nonneg t) (Real.sqrt_nonneg (max R 0))]
  have hv := U43.V6_coercive ht
  have hb : 4*U11.lam*Real.sqrt (t+max R 0)-U16.V6 t≤
      4*U11.lam*Real.sqrt (max R 0)+3 := by
    norm_num [U11.lam] at ⊢
    nlinarith [Real.sqrt_nonneg t]
  have hp := extendedPotential_sqrt_upper rho hR hmass ht
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:EReal)≤2)
  have hf := EReal.sub_le_sub hm (le_refl (U16.V6 t:EReal))
  calc
    (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤
        (2:EReal)*((2*U11.lam*Real.sqrt (t+max R 0):ℝ):EReal)-(U16.V6 t:EReal) := hf
    _=((4*U11.lam*Real.sqrt (t+max R 0)-U16.V6 t:ℝ):EReal) := by
      change ((2*(2*U11.lam*Real.sqrt (t+max R 0))-U16.V6 t:ℝ):EReal)=_
      congr 1
      ring
    _≤_ := EReal.coe_le_coe hb

/-- PROOF-DRAFT: the actual field supremum has a finite explicit real upper bound. -/
theorem fieldSup_ne_top (rho : Measure ℝ) {R : ℝ}
    (hR : ∀ᵐ y ∂rho,|y|≤R) (hmass : rho univ=ENNReal.ofReal U11.lam) :
    U42.fieldSup rho≠⊤ := by
  apply ne_top_of_le_ne_top (EReal.coe_ne_top (4*U11.lam*Real.sqrt (max R 0)+3))
  exact U42.fieldSup_le rho _ (fun _ ht=>field_explicit_majorant rho hR hmass ht)

/-- PROOF-DRAFT: real energy floor at the actual supremum, without supplied H/finiteness premise. -/
theorem optimized_energy_floor_real (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)) :
    (-139:ℝ)/100<U11.lam*(U42.fieldSup rho).toReal-U42.selfEnergy rho+U11.C6 :=
  U42.optimized_energy_floor_real rho hR hmass hlog (fieldSup_ne_top rho hR hmass)

/-- PROOF-DRAFT: actual optimized package margin for every real cutoff, no H/finiteness premise. -/
theorem package_margin_optimized (M : ℝ) (hM : 40≤M)
    (rho : Measure ℝ) [IsFiniteMeasure rho] [NullSingletonClass rho]
    {R : ℝ} (hR : ∀ᵐ x ∂rho,|x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho)) :
    (9:ℝ)/10<Mathathon.P108.thetaPkg 7 6 (3/40) M
      (U11.lam*(U42.fieldSup rho).toReal-U42.selfEnergy rho+U11.C6) :=
  U42.package_margin_at_finite_sup M hM rho hR hmass hlog (fieldSup_ne_top rho hR hmass)

/-- PROOF-DRAFT: each optimized value of the explicit comparison class is finite. -/
lemma optimizedEnergy_finite (rho : Measure ℝ) (hc : U42.ComparisonClass rho) :
    U42.optimizedEnergy rho≠⊤ ∧ U42.optimizedEnergy rho≠⊥ := by
  rcases hc with ⟨hfinite,hatom,⟨R,hR⟩,hmass,hlog⟩
  letI : IsFiniteMeasure rho := hfinite
  letI : NullSingletonClass rho := hatom
  have hS := EReal.coe_toReal (fieldSup_ne_top rho hR hmass)
    (U42.fieldSup_ne_bot rho hR hmass hlog)
  have he : U42.optimizedEnergy rho=
      ((U11.lam*(U42.fieldSup rho).toReal-U42.selfEnergy rho+U11.C6:ℝ):EReal) := by
    unfold U42.optimizedEnergy
    rw [←hS]
    rfl
  rw [he]
  exact ⟨EReal.coe_ne_top _,EReal.coe_ne_bot _⟩

/-- PROOF-DRAFT: the explicit optimized infimum is finite above, witnessed by actual sigma. -/
theorem optimalEnergy_ne_top : U42.optimalEnergy≠⊤ := by
  have hu : U42.optimalEnergy≤U42.optimizedEnergy U20.sigma :=
    sInf_le ⟨U20.sigma,U42.sigma_comparison_class,rfl⟩
  exact ne_top_of_le_ne_top (optimizedEnergy_finite U20.sigma U42.sigma_comparison_class).1 hu

/-- PROOF-DRAFT: its uniform witness lower bound also excludes negative infinity. -/
lemma optimalEnergy_ne_bot : U42.optimalEnergy≠⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot U20.integralWitness) U42.uniform_witness_lower_infimum

/-- PROOF-DRAFT: real strict infimum floor for the precisely defined nonempty Borel class. -/
theorem optimal_energy_floor_real : (-139:ℝ)/100<(U42.optimalEnergy).toReal := by
  have h := U42.optimal_energy_floor
  rw [←EReal.coe_toReal optimalEnergy_ne_top optimalEnergy_ne_bot] at h
  exact EReal.coe_lt_coe_iff.mp h

end U44
#print axioms U44.field_explicit_majorant
#print axioms U44.fieldSup_ne_top
#print axioms U44.optimized_energy_floor_real
#print axioms U44.package_margin_optimized
#print axioms U44.optimizedEnergy_finite
#print axioms U44.optimalEnergy_ne_top
#print axioms U44.optimalEnergy_ne_bot
#print axioms U44.optimal_energy_floor_real
