import BorelAEField
import RealPositiveLog

/-! E234/U39, Codex driver for Ryan, lane U. Every mathematical declaration
has status PROOF-DRAFT pending the gate and human statement comparison.
This composes the explicit extended-potential convention with the actual
Borel witness/package inequalities. Overall E201/I4 remain CONJECTURE. -/
noncomputable section
namespace U39
open MeasureTheory Set Real Mathathon.P108

/-- PROOF-DRAFT: the positive part is finite, so the defined potential has no +infinity value. -/
theorem extendedPotential_ne_top (rho : Measure ℝ) [IsFiniteMeasure rho]
    {R : ℝ} (hR : ∀ᵐ x ∂rho, |x|≤R) (t : ℝ) :
    U37.extendedPotential rho t ≠ ⊤ := by
  have ha := U38.logPlus_lintegral_ne_top rho hR t
  unfold U37.extendedPotential
  rw [←EReal.coe_ennreal_toReal ha]
  by_cases hb : (∫⁻ y,U37.logMinus t y ∂rho)=⊤
  · rw [hb]
    simp
  · rw [←EReal.coe_ennreal_toReal hb,←EReal.coe_sub]
    exact EReal.coe_ne_top _

/-- PROOF-DRAFT: uniform actual trial comparison from the explicit extended field premise. -/
theorem uniform_witness_lower_extended (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho, |x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho))
    (H : ℝ) (hfield : ∀ t,0≤t→
      (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤(H:EReal)) :
    U20.integralWitness≤U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂rho ∂rho)+U11.C6 :=
  U36.uniform_witness_lower_on_integrable rho hR hmass hlog H
    (U37.real_majorant_of_extendedPotential_le (mu:=rho) U16.V6 H hfield)

/-- PROOF-DRAFT: the strict energy floor under the explicit extended field premise. -/
theorem energy_floor_extended (rho : Measure ℝ) [IsFiniteMeasure rho]
    [NullSingletonClass rho] {R : ℝ} (hR : ∀ᵐ x ∂rho, |x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho))
    (H : ℝ) (hfield : ∀ t,0≤t→
      (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤(H:EReal)) :
    (-139:ℝ)/100<U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂rho ∂rho)+U11.C6 :=
  U20.integralWitness_gt.trans_le
    (uniform_witness_lower_extended rho hR hmass hlog H hfield)

/-- PROOF-DRAFT: actual-measure package margin for every real cutoff >=40. -/
theorem package_margin_extended (M : ℝ) (hM : 40≤M)
    (rho : Measure ℝ) [IsFiniteMeasure rho] [NullSingletonClass rho]
    {R : ℝ} (hR : ∀ᵐ x ∂rho, |x|≤R)
    (hmass : rho univ=ENNReal.ofReal U11.lam)
    (hlog : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (rho.prod rho))
    (H : ℝ) (hfield : ∀ t,0≤t→
      (2:EReal)*U37.extendedPotential rho t-(U16.V6 t:EReal)≤(H:EReal)) :
    (9:ℝ)/10<thetaPkg 7 6 (3/40) M
      (U11.lam*H-(∫ x,∫ y,Real.log |x-y| ∂rho ∂rho)+U11.C6) :=
  U36.package_margin_on_integrable M hM rho hR hmass hlog H
    (U37.real_majorant_of_extendedPotential_le (mu:=rho) U16.V6 H hfield)

end U39
#print axioms U39.extendedPotential_ne_top
#print axioms U39.uniform_witness_lower_extended
#print axioms U39.energy_floor_extended
#print axioms U39.package_margin_extended
