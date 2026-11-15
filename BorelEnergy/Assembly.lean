import BorelEnergy.Parameter

/-! E223/U28, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
Finite-measure assembly of the preceding Gaussian/Fubini/DCT stages. Whole E201 remains CONJECTURE. -/
noncomputable section
namespace U28
open MeasureTheory Set Real Filter Topology

lemma parameter_inner (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : ℝ} (hs : 0<s) :
    (∫ p : ℝ×ℝ,(Real.exp (-s)-gauss s p.1 p.2)/s ∂μ.prod ν)=
      (Real.exp (-s)*(μ.real univ)*(ν.real univ)-gaussianPair μ ν s)/s := by
  rw [integral_div,integral_sub (integrable_const _) (gauss_pair_integrable μ ν hs.le),integral_const]
  have hm : (μ.prod ν).real univ=μ.real univ*ν.real univ := by
    change ((μ.prod ν) univ).toReal=(μ univ).toReal*(ν univ).toReal
    rw [show (univ : Set (ℝ×ℝ))=(univ : Set ℝ)×ˢ(univ : Set ℝ) by ext p;simp,
      Measure.prod_prod,ENNReal.toReal_mul]
  rw [hm]
  unfold gaussianPair
  simp only [smul_eq_mul]
  ring

lemma truncated_difference_nonpos (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ=ν univ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p : ℝ×ℝ,Apery.Ltr a b |p.1-p.2| ∂μ.prod μ)+
      (∫ p : ℝ×ℝ,Apery.Ltr a b |p.1-p.2| ∂ν.prod ν)-
      2*(∫ p : ℝ×ℝ,Apery.Ltr a b |p.1-p.2| ∂μ.prod ν)≤0 := by
  let ψ (κ η : Measure ℝ) (s : ℝ) := ∫ p : ℝ×ℝ,(Real.exp (-s)-gauss s p.1 p.2)/s ∂κ.prod η
  have hμμ := parameter_integrable μ μ ha hab
  have hνν := parameter_integrable ν ν ha hab
  have hμν := parameter_integrable μ ν ha hab
  have headd := intervalIntegral.integral_add hμμ hνν
  have hesub := intervalIntegral.integral_sub (hμμ.add hνν) (hμν.const_mul 2)
  try simp only [Pi.add_apply] at headd hesub
  have hneg : (∫ s in a..b,ψ μ μ s+ψ ν ν s-2*(ψ μ ν s))≤0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsIoc
    have hs : s∈Icc a b := Ioc_subset_Icc_self hsIoc
    have hs0 : 0<s := ha.trans_le hs.1
    have hm : μ.real univ=ν.real univ := congrArg ENNReal.toReal hmass
    have he : ψ μ μ s+ψ ν ν s-2*(ψ μ ν s)=
        -(gaussianPair μ μ s+gaussianPair ν ν s-2*gaussianPair μ ν s)/s := by
      dsimp [ψ]
      rw [parameter_inner μ μ hs0,parameter_inner ν ν hs0,parameter_inner μ ν hs0,hm]
      ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [gaussian_difference_nonneg μ ν hs0]) hs0.le
  have hvalue := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0:ℝ)≤1/2) hneg
  dsimp [ψ] at hvalue
  rw [hesub,headd,intervalIntegral.integral_const_mul] at hvalue
  rw [truncated_swap μ μ ha hab,truncated_swap ν ν ha hab,truncated_swap μ ν ha hab]
  linarith

/-- PROOF-DRAFT: equal-mass logarithmic energy nonpositivity, with explicit diagonal nullness. -/
theorem log_difference_nonpos (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ=ν univ)
    (hμμ : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod μ))
    (hμν : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod ν))
    (hνν : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ν.prod ν))
    (dμμ : ∀ᵐ p ∂μ.prod μ,p.1≠p.2) (dμν : ∀ᵐ p ∂μ.prod ν,p.1≠p.2)
    (dνν : ∀ᵐ p ∂ν.prod ν,p.1≠p.2) :
    logPair μ μ+logPair ν ν-2*logPair μ ν≤0 := by
  have hlim := (((truncatedPair_tendsto μ μ hμμ dμμ).add
    (truncatedPair_tendsto ν ν hνν dνν)).sub
    ((truncatedPair_tendsto μ ν hμν dμν).const_mul 2))
  apply le_of_tendsto' hlim
  intro n
  exact truncated_difference_nonpos μ ν hmass (by positivity) (by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)]
    nlinarith)

/-- PROOF-DRAFT: literal nested Borel-integral version. -/
theorem nested_log_difference_nonpos (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ=ν univ)
    (hμμ : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod μ))
    (hμν : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (μ.prod ν))
    (hνν : Integrable (fun p : ℝ×ℝ=>Real.log |p.1-p.2|) (ν.prod ν))
    (dμμ : ∀ᵐ p ∂μ.prod μ,p.1≠p.2) (dμν : ∀ᵐ p ∂μ.prod ν,p.1≠p.2)
    (dνν : ∀ᵐ p ∂ν.prod ν,p.1≠p.2) :
    (∫ x,∫ y,Real.log |x-y| ∂μ ∂μ)+(∫ x,∫ y,Real.log |x-y| ∂ν ∂ν)-
      2*(∫ x,∫ y,Real.log |x-y| ∂ν ∂μ)≤0 := by
  have h := log_difference_nonpos μ ν hmass hμμ hμν hνν dμμ dμν dνν
  rw [logPair_eq_nested μ μ hμμ,logPair_eq_nested ν ν hνν,logPair_eq_nested μ ν hμν] at h
  exact h

end U28
#print axioms U28.log_difference_nonpos

#print axioms U28.nested_log_difference_nonpos
