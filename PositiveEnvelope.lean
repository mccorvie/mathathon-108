import ExtendedOptimization
/-! E239/U44, Codex driver for Ryan, lane U. All mathematical declarations
have status PROOF-DRAFT pending the repository gate and human comparison.
Actual positive-log envelope; no negative-part finiteness asserted.
Overall E201/I4 remain CONJECTURE. -/
set_option autoImplicit false
noncomputable section
namespace U44
open MeasureTheory Set Real

/-- PROOF-DRAFT: a deliberately coarse sublinear logarithmic bound, valid also at zero. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0≤x) : Real.log x≤2*Real.sqrt x := by
  have h := Real.log_le_self (Real.sqrt_nonneg x)
  rw [Real.log_sqrt hx] at h
  linarith

/-- PROOF-DRAFT: pointwise envelope for the canonical exact nonnegative logarithmic kernel. -/
lemma logPlus_le_sqrt_envelope {R t y : ℝ} (ht : 0≤t) (hy : |y|≤R) :
    U37.logPlus t y≤ENNReal.ofReal (2*Real.sqrt (t+max R 0)) := by
  apply ENNReal.ofReal_le_ofReal
  have hd : |t-y|≤t+max R 0 := by
    calc
      |t-y|≤|t|+|y| := abs_sub t y
      _≤t+max R 0 := by
        rw [abs_of_nonneg ht]
        exact add_le_add le_rfl (hy.trans (le_max_left R 0))
  exact (log_le_two_sqrt (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) (by norm_num))

/-- PROOF-DRAFT: actual positive lower integral is bounded by a finite square-root envelope. -/
theorem positive_lintegral_sqrt_upper (rho : Measure ℝ) {R : ℝ}
    (hR : ∀ᵐ y ∂rho,|y|≤R) (hmass : rho univ=ENNReal.ofReal U11.lam)
    {t : ℝ} (ht : 0≤t) :
    (∫⁻ y,U37.logPlus t y ∂rho)≤
      ENNReal.ofReal (2*U11.lam*Real.sqrt (t+max R 0)) := by
  calc
    (∫⁻ y,U37.logPlus t y ∂rho)≤
        ∫⁻ _y,ENNReal.ofReal (2*Real.sqrt (t+max R 0)) ∂rho := by
      apply lintegral_mono_ae
      filter_upwards [hR] with y hy
      exact logPlus_le_sqrt_envelope ht hy
    _=ENNReal.ofReal (2*Real.sqrt (t+max R 0))*rho univ := lintegral_const _
    _=ENNReal.ofReal (2*U11.lam*Real.sqrt (t+max R 0)) := by
      rw [hmass,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- PROOF-DRAFT: dropping the nonnegative negative-part integral gives a valid upper bound. -/
lemma extendedPotential_le_positive (rho : Measure ℝ) (t : ℝ) :
    U37.extendedPotential rho t≤
      ENNReal.toEReal (∫⁻ y,U37.logPlus t y ∂rho) := by
  unfold U37.extendedPotential
  calc
    _≤ENNReal.toEReal (∫⁻ y,U37.logPlus t y ∂rho)+0 :=
      add_le_add le_rfl (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _))
    _=_ := add_zero _

/-- PROOF-DRAFT: actual extended potential upper bound, allowing atoms/infinite negative part. -/
theorem extendedPotential_sqrt_upper (rho : Measure ℝ) {R : ℝ}
    (hR : ∀ᵐ y ∂rho,|y|≤R) (hmass : rho univ=ENNReal.ofReal U11.lam)
    {t : ℝ} (ht : 0≤t) :
    U37.extendedPotential rho t≤
      ((2*U11.lam*Real.sqrt (t+max R 0):ℝ):EReal) := by
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    (positive_lintegral_sqrt_upper rho hR hmass ht)
  have hn : 0≤2*U11.lam*Real.sqrt (t+max R 0) := by
    have hl : 0≤U11.lam := by norm_num [U11.lam]
    positivity
  rw [EReal.coe_ennreal_ofReal,max_eq_left hn] at h
  exact (extendedPotential_le_positive rho t).trans h

end U44
#print axioms U44.positive_lintegral_sqrt_upper
#print axioms U44.extendedPotential_sqrt_upper
