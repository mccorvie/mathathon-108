import Interface

/-!
Codex gpt-6.1-sol, lane C finite-to-leading worker, 2026-11-14.
PROOF-DRAFT until the repository's --final gate passes.
This is a re-derivation of Fauzan's theorem reusing Firsching's formalisation,
mo271/Zeta5@be1c0d82 (Apache-2.0; Comparator metadata Paul-Lez).
The lower-order passage adapts lane B's E431 RealLimit.lean:21-95,
itself adapting upstream Apery/RealBound.lean:88-109. Prior team
Deicyde@be55b3a44213addfd0bb6b7f1d30c6c8998a68e8 PositiveIntegral.lean:174,446
and RealBound.lean:288 are credited as in lane B's source. No first/general
formalisation or mathematical novelty claim. No configuration/energy proof here.
-/
set_option autoImplicit false
open Filter Topology Polynomial

namespace CLeadingInstance
noncomputable section

/-- PROOF-DRAFT: the exact general-s finite target specializes to C0 at s=5. -/
theorem finite_real_bound_at_five
    (hFinite : U48.FiniteRealBoundStatement CCompact.u) :
    CCompact.FiniteRealBoundStatement := by
  intro n hn
  have h := hFinite 5 n (by norm_num) hn
  norm_num only [Nat.cast_ofNat] at h
  simpa only [CCompact.F, CCompact.ξ, CCompact.K] using h

-- PROOF-DRAFT supporting data: actual lower-order coefficient, unchanged from C0.
def lowerOrderCoeff : ℝ :=
  12 * Real.log 2 + 23 + Real.log (BAnalyticIntegral.C 5 (2 * Real.pi))

def lowerOrderError (n : ℕ) : ℝ :=
  (28 * 37 / 40) * (Real.log (CCompact.K n) / CCompact.K n) +
    (lowerOrderCoeff * 37 / 40) / CCompact.K n

/-- PROOF-DRAFT: K=40n is positive for the exact finite-bound range. -/
theorem K_pos {n : ℕ} (hn : 1 ≤ n) : 0 < CCompact.K n := by
  unfold CCompact.K
  positivity

/-- PROOF-DRAFT: same actual K as the arithmetic normalizer, tending to infinity. -/
theorem K_tendsto_atTop : Tendsto CCompact.K atTop atTop := by
  change Tendsto (fun n : ℕ => ((40 * n : ℕ) : ℝ)) atTop atTop
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 40 by norm_num)

/-- PROOF-DRAFT: the exact lower-order error, divided by K squared, vanishes. -/
theorem lower_order_error_tendsto :
    Tendsto lowerOrderError atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1 := (hlog.comp K_tendsto_atTop).const_mul (28 * 37 / 40)
  have h2 := (tendsto_inv_atTop_zero.comp K_tendsto_atTop).const_mul
    (lowerOrderCoeff * 37 / 40)
  have h := h1.add h2
  change Tendsto (fun n : ℕ => (28 * 37 / 40) *
    (Real.log (CCompact.K n) / CCompact.K n) +
      (lowerOrderCoeff * 37 / 40) / CCompact.K n) atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_zero, zero_add, div_eq_mul_inv] using h

/-- PROOF-DRAFT: exact identity with C0's finite-bound error, not an estimate. -/
theorem lower_order_error_mul_square (n : ℕ) (hn : 1 ≤ n) :
    lowerOrderError n * CCompact.K n ^ 2 =
      28 * ((37 * n : ℕ) : ℝ) * Real.log (CCompact.K n) +
        lowerOrderCoeff * ((37 * n : ℕ) : ℝ) := by
  have hK := (K_pos hn).ne'
  have hh : ((37 * n : ℕ) : ℝ) = 37 / 40 * CCompact.K n := by
    unfold CCompact.K
    push_cast
    ring
  rw [hh]
  unfold lowerOrderError
  field_simp [hK] <;> ring

/-- PROOF-DRAFT: the exact C0 finite bound implies its positive leading bound.
The only caller premise is the named finite bound; no field/configuration
statement or asymptotic conclusion is silently assumed. -/
theorem analytic_leading_of_finite
    (hFinite : CCompact.FiniteRealBoundStatement) :
    CCompact.AnalyticLeadingStatement := by
  intro ε hε
  have hsmall := lower_order_error_tendsto.eventually_lt_const hε
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hnε hn
  obtain ⟨hpos, hbound⟩ := hFinite n hn
  refine ⟨hpos, ?_⟩
  calc
    _ ≤ CCompact.u * CCompact.K n ^ 2 + lowerOrderError n * CCompact.K n ^ 2 := by
      rw [lower_order_error_mul_square n hn]
      simpa only [lowerOrderCoeff, add_assoc] using hbound
    _ ≤ CCompact.u * CCompact.K n ^ 2 + ε * CCompact.K n ^ 2 := by
      gcongr
    _ = (CCompact.u + ε) * CCompact.K n ^ 2 := by ring

#check finite_real_bound_at_five
#check analytic_leading_of_finite
#print axioms finite_real_bound_at_five
#print axioms analytic_leading_of_finite

end
end CLeadingInstance
