import GeneralArith
import Apery.Criterion

/-!
E436, Codex lane B, 2026-11-14. PROOF-DRAFT until the official gate.
This generalizes C-zeta5-compact/Assembly.lean's exact proof to symbolic
s, nu, a fixed natural cutoff M and a real analytic exponent u. The delta/8
argument, evaluation-map transport and integer-polynomial criterion are the
same argument as C's; no second fixed-s=5 endpoint is produced here.

Credits: Fauzan's construction and criterion; Firsching's Zeta5 formalisation
at be1c0d82 (Apache-2.0), with Paul-Lez Comparator metadata; upstream
Apery/MainEstimate.lean:67-109 and Apery/Criterion.lean:44-49,99-101;
lane C E600/E601's Assembly.lean; lane L E311 and lane B E432, preserving
their prior Deicyde/PNT attribution. No analytic bound at a new nu, negative
package value or new zeta irrationality is supplied by this conditional theorem.
-/

set_option autoImplicit false
open Polynomial Filter Topology

namespace BSymbolicCriterion
noncomputable section

/-- PROOF-DRAFT: the actual normalized integer-polynomial family has positive
quadratic decay. The integer lift still records its literal polynomial identity. -/
def MainEstimateStatement (s ν M : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ Q : ℤ[X],
    Q.map (Int.castRingHom ℚ) = C (m s ν M n) * F s ν n ∧
    Q.natDegree ≤ 37 * n ∧
    0 < aeval (xi s) Q ∧
    aeval (xi s) Q < Real.exp (-c * (n : ℝ) ^ 2)

/-- PROOF-DRAFT: C's main-estimate proof with only its parameters generalized.
All intermediate hypotheses are explicit here and discharged in the headline. -/
theorem main_estimate_of_inputs (s ν M : ℕ) (u : ℝ)
    (hDegree : DegreeStatement s ν)
    (hNormalization : NormalizationStatement s ν M)
    (hGrowth : NormalizerGrowthStatement s ν M)
    (hAnalytic : AnalyticLeadingStatement s ν u)
    (hClosing : Mathathon.P108.thetaPkg s ν (3 / 40) M u < 0)
    (hMargin : A s ν M + u = Mathathon.P108.thetaPkg s ν (3 / 40) M u) :
    MainEstimateStatement s ν M := by
  obtain ⟨hm_pos, hm_int⟩ := hNormalization
  let δ : ℝ := -(A s ν M + u)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hsum : A s ν M + u < 0 := by
      rw [hMargin]
      exact hClosing
    linarith
  refine ⟨800 * δ, by positivity, ?_⟩
  filter_upwards [hGrowth (δ / 8) (by positivity),
    hAnalytic (δ / 8) (by positivity), eventually_ge_atTop 1] with n hlog hAnal hn
  obtain ⟨Q, hQ⟩ := hm_int n hn
  obtain ⟨hFpos, hFlog⟩ := hAnal
  have hmR : (0 : ℝ) < (m s ν M n : ℝ) := by exact_mod_cast hm_pos n
  have hQeval : aeval (xi s) Q = (m s ν M n : ℝ) * aeval (xi s) (F s ν n) := by
    rw [← aeval_map_algebraMap ℚ (xi s) Q]
    simp only [algebraMap_int_eq, hQ, map_mul, aeval_C]
    rfl
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · have hmap : (Q.map (Int.castRingHom ℚ)).natDegree = Q.natDegree :=
      natDegree_map_eq_of_injective Int.cast_injective Q
    rw [← hmap, hQ, natDegree_C_mul (hm_pos n).ne']
    exact hDegree n
  · rw [hQeval]
    exact mul_pos hmR hFpos
  · rw [hQeval, ← Real.log_lt_iff_lt_exp (mul_pos hmR hFpos),
      Real.log_mul hmR.ne' hFpos.ne']
    have hK2 : K n ^ 2 = 1600 * (n : ℝ) ^ 2 := by
      simp only [K, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
    have hδeq : A s ν M + u = -δ := by dsimp only [δ]; ring
    rw [hK2] at hlog hFlog
    nlinarith [mul_pos hδ hn2]

/-- PROOF-DRAFT: exactly the same integer-polynomial criterion used by C.
The real series is already the target, so no zeta-identification premise appears. -/
theorem irrational_of_main_estimate (s ν M : ℕ)
    (hMain : MainEstimateStatement s ν M) : Irrational (xi s) := by
  obtain ⟨c, hc, h⟩ := hMain
  exact Apery.irrational_of_eventually_exists_int_poly (xi s) (fun n => 37 * n)
    (fun n => Real.exp (-c * (n : ℝ) ^ 2))
    (Apery.tendsto_pow_mul_exp_neg_sq_of_pos hc)
    (h.mono fun _ ⟨Q, _hQ, hdeg, hpos, hlt⟩ => ⟨Q, hdeg, hpos, hlt.le⟩)

/-- PROOF-DRAFT: literal reviewed symbolic criterion. E432 growth, E311 integer
normalization, the general degree bound and the package identity are discharged.
Only the displayed parameter conditions, analytic bound and strict sign remain. -/
theorem irrationality_criterion : CriterionStatement := by
  intro s ν M hScope hM u hAnalytic hClosing
  exact irrational_of_main_estimate s ν M
    (main_estimate_of_inputs s ν M u (degree_statement s ν)
      (normalization s ν M hScope hM)
      (normalizer_growth s ν M hScope hM) hAnalytic hClosing
      (margin_identity s ν M u))

#print axioms main_estimate_of_inputs
#print axioms irrational_of_main_estimate
#print axioms irrationality_criterion
#check irrationality_criterion
#print CriterionStatement
#print AnalyticLeadingStatement

end
end BSymbolicCriterion
