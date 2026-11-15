import Interface

/-!
E601 / C4. Codex GPT-6.1 sol, lane C driver, 2026-11-14.
PROOF-DRAFT: final estimate and criterion assembly, pending build/gate.
A re-derivation of Fauzan's theorem reusing Firsching's formalisation
(mo271/Zeta5@be1c0d82, Apache-2.0; Comparator metadata Paul-Lez).
The logarithm/evaluation/degree assembly adapts Apery/MainEstimate.lean:67-109.
The last reduction adapts Apery/Main.lean:19-27 and imports the unchanged
Apery/Criterion.lean:44-49,99-101. Substantive inputs remain named hypotheses.
-/
set_option autoImplicit false
open Polynomial Filter Topology

namespace CCompact
noncomputable section

/-- PROOF-DRAFT: exact approved final-estimate interface, all inputs explicit. -/
theorem main_estimate_of_inputs : AssemblyStatement := by
  intro hDegree hNormalization hGrowth hAnalytic hClosing hMargin
  obtain ⟨hm_pos, hm_int⟩ := hNormalization
  let δ : ℝ := -(A + u)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hsum : A + u < 0 := by
      rw [hMargin]
      exact hClosing
    linarith
  refine ⟨800 * δ, by positivity, ?_⟩
  filter_upwards [hGrowth (δ / 8) (by positivity),
    hAnalytic (δ / 8) (by positivity), eventually_ge_atTop 1] with n hlog hAnal hn
  obtain ⟨Q, hQ⟩ := hm_int n hn
  obtain ⟨hFpos, hFlog⟩ := hAnal
  have hmR : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hm_pos n
  have hQeval : aeval ξ Q = (m n : ℝ) * aeval ξ (F n) := by
    rw [← aeval_map_algebraMap ℚ ξ Q]
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
    have hδeq : A + u = -δ := by dsimp only [δ]; ring
    rw [hK2] at hlog hFlog
    nlinarith [mul_pos hδ hn2]

/-- PROOF-DRAFT: the exact upstream criterion applied to the actual real zeta value. -/
theorem irrational_five_of_main_estimate : CriterionTransportStatement := by
  intro hZeta hMain
  obtain ⟨c, hc, h⟩ := hMain
  have hIrr : Irrational ξ :=
    Apery.irrational_of_eventually_exists_int_poly ξ (fun n => 37 * n)
      (fun n => Real.exp (-c * (n : ℝ) ^ 2))
      (Apery.tendsto_pow_mul_exp_neg_sq_of_pos hc)
      (h.mono fun _ ⟨Q, _hQ, hdeg, hpos, hlt⟩ => ⟨Q, hdeg, hpos, hlt.le⟩)
  exact ⟨ξ, hIrr, hZeta.2⟩

/-- PROOF-DRAFT: current endpoint; precisely the inputs not yet imported as producers. -/
theorem irrational_five
    (hDegree : DegreeStatement) (hNormalization : NormalizationStatement)
    (hGrowth : NormalizerGrowthStatement) (hAnalytic : AnalyticLeadingStatement)
    (hClosing : ClosingStatement) (hMargin : MarginIdentityStatement)
    (hZeta : ZetaIdentificationStatement) : ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  irrational_five_of_main_estimate hZeta
    (main_estimate_of_inputs hDegree hNormalization hGrowth hAnalytic hClosing hMargin)

#print axioms main_estimate_of_inputs
#print axioms irrational_five_of_main_estimate
#print axioms irrational_five
#check main_estimate_of_inputs
#check irrational_five_of_main_estimate
#check irrational_five

end
end CCompact
