import PhiGamma
import InnerWeight
import InnerScalar

/- E420 native Codex inner_explicit. PROOF-DRAFT composition of the actual
same-allocation local bridge. E428 reverse weights and E424 scalar are exact
credited copies; the posted E405 allocation and every model remain unchanged. -/
namespace BInnerExplicit
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.RangeBridgeTarget

def modelPhiMax (s r n p : ℕ) : ℝ :=
  max
    (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ))
    (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p + 1) : ℝ))

def nearError (s ν M : ℕ) : ℝ :=
  ((fillBudget s ν M : ℝ) + s + 30 * M + 6) * (6 * M + 1)

def localError (s ν M : ℕ) : ℝ :=
  (discreteError s ν M : ℝ) + nearError s ν M + gammaError s M + 4 * M

lemma selectedLevel_abs_bound (s ν K N M p : ℕ) :
    |(selectedLevel s ν K N M p : ℝ)| ≤ (fillBudget s ν M : ℝ) + 4 * M + 4 := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  have hlo : -(B : ℤ) ≤ selectedLevel s ν K N M p :=
    kfSel_ge β (K - N) B (-(B : ℤ)) ((B : ℤ) + 4 * M + 4)
  have hhi : selectedLevel s ν K N M p ≤ (B : ℤ) + 4 * M + 4 :=
    kfSel_le β (K - N) B (-(B : ℤ)) ((B : ℤ) + 4 * M + 4) (by omega)
  have hloR : -(B : ℝ) ≤ (selectedLevel s ν K N M p : ℝ) := by exact_mod_cast hlo
  have hhiR : (selectedLevel s ν K N M p : ℝ) ≤ (B : ℝ) + 4 * M + 4 := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> linarith

lemma twice_max (a b : ℝ) : max (2 * a) (2 * b) = 2 * max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left (le_of_not_ge h), max_eq_left (by linarith)]

variable {p : ℕ} [hp : Fact p.Prime]

lemma model_level_window (s ν n M : ℕ) (hs : 5 ≤ s) (hν : ν ≤ 10) (hKM : 40 * n < p * M) :
    -(fillBudget s ν M : ℤ) ≤ modelKappa s ν n p ∧
      modelKappa s ν n p + 1 ≤ (fillBudget s ν M : ℤ) + 4 * M + 4 := by
  have hT := modelT_bounds ν n M hν hKM
  have hQ := modelQ_bounds n M hKM
  have hloR : -(2 * (M : ℝ)) - s ≤ (modelKappa s ν n p : ℝ) := by
    unfold modelKappa
    push_cast
    linarith [hT.1, hQ.2]
  have hhiR : (modelKappa s ν n p : ℝ) ≤ 24 * M := by
    unfold modelKappa
    push_cast
    linarith [hT.2, hQ.1]
  have hloI : -(2 * (M : ℤ)) - s ≤ modelKappa s ν n p := by exact_mod_cast hloR
  have hhiI : modelKappa s ν n p ≤ 24 * (M : ℤ) := by exact_mod_cast hhiR
  have hB := budget_ge_low s ν M
  have hB24 : 24 * (M + 1) ≤ fillBudget s ν M := by
    have := Nat.mul_le_mul_right (M + 1) (show 24 ≤ 4 * (s + ν + 1) by omega)
    simpa only [fillBudget] using this
  constructor <;> omega

lemma selected_Phi_upper (s r M n p : ℕ) (hs : 5 ≤ s) (hr : r ≤ 5) (hM : 40 ≤ M)
    (hn : fillBudget s (2 * r) M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hpp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n)
      (selectedLevel s (2 * r) (40 * n) (3 * n) M p) : ℝ) ≤
        modelPhiMax s r n p + nearError s (2 * r) M := by
  haveI : Fact p.Prime := ⟨hpp⟩
  let β := beta s (2 * r) (40 * n) (3 * n) p
  let κ := modelKappa s (2 * r) n p
  let k := selectedLevel s (2 * r) (40 * n) (3 * n) M p
  have hOK := explicit_innerOK_fixed_shape s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM
  obtain ⟨hodd, _, _, _, _, _, _, _⟩ := hOK
  have hRows := rows_model_near_peak s r n M hr hodd hKM hin
  have hNear := BInnerWeight.Phi_le_max_adjacent β (37 * n) κ k ((6 * M + 1 : ℕ) : ℚ)
    (by positivity) hRows.1 hRows.2
  have hNearR := (Rat.cast_le (K := ℝ)).mpr hNear
  push_cast at hNearR
  have hSel := selectedLevel_abs_bound s (2 * r) (40 * n) (3 * n) M p
  have hKap := modelKappa_bound s (2 * r) n M (by omega) hKM
  have hDist : |(k : ℝ) - (κ : ℝ)| ≤ (fillBudget s (2 * r) M : ℝ) + s + 30 * M + 4 :=
    (abs_sub _ _).trans (by dsimp [k, κ]; linarith)
  have hDistProd := mul_le_mul_of_nonneg_right (add_le_add_right hDist 2)
    (by positivity : (0 : ℝ) ≤ 6 * M + 1)
  have hScale : modelPhiMax s r n p = 2 * max (PhiK β (37 * n) κ : ℝ) (PhiK β (37 * n) (κ + 1) : ℝ) :=
    twice_max _ _
  unfold nearError
  change 2 * (PhiK β (37 * n) k : ℝ) ≤ _
  nlinarith

lemma selected_cost_upper (s r M n p : ℕ) (hs : 5 ≤ s) (hr : r ≤ 5) (hM : 40 ≤ M)
    (hn : fillBudget s (2 * r) M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hpp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    -(LpSharp s (2 * r) (40 * n) (3 * n) M p (explicitAllocation s (2 * r) (40 * n) (3 * n) M) : ℝ) ≤
      -(vSK (2 * r) (40 * n) (3 * n) p : ℝ) - modelPhiMax s r n p + (discreteError s (2 * r) M : ℝ) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hwindow := model_level_window s (2 * r) n M hs (by omega) hKM
  let κ := modelKappa s (2 * r) n p
  have h0 := selected_cost_le_Phi s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM hin κ
    hwindow.1 (by omega)
  have h1 := selected_cost_le_Phi s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM hin (κ + 1)
    (by omega) hwindow.2
  have h0R := (Rat.cast_le (K := ℝ)).mpr h0
  have h1R := (Rat.cast_le (K := ℝ)).mpr h1
  push_cast at h0R h1R
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  rw [hshape] at h0R h1R
  unfold modelPhiMax
  rcases le_total
      (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) κ : ℝ))
      (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (κ + 1) : ℝ)) with h | h
  · rw [max_eq_right h]
    exact h1R
  · rw [max_eq_left h]
    exact h0R

lemma selected_cost_lower (s r M n p : ℕ) (hs : 5 ≤ s) (hr : r ≤ 5) (hM : 40 ≤ M)
    (hn : fillBudget s (2 * r) M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hpp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    -(vSK (2 * r) (40 * n) (3 * n) p : ℝ) - modelPhiMax s r n p - nearError s (2 * r) M ≤
      -(LpSharp s (2 * r) (40 * n) (3 * n) M p (explicitAllocation s (2 * r) (40 * n) (3 * n) M) : ℝ) := by
  have hW := BInnerWeight.explicit_weight_le_Phi_fixed_shape s (2 * r) M n p
    (by omega) (by omega) hM hn hpp hKM
  have hWR := (Rat.cast_le (K := ℝ)).mpr hW
  push_cast at hWR
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  rw [hshape] at hWR
  have hPhi := selected_Phi_upper s r M n p hs hr hM hn hpp hKM hin
  have hfloor := Int.floor_le
    (2 * WI s (2 * r) (40 * n) (3 * n) p (explicitAllocation s (2 * r) (40 * n) (3 * n) M))
  have hfloorR := (Rat.cast_le (K := ℝ)).mpr hfloor
  push_cast at hfloorR
  rw [selected_explicit_inner s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM hin]
  push_cast
  linarith

/-- PROOF-DRAFT: actual two-sided local inner estimate for the literal explicit allocation. -/
theorem inner_local_fixed_shape (s r M n p : ℕ) (hs : 5 ≤ s) (hr : r ≤ 5) (hM : 40 ≤ M)
    (hn : fillBudget s (2 * r) M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hpp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    InnerOK s (2 * r) (40 * n) (3 * n) p (explicitAllocation s (2 * r) (40 * n) (3 * n) M) ∧
      |(-(LpSharp s (2 * r) (40 * n) (3 * n) M p
            (explicitAllocation s (2 * r) (40 * n) (3 * n) M) : ℝ)) -
          (p : ℝ) * innerR (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ localError s (2 * r) M := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hOK := explicit_innerOK_fixed_shape s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM
  obtain ⟨hodd, _, _, _, _, _, _, _⟩ := hOK
  have hGamma := model_Phi_max_error s r n M hr hodd hKM hin
  have hnM : M ^ 2 ≤ n := by nlinarith [Nat.zero_le (s * M)]
  have hScalar := BInnerScalar.scalar_inner_fixed_shape (2 * r) n M p hM hnM hpp hKM
  have hUpper := selected_cost_upper s r M n p hs hr hM hn hpp hKM hin
  have hLower := selected_cost_lower s r M n p hs hr hM hn hpp hKM hin
  have hDisc0 : (0 : ℝ) ≤ (discreteError s (2 * r) M : ℝ) := by
    apply Rat.cast_nonneg.mpr
    unfold discreteError
    positivity
  have hNear0 : 0 ≤ nearError s (2 * r) M := by unfold nearError; positivity
  refine ⟨explicit_innerOK_fixed_shape s (2 * r) M n p (by omega) (by omega) hM hn hpp hKM, ?_⟩
  change |-(LpSharp s (2 * r) (40 * n) (3 * n) M p
      (explicitAllocation s (2 * r) (40 * n) (3 * n) M) : ℝ) -
    (p : ℝ) * innerR (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ _
  change |modelPhiMax s r n p - (p : ℝ) * innerGamma (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ _ at hGamma
  change |(vSK (2 * r) (40 * n) (3 * n) p : ℝ) -
    (p : ℝ) * innerN ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ 4 * M at hScalar
  rw [abs_le] at hGamma hScalar ⊢
  unfold localError innerR
  constructor <;> nlinarith [hGamma.1, hGamma.2, hScalar.1, hScalar.2]

lemma localError_nonneg (s ν M : ℕ) : 0 ≤ localError s ν M := by
  have hD : (0 : ℝ) ≤ (discreteError s ν M : ℝ) := by
    apply Rat.cast_nonneg.mpr
    unfold discreteError
    positivity
  have hN : 0 ≤ nearError s ν M := by unfold nearError; positivity
  have hG : 0 ≤ gammaError s M := by unfold gammaError; positivity
  unfold localError
  positivity

/-- PROOF-DRAFT: the literal posted E420 two-sided local statement, with actual
InnerOK as conclusion, same explicitAllocation, and no comparison hypothesis. -/
theorem inner_explicit_local_statement : Mathathon.P108.InnerExplicitTarget.InnerExplicitLocalStatement := by
  intro s ν M hscope hM
  obtain ⟨hoddS, hs, hνEven, hν2, hν10⟩ := hscope
  obtain ⟨r, hr⟩ := hνEven
  have hν : ν = 2 * r := by omega
  subst ν
  have hr5 : r ≤ 5 := by omega
  refine ⟨localError s (2 * r) M, localError_nonneg s (2 * r) M, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨fillBudget s (2 * r) M + (s + M + 1) ^ 2 + 1, ?_⟩
  intro n hn p hpp hbound hKM hin
  simpa only [two_mul, modelX] using inner_local_fixed_shape s r M n p hs hr5 hM hn hpp hKM hin

/-- PROOF-DRAFT: exact E405 explicit upper target, derived from the two-sided statement. -/
theorem inner_explicit_upper_statement : InnerExplicitLocalUpperStatement := by
  intro s ν M hscope hM
  obtain ⟨C, hC, hlocal⟩ := inner_explicit_local_statement s ν M hscope hM
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlocal] with n hn
  intro p hpp hbound hKM hin
  obtain ⟨hOK, herr⟩ := hn p hpp hbound hKM hin
  refine ⟨hOK, ?_⟩
  have := (abs_le.mp herr).2
  linarith

/-- PROOF-DRAFT: exact matching lower target for the same explicit allocation. -/
theorem inner_explicit_lower_statement : Mathathon.P108.InnerExplicitTarget.InnerExplicitLocalLowerStatement := by
  intro s ν M hscope hM
  obtain ⟨C, hC, hlocal⟩ := inner_explicit_local_statement s ν M hscope hM
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlocal] with n hn
  intro p hpp hbound hKM hin
  have herr := (hn p hpp hbound hKM hin).2
  have := (abs_le.mp herr).1
  linarith

end
end BInnerExplicit
