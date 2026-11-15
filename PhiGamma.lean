import PhaseErrors

/- E420 native Codex inner_explicit. PROOF-DRAFT two adjacent actual Phi
levels against the literal actual rootGamma. This is a selected-allocation
calculation; it asserts no optimization over allocations. -/
open Finset
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108 Mathathon.P108.RangeBridgeTarget

def modelOrdinarySum (s r n p : ℕ) : ℝ :=
  ∑ c ∈ Icc 1 (p / 2),
    ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
      ((modelT (2 * r) n p : ℝ) + (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
        (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))

lemma sum_erase_zero_eq_Icc_real {m : ℕ} (F : ℕ → ℝ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), Finset.sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by
    ext c
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h2] at h1
  linarith

variable {p : ℕ} [hp : Fact p.Prime]

lemma model_base_row_sum (s r n : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hin : 3 * p ≤ 40 * n) :
    (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ))) =
      (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) := by
  rw [model_rows_base_real s r n hr hodd hin, Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum]
  have hcard : ((univ : Finset (Fin (p / 2 + 1))).erase 0).card = p / 2 := by simp
  have hSX : (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) = ((3 * n - 3 * n / p : ℕ) : ℝ) := by
    exact_mod_cast sum_SX_ordinary (3 * n) hodd
  rw [hcard, hSX]
  simp only [nsmul_eq_mul, Nat.cast_sub (Nat.div_le_self (3 * n) p)]

/-- PROOF-DRAFT: exact base Phi decomposition for actual beta/counts. -/
theorem model_Phi_base (s r n : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hin : 3 * p ≤ 40 * n) :
    2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ) =
      modelOrdinarySum s r n p + (modelKappa s (2 * r) n p : ℝ) *
        (((37 * n : ℕ) : ℝ) -
          (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ)) := by
  let b : Fin (p / 2 + 1) → ℤ := fun c => (r : ℤ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ)
  let ellK : Fin (p / 2 + 1) → ℤ := fun c => (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ)
  have hBeta : ∀ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      beta s (2 * r) (40 * n) (3 * n) p c = 2 * b c - ellK c - (s : ℤ) + 1 := by
    intro c hc
    dsimp [b, ellK, beta]
    push_cast
    ring
  have hTb : ∀ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0, b c ≤ modelT (2 * r) n p :=
    fun c hc => modelT_ge_class r n hr hodd hin c (Finset.mem_erase.mp hc).1
  have hEll : ∀ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      ellK c = modelQ n p ∨ ellK c = modelQ n p + 1 :=
    fun c hc => SX_two_values (40 * n) hodd c (Finset.mem_erase.mp hc).1
  have hPhi := PhiK_model_level (beta s (2 * r) (40 * n) (3 * n) p) b ellK
    (37 * n) (modelT (2 * r) n p) (modelQ n p) s hBeta hTb hEll
  have hLift := congrArg (fun z : ℚ => (z : ℝ)) hPhi
  push_cast at hLift
  have hPhiR :
      2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ) =
        (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
          ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
            ((modelT (2 * r) n p : ℝ) + (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
              (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))) +
        (modelKappa s (2 * r) n p : ℝ) *
          (((37 * n : ℕ) : ℝ) -
            ∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
              ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ))) := by
    simpa only [b, ellK, modelKappa, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast,
      Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat] using hLift
  rw [model_base_row_sum s r n hr hodd hin] at hPhiR
  have hsum : (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
        ((modelT (2 * r) n p : ℝ) + (r : ℝ) * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
          (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))) = modelOrdinarySum s r n p := by
    exact sum_erase_zero_eq_Icc_real (m := p / 2) (fun c : ℕ =>
      ((modelT (2 * r) n p : ℝ) - (r : ℝ) * (SX p (3 * n) ((c : ℤ) : ZMod p) : ℝ)) *
        ((modelT (2 * r) n p : ℝ) + (r : ℝ) * (SX p (3 * n) ((c : ℤ) : ZMod p) : ℝ) -
          (SX p (40 * n) ((c : ℤ) : ZMod p) : ℝ) - (s : ℝ)))
  rw [hsum] at hPhiR
  exact hPhiR

def gammaBase (s r n p : ℕ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) z) +
    sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) * (modelKappa s (2 * r) n p : ℝ)

def gammaError (s M : ℕ) : ℝ :=
  90 * ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 + ((s : ℝ) + 26 * M) * (11 * M) + 13 * M

theorem model_Phi_base_error (s r n M : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    |2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ) -
        (p : ℝ) * gammaBase s r n p| ≤
      90 * ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 + ((s : ℝ) + 26 * M) * (11 * M) := by
  have hOrd := ordinary_gamma_approx s (2 * r) n M p (by omega) hp.out hodd hKM
  have hhalf : ((2 * r : ℕ) : ℝ) / 2 = r := by push_cast; ring
  have hOrd' : |modelOrdinarySum s r n p - (p : ℝ) *
      (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) z)| ≤
        90 * ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 := by
    simpa only [modelOrdinarySum, modelT_cast, modelX, hhalf] using hOrd
  have hPhase := model_rows_remainder_bound s r n M hr hodd hKM hin
  have hKappa := modelKappa_bound s (2 * r) n M (by omega) hKM
  have heq :
      2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ) -
          (p : ℝ) * gammaBase s r n p =
      (modelOrdinarySum s r n p - (p : ℝ) *
        (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) z)) +
      (modelKappa s (2 * r) n p : ℝ) *
        (((37 * n : ℕ) : ℝ) -
          (rowsK (beta s (2 * r) (40 * n) (3 * n) p) (modelKappa s (2 * r) n p) : ℝ) -
            (p : ℝ) * sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)) := by
    rw [model_Phi_base s r n hr hodd hin]
    unfold gammaBase
    ring
  rw [heq]
  have hprod := mul_le_mul hKappa hPhase (abs_nonneg _) (by positivity : 0 ≤ (s : ℝ) + 26 * M)
  rw [← abs_mul] at hprod
  exact (abs_add_le _ _).trans (by linarith)

/-- PROOF-DRAFT: two adjacent actual discrete Phi values identify the literal
rootGamma, including its fractional upper-layer positive-part term. -/
theorem model_Phi_max_error (s r n M : ℕ) (hr : r ≤ 5)
    (hodd : 2 * (p / 2) + 1 = p) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    |max
        (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p) : ℝ))
        (2 * (PhiK (beta s (2 * r) (40 * n) (3 * n) p) (37 * n) (modelKappa s (2 * r) n p + 1) : ℝ)) -
      (p : ℝ) * innerGamma (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ gammaError s M := by
  let β := beta s (2 * r) (40 * n) (3 * n) p
  let κ := modelKappa s (2 * r) n p
  let A : ℝ := 2 * (PhiK β (37 * n) κ : ℝ)
  let B : ℝ := 2 * (PhiK β (37 * n) (κ + 1) : ℝ)
  let Δ : ℝ := B - A
  let phase : ℝ := sigmaC ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) - nplus (modelX n p)
  have hPhi := PhiK_succ β (37 * n) κ
  have hLift := congrArg (fun z : ℚ => (z : ℝ)) hPhi
  push_cast at hLift
  have hDelta : Δ = ((37 * n : ℕ) : ℝ) - (rowsK β (κ + 1) : ℝ) := by
    dsimp [Δ, A, B]
    push_cast
    linarith
  have hPhase : |Δ - (p : ℝ) * phase| ≤ 13 * M := by
    rw [hDelta]
    exact model_next_remainder_bound s r n M hr hodd hKM hin
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hscaled : max 0 ((p : ℝ) * phase) = (p : ℝ) * max phase 0 := by
    by_cases h : 0 ≤ phase
    · rw [max_eq_right (mul_nonneg hpR.le h), max_eq_left h]
    · have h' : phase ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hpR.le h'), max_eq_right h']
      simp
  have hmaxLip := ClassSums.abs_max0_sub Δ ((p : ℝ) * phase)
  rw [hscaled] at hmaxLip
  have htop : |max 0 Δ - (p : ℝ) * max phase 0| ≤ 13 * M := hmaxLip.trans hPhase
  have hmaxeq : max A B = A + max 0 Δ := by
    by_cases h : A ≤ B
    · rw [max_eq_right h, max_eq_right (show 0 ≤ Δ by dsimp [Δ]; linarith)]
      dsimp [Δ]
      ring
    · rw [max_eq_left (le_of_not_ge h), max_eq_left (show Δ ≤ 0 by dsimp [Δ]; linarith)]
      ring
  have hkReal : (modelKappa s (2 * r) n p : ℝ) =
      2 * Tc ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) - (⌊2 * modelX n p⌋ : ℝ) - (s : ℝ) := by
    unfold modelKappa modelQ
    push_cast
    rw [modelT_cast]
    push_cast
    rfl
  have hGamma : innerGamma (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) =
      gammaBase s r n p + max phase 0 := by
    unfold innerGamma gammaBase
    rw [hkReal]
  have heq : max A B - (p : ℝ) * innerGamma (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p) =
      (A - (p : ℝ) * gammaBase s r n p) + (max 0 Δ - (p : ℝ) * max phase 0) := by
    rw [hmaxeq, hGamma]
    ring
  change |max A B - (p : ℝ) * innerGamma (s : ℝ) ((2 * r : ℕ) : ℝ) (3 / 40) (modelX n p)| ≤ _
  rw [heq]
  have hbase := model_Phi_base_error s r n M hr hodd hKM hin
  have hbase' : |A - (p : ℝ) * gammaBase s r n p| ≤
      90 * ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 + ((s : ℝ) + 26 * M) * (11 * M) := hbase
  unfold gammaError
  exact (abs_add_le _ _).trans (by linarith)

end
end BInnerExplicit
