import Zeta5S.NormalizationProof
import Zeta5S.AssemblyAnchors

/-!
L10/E309 finite-prime s-step, Codex lane L, 2026-11-14.
Statements concern the exact finite raw L7 definitions, without a prime-sum passage.
Original capped-weight definitions: Firsching/Paul-Lez mo271/Zeta5@be1c0d82,
Apery/Arith/InnerWeights.lean:20-26,112-127, Apache-2.0.
Status is assigned by the repository gate; work in progress is not claimed checked.
-/

open Finset Polynomial

namespace AperyS

def zeroShiftTwo (b : ℕ → ℚ) : ℕ → ℚ := fun a => b a + if a = 0 then 2 else 0

theorem BseS_sstep (s ν p K N : ℕ) :
    BseS (s + 2) ν p K N = zeroShiftTwo (BseS s ν p K N) := by
  funext a
  by_cases h : a = 0 <;> simp [BseS, zeroShiftTwo, h] <;> push_cast <;> ring

variable {m : ℕ}

lemma topwS_shift (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (a : Fin (m + 1)) (ha : a ≠ 0) :
    topwS (ℓ + 2) L (zeroShiftTwo b) a = topwS ℓ L b a - 1 := by
  have hnat : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  simp only [topwS, zeroShiftTwo, if_neg hnat]
  ring

theorem tminS_shift (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) :
    tminS (ℓ + 2) hm L (zeroShiftTwo b) = tminS ℓ hm L b - 1 := by
  have h1 : tminS (ℓ + 2) hm L (zeroShiftTwo b) + 1 ≤ tminS ℓ hm L b := by
    conv_rhs => unfold tminS
    apply Finset.le_inf'
    intro a ha
    have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have h := tmin_leS (ℓ + 2) hm L (zeroShiftTwo b) hne
    rw [topwS_shift ℓ L b a hne] at h
    linarith
  have h2 : tminS ℓ hm L b - 1 ≤ tminS (ℓ + 2) hm L (zeroShiftTwo b) := by
    conv_rhs => unfold tminS
    apply Finset.le_inf'
    intro a ha
    have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
    rw [topwS_shift ℓ L b a hne]
    have h := tmin_leS ℓ hm L b hne
    linarith
  linarith

theorem wrawS_shift (ℓ : ℚ) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (u : Σ a : Fin (m + 1), Fin (L a)) :
    wrawS (ℓ + 2) L (zeroShiftTwo b) u =
      wrawS ℓ L b u - if u.1 = 0 then 0 else 1 := by
  by_cases h : u.1 = 0
  · simp [wrawS, zeroShiftTwo, h]
  · have hnat : (u.1 : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    simp only [wrawS, zeroShiftTwo, if_neg h, if_neg hnat]
    ring

lemma min_sub_one (a b : ℚ) : min (a - 1) (b - 1) = min a b - 1 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

theorem wcapS_shift_bounds (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (u : Σ a : Fin (m + 1), Fin (L a)) :
    wcapS ℓ hm L b u - 1 ≤ wcapS (ℓ + 2) hm L (zeroShiftTwo b) u ∧
      wcapS (ℓ + 2) hm L (zeroShiftTwo b) u ≤ wcapS ℓ hm L b u := by
  have hlo : wrawS ℓ L b u - 1 ≤ wrawS (ℓ + 2) L (zeroShiftTwo b) u := by
    rw [wrawS_shift]; split_ifs <;> linarith
  have hhi : wrawS (ℓ + 2) L (zeroShiftTwo b) u ≤ wrawS ℓ L b u := by
    rw [wrawS_shift]; split_ifs <;> linarith
  unfold wcapS
  rw [tminS_shift]
  constructor
  · rw [← min_sub_one]
    exact min_le_min hlo le_rfl
  · exact min_le_min hhi (by linarith)

theorem wcapS_shift_ordinary (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (u : Σ a : Fin (m + 1), Fin (L a)) (hu : u.1 ≠ 0) :
    wcapS (ℓ + 2) hm L (zeroShiftTwo b) u = wcapS ℓ hm L b u - 1 := by
  unfold wcapS
  rw [tminS_shift, wrawS_shift, if_neg hu, min_sub_one]

theorem wcapS_shift_zero_uncapped (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (u : Σ a : Fin (m + 1), Fin (L a)) (hu : u.1 = 0)
    (hraw : wrawS ℓ L b u ≤ tminS ℓ hm L b - 1) :
    wcapS (ℓ + 2) hm L (zeroShiftTwo b) u = wcapS ℓ hm L b u := by
  unfold wcapS
  rw [tminS_shift, wrawS_shift, if_pos hu, sub_zero,
    min_eq_left hraw, min_eq_left (by linarith)]

theorem wcapS_shift_zero_capped (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (u : Σ a : Fin (m + 1), Fin (L a)) (hu : u.1 = 0)
    (hraw : tminS ℓ hm L b ≤ wrawS ℓ L b u) :
    wcapS (ℓ + 2) hm L (zeroShiftTwo b) u = wcapS ℓ hm L b u - 1 := by
  unfold wcapS
  rw [tminS_shift, wrawS_shift, if_pos hu, sub_zero,
    min_eq_right hraw, min_eq_right (by linarith)]

theorem sum_wcapS_shift_bounds (ℓ : ℚ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) :
    (∑ u, wcapS ℓ hm L b u) - (Fintype.card (Σ a : Fin (m + 1), Fin (L a)) : ℚ) ≤
        ∑ u, wcapS (ℓ + 2) hm L (zeroShiftTwo b) u ∧
      (∑ u, wcapS (ℓ + 2) hm L (zeroShiftTwo b) u) ≤ ∑ u, wcapS ℓ hm L b u := by
  constructor
  · have h := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) =>
      (wcapS_shift_bounds ℓ hm L b u).1)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  · exact Finset.sum_le_sum (fun u _ => (wcapS_shift_bounds ℓ hm L b u).2)

namespace AssemblyTarget

theorem tmin_BseS_sstep (s ν p K N : ℕ) (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) :
    tminS (((s + 2 : ℕ) : ℚ) - 1) hm L (BseS (s + 2) ν p K N) =
      tminS ((s : ℚ) - 1) hm L (BseS s ν p K N) - 1 := by
  have he : (((s + 2 : ℕ) : ℚ) - 1) = ((s : ℚ) - 1) + 2 := by push_cast; ring
  rw [he, BseS_sstep, tminS_shift]

theorem BseS_zero_loss_sstep (s ν p K N : ℕ) :
    BseS (s + 2) ν p K N 0 - (((s + 2 : ℕ) : ℚ) - 1) =
      BseS s ν p K N 0 - ((s : ℚ) - 1) := by
  rw [BseS_sstep]
  simp only [zeroShiftTwo, if_pos rfl]
  push_cast
  ring

theorem WI_sstep_bounds (s ν K N p : ℕ) (L : Allocations) (hm1 : 1 ≤ p / 2)
    (hL : ∑ c, L p c = K - N) :
    WI s ν K N p L - (K - N : ℕ) ≤ WI (s + 2) ν K N p L ∧
      WI (s + 2) ν K N p L ≤ WI s ν K N p L := by
  have h := sum_wcapS_shift_bounds ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N)
  have he : (((s + 2 : ℕ) : ℚ) - 1) = ((s : ℚ) - 1) + 2 := by push_cast; ring
  unfold WI
  rw [dif_pos hm1, dif_pos hm1, he, BseS_sstep]
  simpa only [Fintype.card_sigma, Fintype.card_fin, hL] using h

theorem InnerOK_sstep (s ν K N p : ℕ) (L : Allocations)
    (hflag : InnerOK s ν K N p L) (hps : s + 2 ≤ p)
    (hdeg : s + 2 + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2) :
    InnerOK (s + 2) ν K N p L := by
  obtain ⟨hm, hm1, _hps, hsep, hK, _hdeg, hsum, hZ⟩ := hflag
  refine ⟨hm, hm1, hps, hsep, hK, hdeg, hsum, ?_⟩
  rw [tmin_BseS_sstep, BseS_zero_loss_sstep]
  linarith

theorem Lp_inner_sstep (s ν K N M p : ℕ) (L : Allocations)
    (hcut : K < p * M) (hrange : 3 * p ≤ K)
    (hflag : InnerOK s ν K N p L) (hflag' : InnerOK (s + 2) ν K N p L) :
    Lp s ν K N M p L - (2 : ℤ) * (K - N : ℕ) ≤ Lp (s + 2) ν K N M p L ∧
      Lp (s + 2) ν K N M p L ≤ Lp s ν K N M p L := by
  have hdata := hflag
  obtain ⟨hm, hm1, hps, hsep, hK, hdeg, hsum, hZ⟩ := hdata
  have hW := WI_sstep_bounds s ν K N p L hm1 hsum
  have hlo : ⌊2 * WI s ν K N p L⌋ - (2 : ℤ) * (K - N : ℕ) ≤
      ⌊2 * WI (s + 2) ν K N p L⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have := Int.floor_le (2 * WI s ν K N p L)
    linarith [hW.1]
  have hhi : ⌊2 * WI (s + 2) ν K N p L⌋ ≤ ⌊2 * WI s ν K N p L⌋ :=
    Int.floor_mono (by linarith [hW.2])
  simp only [Lp, if_neg (Nat.not_le.mpr hcut), if_pos hrange, if_pos hflag, if_pos hflag']
  constructor <;> omega

/-- A concrete flag change prevents an unconditional monotonicity claim for selected Lp. -/
def switchAllocation : Allocations := fun _ c => ([2, 5, 4, 4, 7, 7, 8] : List ℕ).getD c.val 0

theorem switch_old_flag_false : ¬ InnerOK 5 6 40 3 13 switchAllocation := by
  rintro ⟨hm, hm1, hps, hsep, hK, hdeg, hsum, hZ⟩
  have hn : ¬ (tminS ((5 : ℚ) - 1) hm1 (switchAllocation 13) (BseS 5 6 13 40 3) ≤
      2 * (switchAllocation 13 0 : ℚ) + (BseS 5 6 13 40 3 0 - ((5 : ℚ) - 1)) / 2) := by
    decide +kernel +revert
  exact hn hZ

theorem switch_new_flag_true : InnerOK 7 6 40 3 13 switchAllocation := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, ?_, ?_⟩
  · unfold Sep; decide +kernel
  · decide +kernel
  · decide +kernel

theorem switch_WI7 : WI 7 6 40 3 13 switchAllocation = -169 / 2 := by decide +kernel

theorem switch_Lp5 : Lp 5 6 40 3 400 13 switchAllocation = -444 := by
  rw [Lp, if_neg (by decide), if_pos (by decide), if_neg switch_old_flag_false]
  decide +kernel

theorem switch_Lp7 : Lp 7 6 40 3 400 13 switchAllocation = -119 := by
  rw [Lp, if_neg (by decide), if_pos (by decide), if_pos switch_new_flag_true, VS13, switch_WI7]
  norm_num

theorem selected_Lp_can_increase :
    Lp 5 6 40 3 400 13 switchAllocation < Lp 7 6 40 3 400 13 switchAllocation := by
  rw [switch_Lp5, switch_Lp7]
  norm_num

end AssemblyTarget
end AperyS
