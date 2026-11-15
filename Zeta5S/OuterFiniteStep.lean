import Zeta5S.FiniteStep

/-!
L10/E309 outer finite s-step, Codex lane L, 2026-11-14.
Uses the unchanged raw weights and rank from L7, not the sharper E13 correction.
Status: PROOF-DRAFT until the repository gate records these declarations.
-/
open Finset
namespace AperyS
variable {p m : ℕ} [Fact p.Prime]

def outerArg (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  (i : ℚ) + (ν : ℚ) / 2 * delC N c - ((ellC hm K c : ℚ) + ((s : ℚ) - 1)) / 2

lemma outerArg_sstep (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ) :
    outerArg hm (s + 2) ν N K c i = outerArg hm s ν N K c i - 1 := by
  unfold outerArg
  push_cast
  ring

lemma wO_eq_min (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ)
    (hc : c ≠ 0) (hi : i < nbC hm N K c) :
    wO hm s ν N K c i = min 0 (outerArg hm s ν N K c i) := by
  simp [wO, hc, hi, outerArg]

lemma min_zero_shift_bounds (t : ℚ) :
    min 0 t - 1 ≤ min 0 (t - 1) ∧ min 0 (t - 1) ≤ min 0 t := by
  constructor
  · rw [← min_sub_sub_right]
    exact min_le_min (by norm_num) le_rfl
  · exact min_le_min le_rfl (by linarith)

theorem wO_sstep_bounds (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ) :
    wO hm s ν N K c i - 1 ≤ wO hm (s + 2) ν N K c i ∧
      wO hm (s + 2) ν N K c i ≤ wO hm s ν N K c i := by
  by_cases hc : c = 0
  · simp only [wO, if_pos hc]
    constructor <;> linarith
  · by_cases hi : i < nbC hm N K c
    · rw [wO_eq_min hm s ν N K c i hc hi,
        wO_eq_min hm (s + 2) ν N K c i hc hi, outerArg_sstep]
      exact min_zero_shift_bounds _
    · simp [wO, hc, hi]

theorem wO_sstep_unchanged (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ)
    (h : c = 0 ∨ nbC hm N K c ≤ i) :
    wO hm (s + 2) ν N K c i = wO hm s ν N K c i := by
  rcases h with hc | hi
  · simp [wO, hc]
  · by_cases hc : c = 0 <;> simp [wO, hc, Nat.not_lt.mpr hi]

theorem wO_sstep_full_drop (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ)
    (hc : c ≠ 0) (hi : i < nbC hm N K c) (ht : outerArg hm s ν N K c i ≤ 0) :
    wO hm (s + 2) ν N K c i = wO hm s ν N K c i - 1 := by
  rw [wO_eq_min hm s ν N K c i hc hi,
    wO_eq_min hm (s + 2) ν N K c i hc hi, outerArg_sstep,
    min_eq_right ht, min_eq_right (by linarith)]

theorem wO_sstep_zero_drop (hm : 2 * m + 1 = p) (s ν N K : ℕ) (c : Fin (m + 1)) (i : ℕ)
    (hc : c ≠ 0) (hi : i < nbC hm N K c) (ht : 1 ≤ outerArg hm s ν N K c i) :
    wO hm (s + 2) ν N K c i = wO hm s ν N K c i := by
  rw [wO_eq_min hm s ν N K c i hc hi,
    wO_eq_min hm (s + 2) ν N K c i hc hi, outerArg_sstep,
    min_eq_left (by linarith), min_eq_left (by linarith)]

noncomputable def outerWeightSum (hm : 2 * m + 1 = p) (s ν K N : ℕ) : ℚ :=
  ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i

theorem outerWeightSum_sstep_bounds (hm : 2 * m + 1 = p) (s ν K N : ℕ) :
    outerWeightSum hm s ν K N - (K - N : ℕ) ≤ outerWeightSum hm (s + 2) ν K N ∧
      outerWeightSum hm (s + 2) ν K N ≤ outerWeightSum hm s ν K N := by
  constructor
  · have h := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
      Finset.sum_le_sum (fun i (_ : i ∈ range (LoC hm N K c)) =>
        (wO_sstep_bounds hm s ν N K c i).1))
    simpa only [outerWeightSum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, ← Nat.cast_sum, sum_LoC] using h
  · exact Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun i _ =>
      (wO_sstep_bounds hm s ν N K c i).2))

namespace AssemblyTarget

def rawRank (s ν K N p : ℕ) : ℕ :=
  min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1))

lemma half_sstep (s : ℕ) (hs : 1 ≤ s) : (s + 2 - 1) / 2 = (s - 1) / 2 + 1 := by omega

theorem rawRank_sstep (s ν K N p : ℕ) (hs : 1 ≤ s) :
    rawRank (s + 2) ν K N p ≤ rawRank s ν K N p ∧
      rawRank s ν K N p ≤ rawRank (s + 2) ν K N p + (p - 1) := by
  unfold rawRank
  rw [half_sstep s hs, Nat.add_mul, one_mul]
  omega

lemma WO_eq_weights_rank (s ν K N p : ℕ) (hp : p.Prime) (hm : 2 * (p / 2) + 1 = p) :
    WO s ν K N p = 2 * @outerWeightSum p (p / 2) ⟨hp⟩ hm s ν K N -
      (rawRank s ν K N p : ℚ) := by
  simp only [WO, dif_pos hp, dif_pos hm, outerWeightSum, rawRank]

theorem WO_sstep_exact (s ν K N p : ℕ) (hp : p.Prime) (hm : 2 * (p / 2) + 1 = p) :
    WO (s + 2) ν K N p - WO s ν K N p =
      2 * (@outerWeightSum p (p / 2) ⟨hp⟩ hm (s + 2) ν K N -
        @outerWeightSum p (p / 2) ⟨hp⟩ hm s ν K N) +
      ((rawRank s ν K N p : ℚ) - rawRank (s + 2) ν K N p) := by
  simp only [WO, dif_pos hp, dif_pos hm, outerWeightSum, rawRank]
  ring

theorem WO_sstep_bounds (s ν K N p : ℕ) (hp : p.Prime) (hm : 2 * (p / 2) + 1 = p) :
    -2 * (K - N : ℕ) + ((rawRank s ν K N p : ℚ) - rawRank (s + 2) ν K N p) ≤
        WO (s + 2) ν K N p - WO s ν K N p ∧
      WO (s + 2) ν K N p - WO s ν K N p ≤
        (rawRank s ν K N p : ℚ) - rawRank (s + 2) ν K N p := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := outerWeightSum_sstep_bounds hm s ν K N
  rw [WO_sstep_exact s ν K N p hp hm]
  constructor <;> linarith [h.1, h.2]

theorem Lp_outer_sstep (s ν K N M p : ℕ) (L : Allocations) (hp : p.Prime)
    (hcut : K < p * M) (hrange : K < 3 * p)
    (hflag : OuterOK s K N p) (hflag' : OuterOK (s + 2) K N p) :
    Lp s ν K N M p L - (2 : ℤ) * (K - N : ℕ) +
        ((rawRank s ν K N p : ℤ) - rawRank (s + 2) ν K N p) ≤ Lp (s + 2) ν K N M p L ∧
      Lp (s + 2) ν K N M p L ≤ Lp s ν K N M p L +
        ((rawRank s ν K N p : ℤ) - rawRank (s + 2) ν K N p) := by
  have hW := WO_sstep_bounds s ν K N p hp hflag.1
  have hlo : ⌊WO s ν K N p⌋ - (2 : ℤ) * (K - N : ℕ) +
      ((rawRank s ν K N p : ℤ) - rawRank (s + 2) ν K N p) ≤ ⌊WO (s + 2) ν K N p⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have := Int.floor_le (WO s ν K N p)
    linarith [hW.1]
  have hhi : ⌊WO (s + 2) ν K N p⌋ ≤ ⌊WO s ν K N p⌋ +
      ((rawRank s ν K N p : ℤ) - rawRank (s + 2) ν K N p) := by
    apply Int.floor_le_iff.mpr
    push_cast
    have := Int.lt_floor_add_one (WO s ν K N p)
    linarith [hW.2]
  simp only [Lp, if_neg (Nat.not_le.mpr hcut), if_neg (Nat.not_le.mpr hrange),
    if_pos hflag, if_pos hflag']
  constructor <;> omega

end AssemblyTarget
end AperyS
