import Mathathon.P108.SStep

/-!
# #108: the U-free s-step is ≥ 167/300 for every real s ≥ 7 (α = 3/40, ν ≤ 10) (EVENT WORK)

advocate:Claude Opus 5.5 (thread sstep-all-s, queue row 31), Sat Nov 14 2026. Lean v4.33.1,
Mathlib v4.33.1. Master copy: `problems/108-zeta-odd-autopsy/evidence/sstep_all_s/SStepAll.lean`;
built as `LeanCriterion/SStepAll.lean` in the probe `evidence/lean_criterion`.

Claims (`../sstep_all_s/proof.md`, Theorem 1 and Corollary 3):
* `sstep_ge`: for all real `s ≥ 7` and real `ν ≤ 10`,
  `2λ/3 + I_out(s+2, ν, 3/40) − I_out(s, ν, 3/40) ≥ 167/300`, `λ = 37/40`;
* `thetaPkg_odd_ge`: for every `n : ℕ`, real `ν ≤ 10`, `M ≥ 3` and real `U`,
  `Θ(7, ν; M, U) + n · 167/300 ≤ Θ(7 + 2n, ν; M, U)`;
* `thetaPkg_odd_pos`: hence `Θ(7, ν; M, U) > 0` implies `Θ(7 + 2n, ν; M, U) > 0`.

Proof: pointwise in `y` (`Tout_sstep`), `T_out(s+2, ν, y) − T_out(s, ν, y) ≥ −max(0, 8/5 − 3y)`:
the per-pole term gains `2·B(y) ≥ 0`, every removed-class cost `c¹(ℓ)` is non-decreasing in `s`,
`min(r̂, ẑ) ≥ 0` at `s + 2`, and `min(r̂, ẑ) ≤ r̂ ≤ max(0, 8/5 − 3y)` at `s` (this uses `s ≥ 7`,
`ν ≤ 10`). The integral of `max(0, 8/5 − 3y)` over `[1/3, 37/20]` is `3/50`, and `37/60 − 3/50 =
167/300`.

Differences from the claim (read before citing): `I_out`, `T_out`, `Θ` are the definitions of
`OuterDefs.lean` and `SStep.lean` (transcriptions of criterion5's formulas and code, not a formal
derivation of them from Fauzan's valuation bounds); `U` is a free real parameter (the analytic
bound is not formalized; it is the same number on both sides); `s` and `ν` are real (the claim
needs only odd `s ≥ 7` and even `ν ≤ 10`); the numerical floor `Θ(7, ν) ≥ 0.905804` (criterion_map
TABLE.md, COMPUTED) is not formalized, only the implication `thetaPkg_odd_pos`.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-! ### The pieces of `gOuter` with `⌊1/y⌋₊` replaced by a parameter `k` -/

/-- `u = (α + v − y)₊`, `v = 1 − k y`. -/
def uuK (α y : ℝ) (k : ℕ) : ℝ := max 0 (α + (1 - (k : ℝ) * y) - y)

/-- `m_v = min(α, v)`, `v = 1 − k y`. -/
def mvK (α y : ℝ) (k : ℕ) : ℝ := min α (1 - (k : ℝ) * y)

/-- The per-pole bracket `B = (1 − y) − Σ_ℓ dens(ℓ)(ℓ − 2)` of `gOuter`. -/
def brK (α y : ℝ) (k : ℕ) : ℝ :=
  (1 - y) - ((α - mvK α y k) * (2 * (k : ℝ) - 2) + (mvK α y k - uuK α y k) * (2 * (k : ℝ) + 1 - 2)
    + uuK α y k * (2 * (k : ℝ) + 2 - 2))

/-- The removed-class costs `Σ_ℓ dens(ℓ) c¹(ℓ)` of `gOuter`. -/
def clK (s ν α y : ℝ) (k : ℕ) : ℝ :=
  (α - mvK α y k) * cRem s ν (2 * k) + (mvK α y k - uuK α y k) * cRem s ν (2 * k + 1)
    + uuK α y k * cRem s ν (2 * k + 2)

/-- The zero count `ẑ` of `gOuter`. -/
def zhK (s ν α y : ℝ) (k : ℕ) : ℝ :=
  (y - 2 * α) + ((α - mvK α y k) * zRem s ν (2 * k) + (mvK α y k - uuK α y k) * zRem s ν (2 * k + 1)
    + uuK α y k * zRem s ν (2 * k + 2))

/-- The clamped rank `r̂ = min(λ, (1 + (ν−2)α − ((s−1)/2) y)₊)` of `gOuter`. -/
def rhat (s ν α y : ℝ) : ℝ := min (1 - α) (max 0 (1 + (ν - 2) * α - (s - 1) / 2 * y))

lemma gOuter_eq (s ν α y : ℝ) (h : 1 / 3 < y ∧ y ≤ 1) :
    gOuter s ν α y = (s + 2) * brK α y ⌊1 / y⌋₊ + clK s ν α y ⌊1 / y⌋₊
      + min (rhat s ν α y) (zhK s ν α y ⌊1 / y⌋₊) := by
  unfold gOuter brK clK zhK rhat mvK uuK
  rw [if_pos h]

lemma floor_cases (y : ℝ) (h1 : 1 / 3 < y) (h2 : y ≤ 1) :
    ((⌊1 / y⌋₊ : ℝ) = 2 ∧ y ≤ 1 / 2) ∨ ((⌊1 / y⌋₊ : ℝ) = 1 ∧ 1 / 2 < y) := by
  rcases le_or_gt y (1 / 2) with h | h
  · exact Or.inl ⟨by rw [fl2 y h1 h]; norm_num, h⟩
  · exact Or.inr ⟨by rw [fl1 y h h2]; norm_num, h⟩

/-! ### Monotonicity in `s` of the class costs, positivity of the zero counts -/

lemma cRem_le_succ2 (s ν : ℝ) (l : ℕ) : cRem s ν l ≤ cRem (s + 2) ν l := by
  unfold cRem
  apply Finset.sum_le_sum
  intro i _
  exact max_le_max le_rfl (by linarith)

lemma one_le_zRem (s ν : ℝ) (l : ℕ) : 1 ≤ zRem s ν l := by
  unfold zRem
  have : (0 : ℝ) ≤ ∑ i ∈ Finset.range (l - 2),
      (if (l : ℝ) + s - 1 - ν - 2 * (i : ℝ) ≤ 0 then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  linarith

/-! ### The three facts about the densities and the bracket at α = 3/40 -/

lemma dens_nonneg (y : ℝ) (k : ℕ) (h1 : 1 / 3 < y) (h2 : y ≤ 1)
    (hk : ((k : ℝ) = 2 ∧ y ≤ 1 / 2) ∨ ((k : ℝ) = 1 ∧ 1 / 2 < y)) :
    0 ≤ (3/40 : ℝ) - mvK (3/40) y k ∧ 0 ≤ mvK (3/40) y k - uuK (3/40) y k ∧ 0 ≤ uuK (3/40) y k := by
  unfold mvK uuK
  refine ⟨by linarith [min_le_left (3/40 : ℝ) (1 - (k : ℝ) * y)], ?_, le_max_left _ _⟩
  have hv0 : 0 ≤ 1 - (k : ℝ) * y := by
    rcases hk with ⟨hk, h⟩ | ⟨hk, h⟩ <;> rw [hk] <;> linarith
  have hvy : 1 - (k : ℝ) * y ≤ y := by
    rcases hk with ⟨hk, h⟩ | ⟨hk, h⟩ <;> rw [hk] <;> linarith
  have : max 0 ((3/40 : ℝ) + (1 - (k : ℝ) * y) - y) ≤ min (3/40) (1 - (k : ℝ) * y) :=
    max_le (le_min (by norm_num) hv0) (le_min (by linarith) (by linarith))
  linarith

lemma brK_nonneg (y : ℝ) (k : ℕ) (h1 : 1 / 3 < y) (_h2 : y ≤ 1)
    (hk : ((k : ℝ) = 2 ∧ y ≤ 1 / 2) ∨ ((k : ℝ) = 1 ∧ 1 / 2 < y)) : 0 ≤ brK (3/40) y k := by
  unfold brK mvK uuK
  rcases hk with ⟨hk, h⟩ | ⟨hk, h⟩ <;> rw [hk]
  · have hm := min_le_left (3/40 : ℝ) (1 - 2 * y)
    have hu : max 0 ((3/40 : ℝ) + (1 - 2 * y) - y) ≤ 3/40 := max_le (by norm_num) (by linarith)
    linarith
  · rcases le_total 0 ((3/40 : ℝ) + (1 - 1 * y) - y) with hu | hu
    · have e := max_eq_right hu
      have hm := min_le_left (3/40 : ℝ) (1 - 1 * y)
      linarith
    · have e := max_eq_left hu
      have hm := min_le_right (3/40 : ℝ) (1 - 1 * y)
      linarith

lemma clK_mono (s ν y : ℝ) (k : ℕ) (h1 : 1 / 3 < y) (h2 : y ≤ 1)
    (hk : ((k : ℝ) = 2 ∧ y ≤ 1 / 2) ∨ ((k : ℝ) = 1 ∧ 1 / 2 < y)) :
    clK s ν (3/40) y k ≤ clK (s + 2) ν (3/40) y k := by
  obtain ⟨d0, d1, d2⟩ := dens_nonneg y k h1 h2 hk
  unfold clK
  have a := mul_le_mul_of_nonneg_left (cRem_le_succ2 s ν (2 * k)) d0
  have b := mul_le_mul_of_nonneg_left (cRem_le_succ2 s ν (2 * k + 1)) d1
  have c := mul_le_mul_of_nonneg_left (cRem_le_succ2 s ν (2 * k + 2)) d2
  linarith

lemma zhK_nonneg (s ν y : ℝ) (k : ℕ) (h1 : 1 / 3 < y) (h2 : y ≤ 1)
    (hk : ((k : ℝ) = 2 ∧ y ≤ 1 / 2) ∨ ((k : ℝ) = 1 ∧ 1 / 2 < y)) : 0 ≤ zhK s ν (3/40) y k := by
  obtain ⟨d0, d1, d2⟩ := dens_nonneg y k h1 h2 hk
  unfold zhK
  have a := mul_nonneg d0 (le_trans zero_le_one (one_le_zRem s ν (2 * k)))
  have b := mul_nonneg d1 (le_trans zero_le_one (one_le_zRem s ν (2 * k + 1)))
  have c := mul_nonneg d2 (le_trans zero_le_one (one_le_zRem s ν (2 * k + 2)))
  linarith

lemma rhat_nonneg (s ν y : ℝ) : 0 ≤ rhat s ν (3/40) y :=
  le_min (by norm_num) (le_max_left _ _)

lemma rhat_le (s ν y : ℝ) (hs : 7 ≤ s) (hν : ν ≤ 10) (hy : 0 ≤ y) :
    rhat s ν (3/40) y ≤ max 0 (8/5 - 3 * y) := by
  unfold rhat
  refine (min_le_right _ _).trans (max_le_max le_rfl ?_)
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hy]

/-! ### The pointwise s-step bound -/

/-- **Pointwise s-step bound.** For real `s ≥ 7`, `ν ≤ 10` and every `y`:
`g_(s+2,ν)(y) − g_(s,ν)(y) ≥ −max(0, 8/5 − 3y)` at α = 3/40. -/
lemma gOuter_sstep (s ν y : ℝ) (hs : 7 ≤ s) (hν : ν ≤ 10) :
    -max 0 (8/5 - 3 * y) ≤ gOuter (s + 2) ν (3/40) y - gOuter s ν (3/40) y := by
  by_cases h : 1 / 3 < y ∧ y ≤ 1
  · rw [gOuter_eq _ _ _ _ h, gOuter_eq _ _ _ _ h]
    obtain ⟨h1, h2⟩ := h
    have hk := floor_cases y h1 h2
    have hB := brK_nonneg y _ h1 h2 hk
    have hC := clK_mono s ν y _ h1 h2 hk
    have hZ := zhK_nonneg (s + 2) ν y _ h1 h2 hk
    have hR := rhat_nonneg (s + 2) ν y
    have hRs := rhat_le s ν y hs hν (by linarith)
    have m1 : 0 ≤ min (rhat (s + 2) ν (3/40) y) (zhK (s + 2) ν (3/40) y ⌊1 / y⌋₊) := le_min hR hZ
    have m2 : min (rhat s ν (3/40) y) (zhK s ν (3/40) y ⌊1 / y⌋₊) ≤ max 0 (8/5 - 3 * y) :=
      (min_le_left _ _).trans hRs
    have e : (s + 2 + 2) * brK (3/40) y ⌊1 / y⌋₊
        = (s + 2) * brK (3/40) y ⌊1 / y⌋₊ + 2 * brK (3/40) y ⌊1 / y⌋₊ := by ring
    linarith
  · unfold gOuter
    rw [if_neg h, if_neg h, sub_self]
    exact neg_nonpos.mpr (le_max_left _ _)

lemma Tout_sstep (s ν y : ℝ) (hs : 7 ≤ s) (hν : ν ≤ 10) :
    -max 0 (8/5 - 3 * y) ≤ Tout (s + 2) ν (3/40) y - Tout s ν (3/40) y := by
  have := gOuter_sstep s ν y hs hν
  unfold Tout
  linarith

/-! ### Interval integrability of `T_out` for every real `s, ν` (α = 3/40) -/

/-- `T_out` with `⌊1/y⌋₊` frozen to `k ≥ 1`. -/
def ToutK (s ν α y : ℝ) (k : ℕ) : ℝ :=
  ((s + 2) * brK α y k + clK s ν α y k + min (rhat s ν α y) (zhK s ν α y k))
    + (-2 * (1 - α) * (k : ℝ) + ∑ j ∈ Finset.range 6, max (2 * (1 - α) - ((j : ℝ) + 1) * y) 0)

/-- `T_out` on `(1, 2λ]` (`⌊1/y⌋₊ = 0`, `g = 0`). -/
def Tout0 (α y : ℝ) : ℝ :=
  -2 * (1 - α) * ((0 : ℕ) : ℝ) + ∑ j ∈ Finset.range 6, max (2 * (1 - α) - ((j : ℝ) + 1) * y) 0

lemma ToutK_cont (s ν α : ℝ) (k : ℕ) : Continuous (fun y => ToutK s ν α y k) := by
  unfold ToutK brK clK zhK rhat mvK uuK
  fun_prop

lemma Tout0_cont (α : ℝ) : Continuous (fun y => Tout0 α y) := by
  unfold Tout0
  fun_prop

lemma Tout_eq_K2 (s ν α y : ℝ) (h1 : 1 / 3 < y) (h2 : y ≤ 1 / 2) :
    Tout s ν α y = ToutK s ν α y 2 := by
  unfold Tout legendreTerm ToutK
  rw [gOuter_eq s ν α y ⟨h1, by linarith⟩, fl2 y h1 h2]

lemma Tout_eq_K1 (s ν α y : ℝ) (h1 : 1 / 2 < y) (h2 : y ≤ 1) :
    Tout s ν α y = ToutK s ν α y 1 := by
  unfold Tout legendreTerm ToutK
  rw [gOuter_eq s ν α y ⟨by linarith, h2⟩, fl1 y h1 h2]

lemma Tout_eq_K0 (s ν α y : ℝ) (h1 : 1 < y) : Tout s ν α y = Tout0 α y := by
  unfold Tout gOuter legendreTerm Tout0
  rw [if_neg (fun h => by linarith [h.2]), fl0 y h1, zero_add]

lemma Tout_intervalIntegrable (s ν : ℝ) :
    IntervalIntegrable (fun y => Tout s ν (3/40) y) volume (1/3) (2 * (1 - 3/40)) := by
  have i1 : IntervalIntegrable (fun y => Tout s ν (3/40) y) volume (1/3) (1/2) := by
    refine ((ToutK_cont s ν (3/40) 2).intervalIntegrable _ _).congr ?_
    rw [uIoc_of_le (by norm_num)]
    intro y hy
    exact (Tout_eq_K2 s ν (3/40) y hy.1 hy.2).symm
  have i2 : IntervalIntegrable (fun y => Tout s ν (3/40) y) volume (1/2) 1 := by
    refine ((ToutK_cont s ν (3/40) 1).intervalIntegrable _ _).congr ?_
    rw [uIoc_of_le (by norm_num)]
    intro y hy
    exact (Tout_eq_K1 s ν (3/40) y hy.1 hy.2).symm
  have i3 : IntervalIntegrable (fun y => Tout s ν (3/40) y) volume 1 (2 * (1 - 3/40)) := by
    refine ((Tout0_cont (3/40)).intervalIntegrable _ _).congr ?_
    rw [uIoc_of_le (by norm_num)]
    intro y hy
    exact (Tout_eq_K0 s ν (3/40) y hy.1).symm
  exact (i1.trans i2).trans i3

/-! ### The theorems -/

/-- `∫_(1/3)^(2λ) −max(0, 8/5 − 3y) dy = −3/50` (λ = 37/40). -/
lemma integral_bound :
    ∫ y in (1/3 : ℝ)..(2 * (1 - 3/40)), -max 0 (8/5 - 3 * y) = -(3/50) := by
  have p1 := piece_integral (fun y : ℝ => -max 0 (8/5 - 3 * y)) (1/3) (8/15) (-8/5) 3 (by norm_num)
    (fun y hy => by
      show -max 0 (8/5 - 3 * y) = -8/5 + 3 * y
      rw [max_eq_right (by linarith [hy.2])]; ring)
  have p2 := piece_integral (fun y : ℝ => -max 0 (8/5 - 3 * y)) (8/15) (2 * (1 - 3/40)) 0 0
    (by norm_num)
    (fun y hy => by
      show -max 0 (8/5 - 3 * y) = 0 + 0 * y
      rw [max_eq_left (by linarith [hy.1])]; ring)
  exact (integral_concat _ _ _ _ _ _ p1 p2).2.trans (by norm_num)

/-- **Theorem 1 (the s-step for every real s ≥ 7).** At α = 3/40 (λ = 37/40), for all real
`s ≥ 7` and `ν ≤ 10`: `2λ/3 + I_out(s+2, ν) − I_out(s, ν) ≥ 167/300`. -/
theorem sstep_ge (s ν : ℝ) (hs : 7 ≤ s) (hν : ν ≤ 10) :
    167 / 300 ≤ 2 * (1 - (3/40 : ℝ)) / 3 + (Iout (s + 2) ν (3/40) - Iout s ν (3/40)) := by
  have hmono : ∫ y in (1/3 : ℝ)..(2 * (1 - 3/40)), -max 0 (8/5 - 3 * y)
      ≤ ∫ y in (1/3 : ℝ)..(2 * (1 - 3/40)), (Tout (s + 2) ν (3/40) y - Tout s ν (3/40) y) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous fun y : ℝ => -max 0 (8/5 - 3 * y)).intervalIntegrable _ _
    · exact (Tout_intervalIntegrable (s + 2) ν).sub (Tout_intervalIntegrable s ν)
    · intro y _
      exact Tout_sstep s ν y hs hν
  rw [intervalIntegral.integral_sub (Tout_intervalIntegrable (s + 2) ν)
    (Tout_intervalIntegrable s ν), integral_bound] at hmono
  unfold Iout
  linarith

/-- The s-step is positive for every real `s ≥ 7`, `ν ≤ 10` (α = 3/40). -/
theorem sstep_pos (s ν : ℝ) (hs : 7 ≤ s) (hν : ν ≤ 10) :
    0 < 2 * (1 - (3/40 : ℝ)) / 3 + (Iout (s + 2) ν (3/40) - Iout s ν (3/40)) := by
  have := sstep_ge s ν hs hν
  linarith

/-- **Corollary 3.** For every `n : ℕ`, real `ν ≤ 10`, `M ≥ 3` and real `U`:
`Θ(7, ν; M, U) + n · 167/300 ≤ Θ(7 + 2n, ν; M, U)` at α = 3/40. -/
theorem thetaPkg_odd_ge (n : ℕ) (ν M U : ℝ) (hν : ν ≤ 10) (hM : 3 ≤ M) :
    thetaPkg 7 ν (3/40) M U + n * (167 / 300) ≤ thetaPkg (7 + 2 * n) ν (3/40) M U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep := thetaPkg_sstep (7 + 2 * n) ν (3/40) M U hM
    have hpos := sstep_ge (7 + 2 * n) ν (by linarith) hν
    have e : (7 : ℝ) + 2 * ((n + 1 : ℕ) : ℝ) = 7 + 2 * (n : ℝ) + 2 := by push_cast; ring
    rw [e]
    push_cast
    linarith

/-- If the ζ(7) margin `Θ(7, ν; M, U)` is positive, so is `Θ(s, ν; M, U)` for every odd `s ≥ 7`. -/
theorem thetaPkg_odd_pos (n : ℕ) (ν M U : ℝ) (hν : ν ≤ 10) (hM : 3 ≤ M)
    (h7 : 0 < thetaPkg 7 ν (3/40) M U) : 0 < thetaPkg (7 + 2 * n) ν (3/40) M U := by
  have := thetaPkg_odd_ge n ν M U hν hM
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end

end Mathathon.P108
