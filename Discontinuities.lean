import Continuity

/- E426 Codex inner_regularity. PROOF-DRAFT actual finite discontinuities.
Proof pattern: PRIOR Deicyde/zeta7-irrational@be55b3a4 PrimeSumBound536-591,
extended to zero/negative arbitrary coefficients, literal actual root model. -/
open MeasureTheory Set Filter Topology
namespace BInnerLimit
noncomputable section
open Mathathon.P108

def badSet (c : ℝ) (M : ℕ) : Set ℝ :=
  if c = 0 then ∅ else (fun k : ℤ => c / k) '' Icc (-⌈|c| * M⌉) ⌈|c| * M⌉

theorem badSet_finite (c : ℝ) (M : ℕ) : (badSet c M).Finite := by
  unfold badSet
  split_ifs
  · exact finite_empty
  · exact (finite_Icc _ _).image _

theorem mul_inv_ne_int {M : ℕ} (hM : 0 < M) {c y : ℝ} (hc : c ≠ 0)
    (hy : y ∈ Icc (1 / (M : ℝ)) (1 / 3)) (hF : y ∉ badSet c M) :
    ∀ k : ℤ, c * y⁻¹ ≠ k := by
  intro k hk
  apply hF
  unfold badSet
  rw [if_neg hc]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr hMR) hy.1
  have hxM : y⁻¹ ≤ M := by
    rw [← one_div, div_le_iff₀ hy0]
    have h := hy.1
    rw [div_le_iff₀ hMR] at h
    linarith
  have habs : |(k : ℝ)| ≤ |c| * M := by
    rw [← hk, abs_mul, abs_of_pos (inv_pos.mpr hy0)]
    exact mul_le_mul_of_nonneg_left hxM (abs_nonneg c)
  have hceil : |c| * (M : ℝ) ≤ (⌈|c| * (M : ℝ)⌉ : ℝ) := Int.le_ceil _
  refine ⟨k, ⟨?_, ?_⟩, ?_⟩
  · have h := (abs_le.mp habs).1
    have hr : (-(⌈|c| * (M : ℝ)⌉ : ℝ)) ≤ k := by linarith
    exact_mod_cast hr
  · have h := (abs_le.mp habs).2
    have hr : (k : ℝ) ≤ ⌈|c| * (M : ℝ)⌉ := by linarith
    exact_mod_cast hr
  · change c / (k : ℝ) = y
    rw [← hk, div_mul_eq_div_div, div_self hc, one_div, inv_inv]

theorem innerWeight_disc_finite (s ν : ℝ) {M : ℕ} (hM : 3 ≤ M) :
    {y ∈ Icc (1 / (M : ℝ)) (1 / 3) |
      ¬ContinuousWithinAt (innerWeight s ν) (Icc (1 / (M : ℝ)) (1 / 3)) y}.Finite := by
  let cH : ℝ := 2 * Hc ν (3 / 40)
  have hfin := ((((badSet_finite 1 M).union (badSet_finite (3 / 40) M)).union
    (badSet_finite 2 M)).union (badSet_finite (2 * (1 - 3 / 40)) M)).union (badSet_finite cH M)
  apply hfin.subset
  rintro y ⟨hy, hdisc⟩
  by_contra hF
  simp only [mem_union, not_or] at hF
  obtain ⟨⟨⟨⟨hF1, hFa⟩, hF2⟩, hFl⟩, hFH⟩ := hF
  have hM0 : 0 < M := by omega
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by exact_mod_cast hM0)) hy.1
  have hX : ∀ k : ℤ, y⁻¹ ≠ k := by
    simpa only [one_mul] using mul_inv_ne_int hM0 (by norm_num : (1 : ℝ) ≠ 0) hy hF1
  have hA := mul_inv_ne_int hM0 (by norm_num : (3 / 40 : ℝ) ≠ 0) hy hFa
  have hTwo := mul_inv_ne_int hM0 (by norm_num : (2 : ℝ) ≠ 0) hy hF2
  have hLam := mul_inv_ne_int hM0 (by norm_num : (2 * (1 - 3 / 40) : ℝ) ≠ 0) hy hFl
  have cT : ContinuousAt (Tc ν (3 / 40)) y⁻¹ := by
    by_cases hc : cH = 0
    · have heq : Tc ν (3 / 40) = fun _ : ℝ => 0 := by
        funext z
        have hz : 2 * Hc ν (3 / 40) = 0 := hc
        simp only [Tc, hz, zero_mul, Int.floor_zero, Int.cast_zero]
      rw [heq]
      exact continuousAt_const
    · have hNe := mul_inv_ne_int hM0 hc hy hFH
      have hh : cH * y⁻¹ ≠ (⌊cH * y⁻¹⌋ : ℝ) := hNe _
      exact (continuousAt_floorCast hh).comp (continuousAt_const.mul continuousAt_id)
  have hR := innerR_continuousAt s ν (3 / 40) y⁻¹ hX hA cT hTwo hLam
  apply hdisc
  exact (continuousAt_id.mul (hR.comp (continuousAt_inv₀ hy0.ne'))).continuousWithinAt

theorem finite_discontinuities_statement : FiniteDiscontinuitiesStatement := by
  intro s ν M hM
  exact innerWeight_disc_finite s ν hM

#print axioms innerWeight_disc_finite
#print axioms finite_discontinuities_statement
end
end BInnerLimit
