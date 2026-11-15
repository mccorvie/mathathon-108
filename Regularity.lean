import Mathathon.P108.OuterDefs
import Transfer

/- E423 lane B driver. PROOF-DRAFT until gate.
Actual rootTout is unchanged. The continuous fixed-floor branch below is an
auxiliary expression identified with that actual definition, not a model substitute.
Source: Mathathon/P108/OuterDefs.lean47-79, event work; source attribution retained. -/
open Filter Topology MeasureTheory Set
namespace BOuterLimit
noncomputable section
open Mathathon.P108

def gFixed (s ν : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  let α : ℝ := 3 / 40
  let v : ℝ := 1 - (k : ℝ) * y
  let u : ℝ := max 0 (α + v - y)
  let mv : ℝ := min α v
  let d0 : ℝ := α - mv
  let d1 : ℝ := mv - u
  let d2 : ℝ := u
  let cost : ℝ := (s + 2) * ((1 - y) - (d0 * (2 * (k : ℝ) - 2) + d1 * (2 * (k : ℝ) + 1 - 2)
      + d2 * (2 * (k : ℝ) + 2 - 2)))
    + (d0 * cRem s ν (2 * k) + d1 * cRem s ν (2 * k + 1) + d2 * cRem s ν (2 * k + 2))
  let zz : ℝ := (y - 2 * α)
    + (d0 * zRem s ν (2 * k) + d1 * zRem s ν (2 * k + 1) + d2 * zRem s ν (2 * k + 2))
  let r : ℝ := min (1 - α) (max 0 (1 + (ν - 2) * α - (s - 1) / 2 * y))
  cost + min r zz

def lFixed (k : ℕ) (y : ℝ) : ℝ :=
  -2 * (1 - 3 / 40) * (k : ℝ) + ∑ j ∈ Finset.range 6, max (2 * (1 - 3 / 40) - ((j : ℝ) + 1) * y) 0

def tFixed (s ν : ℝ) (k : ℕ) (y : ℝ) : ℝ := gFixed s ν k y + lFixed k y

theorem continuous_gFixed (s ν : ℝ) (k : ℕ) : Continuous (gFixed s ν k) := by
  unfold gFixed
  fun_prop

theorem continuous_lFixed (k : ℕ) : Continuous (lFixed k) := by
  unfold lFixed
  fun_prop

theorem continuous_tFixed (s ν : ℝ) (k : ℕ) : Continuous (tFixed s ν k) :=
  (continuous_gFixed s ν k).add (continuous_lFixed k)

theorem Tout_eq_fixed (s ν y : ℝ) (k : ℕ)
    (hy : 1 / 3 < y ∧ y ≤ 1) (hk : ⌊1 / y⌋₊ = k) :
    Tout s ν (3 / 40) y = tFixed s ν k y := by
  simp only [Tout, gOuter, if_pos hy, legendreTerm, hk, tFixed, gFixed, lFixed]

theorem Tout_eq_fixed0 (s ν y : ℝ) (hy : 1 < y) :
    Tout s ν (3 / 40) y = lFixed 0 y := by
  have hnot : ¬(1 / 3 < y ∧ y ≤ 1) := by intro h; linarith [h.2]
  simp only [Tout, gOuter, if_neg hnot, legendreTerm, fl0 y hy, zero_add, lFixed]

theorem Tout_left_endpoint (s ν : ℝ) :
    Tout s ν (3 / 40) (1 / 3) = lFixed 3 (1 / 3) := by
  norm_num [Tout, gOuter, legendreTerm, lFixed]

theorem Tout_continuousAt (s ν y : ℝ) (hy : (1 : ℝ) / 3 ≤ y)
    (h13 : y ≠ 1 / 3) (h12 : y ≠ 1 / 2) (h1 : y ≠ 1) :
    ContinuousAt (Tout s ν (3 / 40)) y := by
  have hy13 : (1 : ℝ) / 3 < y := lt_of_le_of_ne hy (Ne.symm h13)
  by_cases hy12 : y < 1 / 2
  · apply (continuous_tFixed s ν 2).continuousAt.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hy13 hy12] with z hz
    exact Tout_eq_fixed s ν z 2 ⟨hz.1, by linarith [hz.2]⟩ (fl2 z hz.1 hz.2.le)
  · have hyhalf : (1 : ℝ) / 2 < y := lt_of_le_of_ne (le_of_not_gt hy12) (Ne.symm h12)
    by_cases hy1 : y < 1
    · apply (continuous_tFixed s ν 1).continuousAt.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hyhalf hy1] with z hz
      exact Tout_eq_fixed s ν z 1 ⟨by linarith [hz.1], hz.2.le⟩ (fl1 z hz.1 hz.2.le)
    · have hyy : (1 : ℝ) < y := lt_of_le_of_ne (le_of_not_gt hy1) (Ne.symm h1)
      apply (continuous_lFixed 0).continuousAt.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hyy] with z hz
      exact Tout_eq_fixed0 s ν z hz

theorem Tout_finite_discontinuities (s ν : ℝ) :
    {y ∈ Icc ((1 : ℝ) / 3) (37 / 20) |
      ¬ContinuousWithinAt (Tout s ν (3 / 40)) (Icc (1 / 3) (37 / 20)) y}.Finite := by
  apply (show ({(1 : ℝ) / 3, 1 / 2, 1} : Set ℝ).Finite by simp).subset
  intro y hy
  by_contra h
  have hn : y ≠ (1 : ℝ) / 3 ∧ y ≠ 1 / 2 ∧ y ≠ 1 := by simpa using h
  exact hy.2 ((Tout_continuousAt s ν y hy.1.1 hn.1 hn.2.1 hn.2.2).continuousWithinAt)

theorem continuous_bound (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, ∀ y ∈ Icc ((1 : ℝ) / 3) (37 / 20), |f y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.abs.continuousOn
  exact ⟨C, fun y hy => hC (mem_image_of_mem _ hy)⟩

theorem Tout_bounded (s ν : ℝ) :
    ∃ C : ℝ, ∀ y ∈ Icc ((1 : ℝ) / 3) (37 / 20), |Tout s ν (3 / 40) y| ≤ C := by
  obtain ⟨C0, h0⟩ := continuous_bound (lFixed 0) (continuous_lFixed 0)
  obtain ⟨C1, h1⟩ := continuous_bound (tFixed s ν 1) (continuous_tFixed s ν 1)
  obtain ⟨C2, h2⟩ := continuous_bound (tFixed s ν 2) (continuous_tFixed s ν 2)
  obtain ⟨C3, h3⟩ := continuous_bound (lFixed 3) (continuous_lFixed 3)
  refine ⟨max C0 (max C1 (max C2 C3)), ?_⟩
  intro y hy
  by_cases he : y = 1 / 3
  · subst y
    rw [Tout_left_endpoint]
    exact (h3 _ hy).trans ((le_max_right C2 C3).trans ((le_max_right C1 _).trans (le_max_right C0 _)))
  · have hy13 : (1 : ℝ) / 3 < y := lt_of_le_of_ne hy.1 (Ne.symm he)
    by_cases hy12 : y ≤ 1 / 2
    · rw [Tout_eq_fixed s ν y 2 ⟨hy13, by linarith⟩ (fl2 y hy13 hy12)]
      exact (h2 y hy).trans ((le_max_left C2 C3).trans ((le_max_right C1 _).trans (le_max_right C0 _)))
    · by_cases hy1 : y ≤ 1
      · have hyhalf : (1 : ℝ) / 2 < y := lt_of_not_ge hy12
        rw [Tout_eq_fixed s ν y 1 ⟨hy13, hy1⟩ (fl1 y hyhalf hy1)]
        exact (h1 y hy).trans ((le_max_left C1 _).trans (le_max_right C0 _))
      · rw [Tout_eq_fixed0 s ν y (lt_of_not_ge hy1)]
        exact (h0 y hy).trans (le_max_left C0 _)

theorem actual_outer_model_limit (s ν : ℝ) :
    Tendsto (fun n : ℕ => (BPrimeTransfer.K n : ℝ)⁻¹ *
      ∑ p ∈ Finset.Ioc ⌊(1 / 3 : ℝ) * BPrimeTransfer.K n⌋₊
        ⌊(37 / 20 : ℝ) * BPrimeTransfer.K n⌋₊ with p.Prime,
        Tout s ν (3 / 40) ((p : ℝ) / BPrimeTransfer.K n) * Real.log p)
      atTop (nhds (Iout s ν (3 / 40))) := by
  have h := (BPriorPrime.tendsto_primeRiemannSum (a := 1 / 3) (b := 37 / 20)
    (by norm_num) (by norm_num) (Tout_bounded s ν) (Tout_finite_discontinuities s ν)).comp
      BPrimeTransfer.tendsto_K_atTop
  convert h using 1 <;> norm_num [Iout] <;> rfl

#print axioms Tout_bounded
#print axioms Tout_finite_discontinuities
#print axioms actual_outer_model_limit

end
end BOuterLimit
