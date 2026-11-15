import BorelRegularity
/-! E225/U30, Codex. Every mathematical claim in this file has status
CONJECTURE pending parent gate and human statement comparison. Atomlessness
here follows from an explicit small-interval mass bound, never from the value
assigned by Lean to Real.log 0. -/
set_option autoImplicit false
noncomputable section
namespace U30
open MeasureTheory Set Real Filter

/-- CONJECTURE: a fixed finite real sqrt-mass constant excludes every atom.
The real constant C is finite by its type; the displayed bound is a premise. -/
theorem noAtoms_of_local_sqrt_bound (mu : Measure ℝ) (C : ℝ)
    (hsmall : ∀ x e : ℝ, 0<e →
      mu (Icc (x-e) (x+e)) ≤ ENNReal.ofReal (C*Real.sqrt e)) :
    NullSingletonClass mu := by
  refine ⟨fun x => ?_⟩
  apply le_antisymm ?_ bot_le
  have hc : Continuous (fun e : ℝ => ENNReal.ofReal (C*Real.sqrt e)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul Real.continuous_sqrt)
  have hl : Tendsto (fun e : ℝ => ENNReal.ofReal (C*Real.sqrt e))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ e : ℝ in nhdsWithin 0 (Ioi 0),
      mu {x} ≤ ENNReal.ofReal (C*Real.sqrt e) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    change 0<e at he
    have hsub : ({x}:Set ℝ) ⊆ Icc (x-e) (x+e) := by
      rw [singleton_subset_iff]
      constructor <;> linarith
    exact (measure_mono hsub).trans (hsmall x e he)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hl he

end U30
#print axioms U30.noAtoms_of_local_sqrt_bound
