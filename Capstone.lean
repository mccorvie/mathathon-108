import BInnerStatement
import Asymptotic
import SharpSplit

/- E427 lane B driver. PROOF-DRAFT conditional assembly only.
The actual normalizer and range definitions are unchanged; SharpSplit has only
its import redirected to the canonical unchanged E405 source. Missing inner
and outer limiting propositions stay explicit hypotheses in this staging file.
-/
open Filter Topology
namespace BNormalizerLimit
noncomputable section
open AperyS.AssemblyTarget Mathathon.P108 Mathathon.P108.BridgeTarget
  Mathathon.P108.RangeBridgeTarget Mathathon.P108.InnerExplicitTarget

theorem tendsto_of_eventual_abs {f : ℕ → ℝ} {l : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |f n - l| ≤ ε) :
    Tendsto f atTop (nhds l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact hn.trans_lt (half_lt_self hε)

theorem outer_cost_tendsto (hOuter : OuterLimitStatement)
    (s ν M : ℕ) (hscope : ParameterScope s ν) (hM : 3 ≤ M)
    (L : ℕ → Allocations) :
    Tendsto (fun n : ℕ => outerPrimeLogContribution s ν (40 * n) (3 * n) M (L n) /
      (((40 * n : ℕ) : ℝ) ^ 2)) atTop (nhds (Iout (s : ℝ) (ν : ℝ) (3 / 40))) := by
  apply tendsto_of_eventual_abs
  intro ε hε
  filter_upwards [hOuter s ν hscope ε hε] with n hn
  obtain ⟨hl, hu⟩ := hn M hM (L n)
  rw [abs_le]
  constructor <;> linarith

theorem inner_cost_tendsto (hInner : InnerExplicitLimitStatement)
    (s ν M : ℕ) (hscope : ParameterScope s ν) (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => innerPrimeLogContribution s ν (40 * n) (3 * n) M
      (explicitAllocation s ν (40 * n) (3 * n) M) / (((40 * n : ℕ) : ℝ) ^ 2))
      atTop (nhds (innerIntegral s ν M)) :=
  tendsto_of_eventual_abs (hInner s ν M hscope hM)

/-- Conditional staging: the exact capstone follows from the two named range limits. -/
theorem explicit_normalizer_limit_of_ranges
    (hInner : InnerExplicitLimitStatement) (hOuter : OuterLimitStatement) :
    ExplicitNormalizerLimitStatement := by
  intro s ν M hscope hM
  have hM3 : 3 ≤ M := by omega
  let L : ℕ → Allocations := fun n => explicitAllocation s ν (40 * n) (3 * n) M
  have hsmall := Mathathon.P108.BridgeAsymptotic.small_prime_cost_tendsto
    s ν M (by have := hscope.2.1; omega) hM3 L
  have hinner := inner_cost_tendsto hInner s ν M hscope hM
  have houter := outer_cost_tendsto hOuter s ν M hscope hM3 L
  have h := (hsmall.add hinner).add houter
  convert h using 1
  · funext n
    rw [Mathathon.P108.SharpSplit.log_normalizerSharp_split s ν (40 * n) (3 * n) M (L n) hM3]
    dsimp only [L]
    ring
  · congr 1
    simp only [arithmeticPackage, thetaPkg, innerIntegral,
      Mathathon.P108.BridgeAsymptotic.coefficient]
    ring

/-- Adding a fixed energy exponent preserves the literal package limit. -/
theorem explicit_margin_limit_of_normalizer (hLimit : ExplicitNormalizerLimitStatement) :
    ZetaSevenExplicitMarginLimitStatement := by
  intro M hM U
  have h := (hLimit 7 6 M (by norm_num [ParameterScope, Odd, Even]) hM).const_add U
  convert h using 1
  simp only [arithmeticPackage, thetaPkg]
  ring

#print axioms explicit_normalizer_limit_of_ranges
#print axioms explicit_margin_limit_of_normalizer
end
end BNormalizerLimit
