import FiniteProof
import PrimeNumberTheoremAnd.Consequences

/-!
B3 / E404, Codex, lane B, 2026-11-14. PROOF-DRAFT until driver gate.
Exact asymptotic of the small-prime contribution, uniformly in allocations.

Finite estimates are imported from FiniteProof without modification.
PNT is the imported theorem `chebyshev_asymptotic`, not a new assumption.
The prime-sum architecture follows Firsching/Paul-Lez mo271/Zeta5@be1c0d82
Apery/PrimeSum.lean:42-50 and Growth.lean; Apache-2.0 attribution is retained
in the probe. The remainder proof here uses Mathlib's log little-o theorems.
No full-normalizer, other-prime-range, or irrationality claim is made.
-/

open Filter Asymptotics
open scoped Topology

namespace Mathathon.P108.BridgeAsymptotic

noncomputable section

open AperyS.AssemblyTarget Mathathon.P108.BridgeTarget Mathathon.P108.BridgeFinite

def coefficient (s M : ℕ) : ℝ := ((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)) / (M : ℝ)

def degreeArgument (s ν n : ℕ) : ℝ := (degreeBound s ν (40 * n) (3 * n) + 1 : ℕ)

def leading (s M n : ℕ) : ℝ :=
  (((s : ℝ) + 1) * (1 - (3 / 40 : ℝ))) *
    (Chebyshev.theta (((40 * n / M : ℕ) : ℝ)) / ((40 * n : ℕ) : ℝ))

def remainder (s ν n : ℕ) : ℝ :=
  (((s : ℝ) + 1) * 37 / 1600) *
      (((Real.sqrt (degreeArgument s ν n) + 1) * Real.log (degreeArgument s ν n)) / (n : ℝ)) +
    (37 / 1600 : ℝ) *
      ((((s - 1).factorial : ℝ) * Real.log ((s - 1).factorial : ℝ)) / (n : ℝ))

theorem degreeArgument_eq (s ν n : ℕ) (hn : 1 ≤ n) :
    degreeArgument s ν n = (6 * (ν : ℝ) + 148) * (n : ℝ) + (s : ℝ) - 3 := by
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  unfold degreeArgument degreeBound
  rw [hshape]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 37 * n)]
  ring

theorem degreeArgument_atTop (s ν : ℕ) : Tendsto (degreeArgument s ν) atTop atTop := by
  have hc : Tendsto (fun n : ℕ => (6 * (ν : ℝ) + 148) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := tendsto_atTop_add_const_right atTop ((s : ℝ) - 3) hc
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [degreeArgument_eq s ν n hn]
  ring

theorem degreeArgument_div_tendsto (s ν : ℕ) :
    Tendsto (fun n : ℕ => degreeArgument s ν n / (n : ℝ)) atTop (𝓝 (6 * (ν : ℝ) + 148)) := by
  have hzero := tendsto_natCast_atTop_atTop.const_div_atTop ((s : ℝ) - 3)
  have hc : Tendsto (fun _ : ℕ => (6 * (ν : ℝ) + 148)) atTop (𝓝 (6 * (ν : ℝ) + 148)) :=
    tendsto_const_nhds
  have h := hc.add hzero
  have h' : Tendsto (fun n : ℕ => (6 * (ν : ℝ) + 148) + ((s : ℝ) - 3) / (n : ℝ))
      atTop (𝓝 (6 * (ν : ℝ) + 148)) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [degreeArgument_eq s ν n hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

theorem degree_log_remainder_tendsto (s ν : ℕ) :
    Tendsto (fun n : ℕ =>
      (Real.sqrt (degreeArgument s ν n) + 1) * Real.log (degreeArgument s ν n) / (n : ℝ))
      atTop (𝓝 0) := by
  have hd := degreeArgument_atTop s ν
  have hhalf : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hone : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (degreeArgument_div_tendsto s ν).mul ((hhalf.comp hd).add (hone.comp hd))
  have h' : Tendsto (fun n : ℕ => degreeArgument s ν n / (n : ℝ) *
      (Real.log (degreeArgument s ν n) / Real.sqrt (degreeArgument s ν n) +
        Real.log (degreeArgument s ν n) / degreeArgument s ν n)) atTop (𝓝 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hdpos : 0 < degreeArgument s ν n := by unfold degreeArgument; positivity
  have hspos : 0 < Real.sqrt (degreeArgument s ν n) := Real.sqrt_pos.2 hdpos
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsquare := Real.sq_sqrt hdpos.le
  field_simp
  linear_combination -(Real.log (degreeArgument s ν n)) * hsquare

theorem remainder_tendsto (s ν : ℕ) : Tendsto (remainder s ν) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => remainder s ν n) atTop (𝓝 0)
  have h1 := (degree_log_remainder_tendsto s ν).const_mul (((s : ℝ) + 1) * 37 / 1600)
  have h2 := (tendsto_natCast_atTop_atTop.const_div_atTop
    (((s - 1).factorial : ℝ) * Real.log ((s - 1).factorial : ℝ))).const_mul (37 / 1600 : ℝ)
  simpa only [remainder, mul_zero, zero_add] using h1.add h2

theorem theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hnonzero : ∀ᶠ x : ℝ in atTop, (id x : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  exact (isEquivalent_iff_tendsto_one hnonzero).mp chebyshev_asymptotic

theorem theta_shape_ratio_tendsto (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun n : ℕ => Chebyshev.theta (((40 * n / M : ℕ) : ℝ)) /
      ((40 * n : ℕ) : ℝ)) atTop (𝓝 (1 / (M : ℝ))) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hK : Tendsto (fun n : ℕ => ((40 * n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 40 by norm_num)
  have hx : Tendsto (fun n : ℕ => ((40 * n : ℕ) : ℝ) / (M : ℝ)) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hMR).mpr hK
  have h := (theta_ratio_tendsto.comp hx).mul_const (1 / (M : ℝ))
  have h' : Tendsto (fun n : ℕ =>
      (Chebyshev.theta (((40 * n : ℕ) : ℝ) / (M : ℝ)) /
        (((40 * n : ℕ) : ℝ) / (M : ℝ))) * (1 / (M : ℝ))) atTop (𝓝 (1 / (M : ℝ))) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hθ : Chebyshev.theta (((40 * n : ℕ) : ℝ) / (M : ℝ)) =
      Chebyshev.theta (((40 * n / M : ℕ) : ℝ)) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, Nat.floor_div_eq_div]
  rw [hθ]
  have hn0 : ((40 * n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem leading_tendsto (s M : ℕ) (hM : 1 ≤ M) :
    Tendsto (leading s M) atTop (𝓝 (coefficient s M)) := by
  change Tendsto (fun n : ℕ => leading s M n) atTop (𝓝 (coefficient s M))
  have h := (theta_shape_ratio_tendsto M hM).const_mul (((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)))
  simpa only [leading, coefficient, mul_one_div] using h

theorem finite_sandwich (s ν M n : ℕ) (L : Allocations)
    (hs : 3 ≤ s) (hM : 3 ≤ M) (hn : 1 ≤ n) :
    leading s M n ≤ smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
      (((40 * n : ℕ) : ℝ) ^ 2) ∧
    smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
      (((40 * n : ℕ) : ℝ) ^ 2) ≤ leading s M n + remainder s ν n := by
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  have hsupp : 40 * n / M ≤ primeBound s (40 * n) (3 * n) := by
    have hdiv := Nat.div_le_self (40 * n) M
    unfold primeBound
    rw [hshape]
    omega
  have hdeg : 40 * n / M ≤ degreeBound s ν (40 * n) (3 * n) + 1 := by
    have hdiv := Nat.div_le_self (40 * n) M
    unfold degreeBound
    rw [hshape]
    omega
  have hlo := finite_small_prime_lower_full s ν (40 * n) (3 * n) M L (by omega) hsupp hdeg
  have hup := finite_small_prime_statement s ν (40 * n) (3 * n) M L hs (by omega) (by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hK2 : 0 < (((40 * n : ℕ) : ℝ) ^ 2) := by positivity
  have hlo' := div_le_div_of_nonneg_right hlo hK2.le
  have hup' := div_le_div_of_nonneg_right hup hK2.le
  constructor
  · have heq : (((s : ℝ) + 1) * (40 * n - 3 * n : ℕ) *
        Chebyshev.theta (((40 * n / M : ℕ) : ℝ))) / (((40 * n : ℕ) : ℝ) ^ 2) = leading s M n := by
      unfold leading
      rw [hshape]
      push_cast
      field_simp
      ring
    rw [heq] at hlo'
    exact hlo'
  · refine hup'.trans (le_of_eq ?_)
    unfold smallPrimeFiniteEnvelope leading remainder degreeArgument
    rw [hshape]
    push_cast
    field_simp
    ring

theorem eventual_uniform_abs (s ν M : ℕ) (hs : 3 ≤ s) (hM : 3 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ L : Allocations,
      |smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
        (((40 * n : ℕ) : ℝ) ^ 2) - coefficient s M| < ε := by
  have hlead := leading_tendsto s M (by omega)
  have hu : Tendsto (fun n => leading s M n + remainder s ν n) atTop
      (𝓝 (coefficient s M)) := by simpa using hlead.add (remainder_tendsto s ν)
  have helo := hlead.eventually (lt_mem_nhds (show coefficient s M - ε < coefficient s M by linarith))
  have heup := hu.eventually (gt_mem_nhds (show coefficient s M < coefficient s M + ε by linarith))
  filter_upwards [helo, heup, eventually_ge_atTop 1] with n hlo hup hn
  intro L
  obtain ⟨h1, h2⟩ := finite_sandwich s ν M n L hs hM hn
  rw [abs_lt]
  constructor <;> linarith

theorem eventual_small_prime_coefficient_statement : EventualSmallPrimeCoefficientStatement := by
  intro s ν M hs hM ε hε
  filter_upwards [eventual_uniform_abs s ν M hs hM ε hε] with n hn
  intro L
  have h := (abs_lt.mp (hn L)).2
  unfold coefficient at h
  linarith

theorem eventual_small_prime_package_statement : EventualSmallPrimePackageStatement := by
  intro s ν M hs hM ε hε
  filter_upwards [eventual_small_prime_coefficient_statement s ν M hs hM ε hε] with n hn
  intro L U
  have h := hn L
  unfold Mathathon.P108.thetaPkg
  linarith

theorem small_prime_bridge_statement : SmallPrimeBridgeStatement :=
  ⟨finite_small_prime_statement, eventual_small_prime_package_statement⟩

theorem eventual_small_prime_lower (s ν M : ℕ) (hs : 3 ≤ s) (hM : 3 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ L : Allocations,
      coefficient s M - ε ≤ smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
        (((40 * n : ℕ) : ℝ) ^ 2) := by
  filter_upwards [eventual_uniform_abs s ν M hs hM ε hε] with n hn
  intro L
  have h := (abs_lt.mp (hn L)).1
  linarith

theorem small_prime_cost_tendsto (s ν M : ℕ) (hs : 3 ≤ s) (hM : 3 ≤ M)
    (L : ℕ → Allocations) :
    Tendsto (fun n : ℕ => smallPrimeLogContribution s ν (40 * n) (3 * n) M (L n) /
      (((40 * n : ℕ) : ℝ) ^ 2)) atTop (𝓝 (coefficient s M)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_uniform_abs s ν M hs hM ε hε)
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn (L n)⟩

/-- C3 combined statement: the approved finite/package bridge and the exact
limiting coefficient, displayed explicitly. Allocations may vary with n. -/
theorem exact_small_prime_bridge :
    SmallPrimeBridgeStatement ∧
      ∀ (s ν M : ℕ), 3 ≤ s → 3 ≤ M → ∀ L : ℕ → Allocations,
        Tendsto (fun n : ℕ => smallPrimeLogContribution s ν (40 * n) (3 * n) M (L n) /
          (((40 * n : ℕ) : ℝ) ^ 2)) atTop
          (𝓝 (((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)) / (M : ℝ))) := by
  refine ⟨small_prime_bridge_statement, ?_⟩
  intro s ν M hs hM L
  exact small_prime_cost_tendsto s ν M hs hM L

/-- Integrator C3 statement, displaying all required scopes. The universal
finite lower bound retains the range/support/degree minimum; the original
shape has the full matching eventual coefficient. No allocation is fixed. -/
def TwoSidedSmallPrimeBridgeStatement : Prop :=
  FiniteSmallPrimeStatement ∧
  (∀ (s ν K N M : ℕ) (L : Allocations), 1 ≤ M →
    ((s : ℝ) + 1) * (K - N : ℕ) *
      Chebyshev.theta ((min (K / M) (min (primeBound s K N)
        (degreeBound s ν K N + 1)) : ℕ) : ℝ) ≤
      smallPrimeLogContribution s ν K N M L) ∧
  EventualSmallPrimeCoefficientStatement ∧
  EventualSmallPrimePackageStatement ∧
  (∀ (s ν M : ℕ), 3 ≤ s → 3 ≤ M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ L : Allocations,
      ((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)) / (M : ℝ) - ε ≤
        smallPrimeLogContribution s ν (40 * n) (3 * n) M L /
          (((40 * n : ℕ) : ℝ) ^ 2)) ∧
  (∀ (s ν M : ℕ), 3 ≤ s → 3 ≤ M → ∀ L : ℕ → Allocations,
    Tendsto (fun n : ℕ => smallPrimeLogContribution s ν (40 * n) (3 * n) M (L n) /
      (((40 * n : ℕ) : ℝ) ^ 2)) atTop
      (𝓝 (((s : ℝ) + 1) * (1 - (3 / 40 : ℝ)) / (M : ℝ))))

theorem two_sided_small_prime_bridge_statement : TwoSidedSmallPrimeBridgeStatement := by
  refine ⟨finite_small_prime_statement, ?_, eventual_small_prime_coefficient_statement,
    eventual_small_prime_package_statement, ?_, ?_⟩
  · intro s ν K N M L hM
    exact finite_small_prime_lower s ν K N M L hM
  · intro s ν M hs hM ε hε
    exact eventual_small_prime_lower s ν M hs hM ε hε
  · intro s ν M hs hM L
    exact small_prime_cost_tendsto s ν M hs hM L

#print TwoSidedSmallPrimeBridgeStatement
#print axioms eventual_uniform_abs
#print axioms eventual_small_prime_coefficient_statement
#print axioms eventual_small_prime_package_statement
#print axioms small_prime_bridge_statement
#print axioms eventual_small_prime_lower
#print axioms small_prime_cost_tendsto
#print axioms exact_small_prime_bridge
#print axioms two_sided_small_prime_bridge_statement

end
end Mathathon.P108.BridgeAsymptotic
