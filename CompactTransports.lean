import TransportGoals
import PriorTailFinal
/-! E246/U51, Codex driver for Ryan, lane U. Every mathematical declaration
has status PROOF-DRAFT until the gate and human comparison. These independent
transport/scalar lemmas do not supply the LocalField certificate or assemble
C's final proof. Overall CONJECTURE. -/
set_option autoImplicit false
noncomputable section
namespace U51
open Real

/-- PROOF-DRAFT: exact C0requested transport, with local leaf and old-threshold order explicit. -/
theorem local_to_enhanced (T : ℝ) : U48.LocalToEnhancedGoal T := by
  intro hLocal hM K t hK ht
  have hK0 : 0<K := by linarith
  rcases le_or_gt t 2 with h|h
  · have hf := hLocal t ht h
    have hs : Real.sqrt t≤3/2 := by
      rw [Real.sqrt_le_iff]
      constructor <;> [norm_num;nlinarith]
    have hc : 2/K*Real.sqrt t≤3/K := by
      rw [show 3/K=2/K*(3/2) by ring]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    exact add_le_add hf hc
  · have hf := U51.Prior.potential_ineq_tail' (c:=2/K) h.le (by positivity)
      (by rw [div_le_iff₀ hK0];linarith)
    have hc : 0≤3/K := by positivity
    exact hf.trans (hM.trans (le_add_of_nonneg_right hc))

/-- PROOF-DRAFT: specialization leaves precisely the new local certificate as a premise. -/
theorem local_tau_to_enhanced :
    U48.LocalFieldStatement ((-1323:ℝ)/200) →
      U48.EnhancedFieldStatement ((-1323:ℝ)/200) := by
  intro h
  exact local_to_enhanced _ h (by norm_num [Apery.M0])

/-- PROOF-DRAFT: reuse the actual old scalar certificate without any old pointwise field table. -/
theorem scalar_budget_transport (T : ℝ) :
    U48.ScalarBudgetStatement T ((Apery.U:ℝ)+Apery.lam*(T-Apery.M0)) := by
  unfold U48.ScalarBudgetStatement
  calc
    Apery.lam*T-Apery.Irho+Apery.Cstar=
        (Apery.lam*Apery.M0-Apery.Irho+Apery.Cstar)+Apery.lam*(T-Apery.M0) := by ring
    _≤_ := add_le_add Apery.energy_const le_rfl

/-- PROOF-DRAFT: the exact C0scalar-budget proposition. -/
theorem scalar_budget_tau : U48.Original16ScalarBudgetGoal :=
  scalar_budget_transport U48.tau

/-- PROOF-DRAFT: the new leading constant has exactly the literal rational requested by C0. -/
theorem unew_eq_literal : U48.Unew=(-2678491:ℝ)/2000000 := by
  norm_num [U48.Unew,U48.tau,Apery.U,Apery.lam,Apery.M0]

/-- PROOF-DRAFT: actual same-measure energy coefficient with the literal new tau and upper bound. -/
theorem scalar_budget_literal :
    Apery.lam*((-1323:ℝ)/200)-Apery.Irho+Apery.Cstar≤(-2678491:ℝ)/2000000 := by
  have h := scalar_budget_tau
  change Apery.lam*U48.tau-Apery.Irho+Apery.Cstar≤U48.Unew at h
  rw [unew_eq_literal] at h
  simpa [U48.tau] using h

end U51
#print axioms U51.Prior.potential_ineq_tail'
#print axioms U51.local_to_enhanced
#print axioms U51.local_tau_to_enhanced
#print axioms U51.scalar_budget_transport
#print axioms U51.scalar_budget_tau
#print axioms U51.unew_eq_literal
#print axioms U51.scalar_budget_literal
