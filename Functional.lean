import FunctionalStatement
import PartialFractions

/-!
B9/E411: actual functional/moment interface, Codex lane B. PROOF-DRAFT until gate.
Adapted from mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/Positivity.lean:50-115, Firsching/Paul-Lez, Apache-2.0 (NOTICE/LICENSE).
s=5 replaced by every natural s>=2 using the proved actual B6/B8 moment identities.
No determinant positivity or energy inequality is claimed here.
-/
open MeasureTheory Set Filter Topology Polynomial Finset AperyS
namespace BAnalyticFunctional

-- Generalizes upstream Positivity.lean:54-67; actual polynomial/density definitions retained.
lemma integrand_eq_sum (s K : ℕ) (P : ℚ[X]) {y : ℝ} (hy : 0 < y) :
    integrand s K P y =
      (∑ e ∈ range ((P /ₘ D K).natDegree + 1),
          ((P /ₘ D K).coeff e : ℝ) * (y ^ (2 * e) * BAnalyticMoments.w s y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) *
          (BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2)) := by
  unfold integrand
  rw [partial_fractions K P (t := y ^ 2) (by positivity), aeval_eq_sum_range, add_mul,
    Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    try simp only [Rat.smul_def, ← pow_mul]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

-- Generalizes upstream Positivity.lean:70-84, retaining pole evaluations rather than expanding them.
lemma aeval_μXS (s K : ℕ) (P : ℚ[X]) :
    aeval (BAnalyticPoles.zetaS s) (μXS s K P) =
      (∑ e ∈ range ((P /ₘ D K).natDegree + 1),
        ((P /ₘ D K).coeff e : ℝ) * (μmonoS s e : ℝ)) +
      ∑ j ∈ Icc 1 K, (res K P j : ℝ) *
        aeval (BAnalyticPoles.zetaS s) (poleValueS s j) := by
  simp only [μXS, map_add, aeval_C, map_sum, map_mul, eq_ratCast]
  congr 1
  · unfold μpolyS
    rw [Polynomial.sum_over_range' _ (fun n => by simp) _ (Nat.lt_succ_self _)]
    push_cast
    rfl

/-- Moment representation of the actual rational functional at the actual zeta sum,
with integrability proved for all natural s>=2, arbitrary K and P. -/
theorem moment_rep (s : ℕ) (hs : 2 ≤ s) (K : ℕ) (P : ℚ[X]) :
    IntegrableOn (integrand s K P) (Ioi 0) ∧
      aeval (BAnalyticPoles.zetaS s) (μXS s K P) = ∫ y in Ioi 0, integrand s K P y := by
  set Q := P /ₘ D K with hQ
  have hint1 : ∀ e ∈ range (Q.natDegree + 1),
      IntegrableOn (fun y => (Q.coeff e : ℝ) * (y ^ (2 * e) * BAnalyticMoments.w s y)) (Ioi 0) :=
    fun e _ => (BAnalyticMoments.mono_moment s hs e).1.const_mul _
  have hint2 : ∀ j ∈ Finset.Icc 1 K,
      IntegrableOn (fun y => (res K P j : ℝ) *
        (BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) :=
    fun j hj => (BAnalyticPoles.integrableOn_pole s hs
      (by exact_mod_cast (Finset.mem_Icc.mp hj).1 : (0 : ℝ) < j)).const_mul _
  have hsumint : IntegrableOn (fun y =>
      (∑ e ∈ range (Q.natDegree + 1), (Q.coeff e : ℝ) * (y ^ (2 * e) * BAnalyticMoments.w s y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) *
          (BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) :=
    (integrable_finsetSum _ hint1).add (integrable_finsetSum _ hint2)
  have hEq : EqOn (fun y =>
      (∑ e ∈ range (Q.natDegree + 1), (Q.coeff e : ℝ) * (y ^ (2 * e) * BAnalyticMoments.w s y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) *
          (BAnalyticMoments.w s y / (y ^ 2 + (j : ℝ) ^ 2))) (integrand s K P) (Ioi 0) :=
    fun y hy => (integrand_eq_sum s K P hy).symm
  refine ⟨hsumint.congr_fun hEq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hEq, integral_add (integrable_finsetSum _ hint1)
    (integrable_finsetSum _ hint2), integral_finsetSum _ hint1, integral_finsetSum _ hint2,
    aeval_μXS]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_const_mul, (BAnalyticMoments.mono_moment s hs e).2]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, BAnalyticPoles.pole_identity s hs j (Finset.mem_Icc.mp hj).1]

/-- The exact posted interface target. -/
theorem functional_statement : FunctionalStatement := by
  intro s hs K P
  exact moment_rep s hs K P

#print axioms BAnalyticFunctional.integrand_eq_sum
#print axioms BAnalyticFunctional.aeval_μXS
#print axioms BAnalyticFunctional.moment_rep
#print axioms BAnalyticFunctional.functional_statement
end BAnalyticFunctional
