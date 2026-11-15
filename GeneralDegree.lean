import Zeta5S.SmallPrimeF

/-!
E436, Codex gpt-6.1-sol, lane B, 2026-11-14. PROOF-DRAFT until parent gate.
Uniform degree upper bounds for the actual general-s family, with no parameter
hypotheses. The generic determinant helper body below is copied verbatim from
Firsching/Paul-Lez, mo271/Zeta5@be1c0d82, Apery/Degree.lean:16-34,
Apache-2.0; only its namespace is changed to prevent a later C import collision.
The affine-functional proof uses the existing lane-L definitions
poleValueS/μXS/GS/ΔS/FS, credited in their unchanged imported source files.
No exact-degree, Vandermonde nonvanishing, analytic or irrationality claim.
-/
set_option autoImplicit false
open Polynomial Matrix Finset

namespace BSymbolicCriterion.DegreeHelpers

lemma coeff_det_of_natDegree_le_one {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (M.det).coeff n = (Matrix.of fun i j => (M i j).coeff 1).det ∧ M.det.natDegree ≤ n := by
  constructor
  · rw [det_apply', det_apply', finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hc := coeff_prod_of_natDegree_le (s := Finset.univ) (f := fun i => M (σ i) i) (n := 1)
      (fun i _ => hM _ _)
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hc
    rw [← C_eq_intCast, coeff_C_mul, hc]
    simp
  · rw [det_apply']
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_intCast, zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i : Fin n, (M (σ i) i).natDegree ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp

end BSymbolicCriterion.DegreeHelpers

namespace AperyS

lemma natDegree_poleValueS_le (s j : ℕ) : (poleValueS s j).natDegree ≤ 1 := by
  unfold poleValueS
  compute_degree!

lemma natDegree_μXS_le (s K : ℕ) (P : ℚ[X]) : (μXS s K P).natDegree ≤ 1 := by
  unfold μXS
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine natDegree_mul_le.trans ?_
    simpa only [natDegree_C, zero_add] using natDegree_poleValueS_le s j

lemma natDegree_ΔS_le (s ν K N h : ℕ) : (ΔS s ν K N h).natDegree ≤ h := by
  exact (BSymbolicCriterion.DegreeHelpers.coeff_det_of_natDegree_le_one (GS s ν K N h)
    (fun _ _ => natDegree_μXS_le s K _)).2

lemma natDegree_FS_le (s ν K N h : ℕ) : (FS s ν K N h).natDegree ≤ h := by
  unfold FS
  refine natDegree_mul_le.trans ?_
  simpa only [natDegree_C, zero_add] using natDegree_ΔS_le s ν K N h

end AperyS

namespace BSymbolicCriterion

/-- The raw actual-FS form is definitionally the statement-alias `F` form. -/
theorem degree_bound (s ν n : ℕ) :
    (AperyS.FS s ν (40 * n) (3 * n) (37 * n)).natDegree ≤ 37 * n :=
  AperyS.natDegree_FS_le s ν (40 * n) (3 * n) (37 * n)

#check degree_bound
#print axioms degree_bound
#print axioms AperyS.natDegree_μXS_le
#print axioms AperyS.natDegree_ΔS_le
#print axioms AperyS.natDegree_FS_le

end BSymbolicCriterion
