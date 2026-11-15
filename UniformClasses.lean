import ContinuousClasses

/- E420 Codex inner_explicit. PROOF-DRAFT coefficient bounds for the actual
finite-class comparison. No allocation optimum or rootGamma limit is claimed. -/
open Finset
namespace BInnerExplicit.UniformClasses
noncomputable section
open BInnerExplicit.ClassSums BInnerExplicit.ContinuousClasses

lemma abs_bcoef_le (h : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a : ℕ, a ≤ 2 → |h a| ≤ C) (i : Fin 3) : |bcoef h i| ≤ 2 * C := by
  fin_cases i
  · change |h 0| ≤ 2 * C
    linarith [hbound 0 (by omega)]
  · change |h 1 - h 0| ≤ 2 * C
    exact (abs_sub (h 1) (h 0)).trans (by linarith [hbound 0 (by omega), hbound 1 (by omega)])
  · change |h 2 - h 1| ≤ 2 * C
    exact (abs_sub (h 2) (h 1)).trans (by linarith [hbound 1 (by omega), hbound 2 (by omega)])

lemma sum_abs_bcoef_le (h : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a b : ℕ, a ≤ 2 → b ≤ 2 → |h a b| ≤ C) :
    (∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i|) ≤ 36 * C := by
  have hb (i j : Fin 3) : |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 4 * C := by
    have hc : 0 ≤ 2 * C := by positivity
    have hinner (a : ℕ) (ha : a ≤ 2) : |bcoef (fun b => h a b) j| ≤ 2 * C :=
      abs_bcoef_le (fun b => h a b) C hC (fun b hb => hbound a b ha hb) j
    have := abs_bcoef_le (fun a => bcoef (fun b => h a b) j) (2 * C) hc hinner i
    linarith
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * C :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = 36 * C := by simp; ring

/-- PROOF-DRAFT: table-value bound gives a completely uniform finite Riemann error. -/
theorem finite_class_integral_uniform {p m v v' : ℕ}
    (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a b : ℕ, a ≤ 2 → b ≤ 2 → |h a b| ≤ C) :
    |∑ c ∈ Icc 1 m, h (ClassSums.aCnt p v c) (ClassSums.aCnt p v' c) -
        (p : ℝ) * ∫ z in (0 : ℝ)..(1 / 2),
          h (aCount ((v : ℝ) / p) z) (aCount ((v' : ℝ) / p) z)| ≤ 90 * C := by
  have h1 := finite_class_integral_approx hm hv hv' h
  have h2 := sum_abs_bcoef_le h C hC hbound
  nlinarith

/-- The literal ordinary row polynomial after the exact class dictionary. -/
def rowTable (s ν T qK qN : ℝ) (a b : ℕ) : ℝ :=
  (T - ν / 2 * (2 * qN + b)) *
    (T + ν / 2 * (2 * qN + b) - (2 * qK + a) - s)

/-- PROOF-DRAFT: explicit table bound for fixed s,nu,M on the inner window. -/
theorem rowTable_bound (s ν T qK qN M : ℝ) (hs : 0 ≤ s)
    (hν0 : 0 ≤ ν) (hν10 : ν ≤ 10) (hT0 : 0 ≤ T) (hT : T ≤ 12 * M)
    (hqK0 : 0 ≤ qK) (hqK : qK ≤ M) (hqN0 : 0 ≤ qN) (hqN : qN ≤ M)
    (hM : 0 ≤ M) (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    |rowTable s ν T qK qN a b| ≤ (s + 40 * (M + 1)) ^ 2 := by
  have haR : (a : ℝ) ≤ 2 := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ 2 := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ ν / 2 * (2 * qN + b) := by positivity
  have hbup : ν / 2 * (2 * qN + b) ≤ 10 * M + 10 := by
    have hleft : ν / 2 ≤ 5 := by linarith
    have hright : 2 * qN + (b : ℝ) ≤ 2 * M + 2 := by linarith
    have := mul_le_mul hleft hright (by positivity : 0 ≤ 2 * qN + (b : ℝ)) (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith
  have hA : |T - ν / 2 * (2 * qN + b)| ≤ s + 40 * (M + 1) := by
    rw [abs_le]
    constructor <;> linarith
  have hB : |T + ν / 2 * (2 * qN + b) - (2 * qK + a) - s| ≤ s + 40 * (M + 1) := by
    have ha0 : (0 : ℝ) ≤ a := by positivity
    rw [abs_le]
    constructor <;> linarith
  unfold rowTable
  rw [abs_mul]
  simpa only [pow_two] using mul_le_mul hA hB (abs_nonneg _) (by positivity : 0 ≤ s + 40 * (M + 1))

end
end BInnerExplicit.UniformClasses
