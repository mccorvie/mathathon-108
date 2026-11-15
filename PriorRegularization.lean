import Apery.EnergyRaw
/-! CITED prior declarations copied byte-exact from Moritz Firsching, mo271/Zeta5@be1c0d82 Apery/EnergyFinal.lean20-87 and130-155. Paul-Lez: Comparator metadata. Apache-2.0. Supporting status PROOF-DRAFT, overall CONJECTURE. -/
open MeasureTheory Set Real Filter Topology Finset
open Apery
namespace U51.Prior
lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The regularisation error at one interval. -/
lemma errj_le {ε t m r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hm : 0 < m ∧ m < 2)
    (hr : 1 / 450 ≤ r) :
    errj ε t m r ≤ Real.sqrt ε * (637 * Real.sqrt t + 1457) := by
  unfold errj
  have hr0 : 0 < r := by linarith
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hεs : ε ≤ Real.sqrt ε := by
    rw [Real.le_sqrt hε.le hε.le]; nlinarith
  have h1 : ε / r ≤ 450 * ε := by rw [div_le_iff₀ hr0]; nlinarith
  have habs : |t - m| ≤ t + 2 := by rw [abs_le]; constructor <;> linarith
  have h2 : ε / r * ((ε + 2 * |t - m|) / r) ≤ 450 ^ 2 * ε * (2 * t + 5) := by
    have : (ε + 2 * |t - m|) / r ≤ 450 * (2 * t + 5) := by
      rw [div_le_iff₀ hr0]; nlinarith
    calc ε / r * ((ε + 2 * |t - m|) / r) ≤ (450 * ε) * (450 * (2 * t + 5)) :=
          mul_le_mul h1 this (by positivity) (by positivity)
      _ = 450 ^ 2 * ε * (2 * t + 5) := by ring
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hs5 : Real.sqrt 5 ≤ 22361 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have h3 : Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r)) ≤
      450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
    calc Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r))
        ≤ Real.sqrt (450 ^ 2 * ε * (2 * t + 5)) := Real.sqrt_le_sqrt h2
      _ = 450 * Real.sqrt ε * Real.sqrt (2 * t + 5) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
      _ ≤ 450 * Real.sqrt ε * (Real.sqrt (2 * t) + Real.sqrt 5) := by
          apply mul_le_mul_of_nonneg_left (sqrt_add_le' (by positivity) (by norm_num))
          positivity
      _ ≤ 450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Real.sqrt_mul (by norm_num)]
          have := mul_le_mul_of_nonneg_right hs2 hst
          linarith
  nlinarith

/-- The total mass of the sixteen weights. -/
lemma sum_cρ_fin : ∑ j : Fin 16, cρ (j + 1) = lam := by
  rw [← Sρ_sixteen, Sρ, sum_Icc_eq_sum_range', Fin.sum_univ_eq_sum_range (fun j => cρ (j + 1))]

/-- The total regularisation error. -/
lemma Err_le {ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) :
    Err ε t ≤ Real.sqrt ε * (590 * Real.sqrt t + 1348) := by
  unfold Err
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc ∑ j : Fin 16, cρ (j + 1) * errj ε t (mρ (j + 1)) (rρ (j + 1))
      ≤ ∑ j : Fin 16, cρ (j + 1) * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (errj_le hε hε1 ht (mρ_bounds j) (rρ_ge j))
          (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
    _ = lam * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by
        rw [← Finset.sum_mul, sum_cρ_fin]
    _ ≤ _ := by
        simp only [lam]
        nlinarith

lemma sum_pairs_eq {h : ℕ} (t : Fin h → ℝ) :
    ∑ i, ∑ i', Real.log |t i - t i'| = ∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i| := by
  have hsplit : ∀ i : Fin h, ∑ i', Real.log |t i - t i'| =
      ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| + ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    intro i
    have e1 : (Finset.univ : Finset (Fin h)).filter (fun x => x < i) = Finset.Iio i := by
      ext x; simp
    have e2 : (Finset.univ : Finset (Fin h)).filter (fun x => ¬ x < i) = Finset.Ici i := by
      ext x; simp [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x < i), e1, e2,
      ← Finset.add_sum_Ioi_eq_sum_Ici, sub_self, abs_zero, Real.log_zero, zero_add]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hcomm : ∑ i, ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| =
      ∑ i, ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i' => Finset.Ioi i')]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [abs_sub_comm]
    · intro x y
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [hcomm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_sub_comm]; ring


end U51.Prior
