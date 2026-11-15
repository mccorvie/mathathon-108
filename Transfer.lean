import PriorPrime

/-!
E421, lane B driver. PROOF-DRAFT until parent gate.
Adapted from PRIOR Deicyde/zeta7-irrational@be55b3a4,
ZetaSeven/PrimeSumBound.lean:153-241. The new interface is uniform over an
arbitrary supplied parameter family; all regularity hypotheses remain explicit.
No new mathematical result or actual outer/inner identification is claimed.
-/

open Filter Topology MeasureTheory

namespace BPrimeTransfer
noncomputable section

def K (n : ℕ) : ℕ := 40 * n

theorem K_pos {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < K n := by
  unfold K
  positivity

theorem tendsto_K_atTop : Tendsto (fun n : ℕ => (K n : ℝ)) atTop atTop := by
  simpa only [K, Nat.cast_mul, Nat.cast_ofNat] using
    tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 40 by norm_num)

def weightedSum (a b : ℝ) (w : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
    w n p * Real.log p) / (K n : ℝ) ^ 2

theorem abs_sum_prime_le {a b : ℕ} {f : ℕ → ℝ} {C x : ℝ}
    (hb : b = ⌊x⌋₊) (hC : 0 ≤ C)
    (hf : ∀ p ∈ Finset.Ioc a b, p.Prime → |f p| ≤ C) :
    |∑ p ∈ Finset.Ioc a b with p.Prime, f p * Real.log p| ≤
      C * Chebyshev.theta x := by
  calc
    |∑ p ∈ Finset.Ioc a b with p.Prime, f p * Real.log p|
        ≤ ∑ p ∈ Finset.Ioc a b with p.Prime, |f p * Real.log p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Ioc a b with p.Prime, C * Real.log p := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
      rw [abs_mul, abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_right (hf p hp.1 hp.2) hl
    _ ≤ ∑ p ∈ Finset.Ioc 0 b with p.Prime, C * Real.log p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
      · intro p hp _
        rw [Finset.mem_filter] at hp
        exact mul_nonneg hC (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
    _ = C * Chebyshev.theta x := by
      rw [← Finset.mul_sum]
      unfold Chebyshev.theta
      rw [← hb]

theorem weighted_sum_error {a b : ℝ} (hb : 0 < b) {G : ℝ → ℝ}
    (w : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hw : ∀ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊, p.Prime →
      |w n p - (K n : ℝ) * G ((p : ℝ) / K n)| ≤ C) :
    |weightedSum a b w n - (K n : ℝ)⁻¹ *
      ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
        G ((p : ℝ) / K n) * Real.log p| ≤
      C * Real.log 4 * b * (K n : ℝ)⁻¹ := by
  have hK := K_pos hn
  have hXX : (K n : ℝ) * (K n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  have hsplit : weightedSum a b w n - (K n : ℝ)⁻¹ *
      ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
        G ((p : ℝ) / K n) * Real.log p =
      (∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
        (w n p - (K n : ℝ) * G ((p : ℝ) / K n)) * Real.log p) /
          (K n : ℝ) ^ 2 := by
    unfold weightedSum
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    linear_combination (G ((p : ℝ) / K n) * Real.log p * (K n : ℝ)⁻¹) * hXX
  have hsum := abs_sum_prime_le (x := b * K n) rfl hC hw
  have hθ := Chebyshev.theta_le_log4_mul_x (mul_nonneg hb.le (Nat.cast_nonneg (K n)))
  have hK2 : (0 : ℝ) < (K n : ℝ) ^ 2 := pow_pos hK 2
  rw [hsplit, abs_div, abs_of_pos hK2]
  calc
    _ ≤ C * Chebyshev.theta (b * K n) / (K n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum hK2.le
    _ ≤ C * (Real.log 4 * (b * K n)) / (K n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hC) hK2.le
    _ = C * Real.log 4 * b * (K n : ℝ)⁻¹ := by
      linear_combination (C * Real.log 4 * b * (K n : ℝ)⁻¹) * hXX

/-- PROOF-DRAFT: uniform over arbitrary allocation/cutoff parameter families. -/
theorem uniform_weighted_prime_limit {ι : Type*} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {G : ℝ → ℝ}
    (hG : ∃ C, ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite)
    (w : ℕ → ι → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ᶠ n : ℕ in atTop, ∀ i p,
      p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ → p.Prime →
        |w n i p - (K n : ℝ) * G ((p : ℝ) / K n)| ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ i,
      |weightedSum a b (fun n p => w n i p) n - (∫ y in a..b, G y)| ≤ ε := by
  have hb : 0 < b := ha.trans hab
  have hRS := (BPriorPrime.tendsto_primeRiemannSum ha hab hG hGc).comp tendsto_K_atTop
  have he : Tendsto (fun n : ℕ => C * Real.log 4 * b * (K n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_K_atTop).const_mul (C * Real.log 4 * b)
    simpa only [mul_zero, Function.comp_apply] using h
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hRS' := (Metric.tendsto_nhds.mp hRS) (ε / 2) hhalf
  have he' := he.eventually_lt_const hhalf
  filter_upwards [hw, eventually_ge_atTop 1, hRS', he'] with n hwn hn hmodel herr
  intro i
  rw [Real.dist_eq] at hmodel
  dsimp only [Function.comp_apply] at hmodel
  have herror := weighted_sum_error hb (fun n p => w n i p) hC hn
    (fun p hp hpp => hwn i p hp hpp)
  calc
    _ ≤ |weightedSum a b (fun n p => w n i p) n - (K n : ℝ)⁻¹ *
          ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
            G ((p : ℝ) / K n) * Real.log p| +
        |(K n : ℝ)⁻¹ *
          ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
            G ((p : ℝ) / K n) * Real.log p - (∫ y in a..b, G y)| :=
      abs_sub_le _ _ _
    _ ≤ ε := by linarith

#print axioms uniform_weighted_prime_limit
#print axioms weighted_sum_error
end
end BPrimeTransfer
