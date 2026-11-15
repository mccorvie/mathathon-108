import MeshCounts

/- E420 Codex inner_explicit. PROOF-DRAFT exact finite ordinary row counts.
The erase-to-Icc architecture follows Apache Zeta5 Growth/InnerPrime20-28;
the count identities below are written here against actual AperyS.SX.
-/
open Finset
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108.RangeBridgeTarget

lemma sum_aCnt {p m r : ℕ} (hm : 2 * m + 1 = p) (hr : r < p) :
    (∑ c ∈ Icc 1 m, aCnt p r c) = r := by
  have hA : (∑ c ∈ Icc 1 m, if c ≤ r then (1 : ℕ) else 0) = min m r := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    have hset : (Icc 1 m).filter (fun c => c ≤ r) = Icc 1 (min m r) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
      tauto
    rw [hset, Nat.card_Icc]
    simp
  have hB : (∑ c ∈ Icc 1 m, if p - r ≤ c then (1 : ℕ) else 0) = m + 1 - (p - r) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    have hset : (Icc 1 m).filter (fun c => p - r ≤ c) = Icc (p - r) m := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hset, Nat.card_Icc]
    simp
  unfold aCnt
  rw [Finset.sum_add_distrib, hA, hB]
  omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: every positive nonzero residue lies in exactly one ordinary class. -/
lemma sum_SX_Icc (X : ℕ) (hodd : 2 * (p / 2) + 1 = p) :
    (∑ c ∈ Icc 1 (p / 2), SX p X (((c : ℕ) : ℤ) : ZMod p)) = X - X / p := by
  have hsum : (∑ c ∈ Icc 1 (p / 2), SX p X (((c : ℕ) : ℤ) : ZMod p)) =
      (p / 2) * (2 * (X / p)) + X % p := by
    rw [Finset.sum_congr rfl (fun c hc => SX_class hodd (Finset.mem_Icc.mp hc).1
      (Finset.mem_Icc.mp hc).2 X), Finset.sum_add_distrib]
    rw [sum_aCnt hodd (Nat.mod_lt X hp.out.pos)]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
  rw [hsum]
  have hdiv := Nat.div_add_mod X p
  have hmul := congrArg (fun t : ℕ => t * (X / p)) hodd
  have heq : p / 2 * (2 * (X / p)) + X % p + X / p = X := by nlinarith
  omega

lemma sum_erase_zero_eq_Icc_nat {m : ℕ} (F : ℕ → ℕ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), Finset.sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero, Finset.sum_range_one] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by
    ext c
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h2] at h1
  omega

/-- PROOF-DRAFT: the exact erased-Fin ordinary count sum, in the allocation index type. -/
lemma sum_SX_ordinary (X : ℕ) (hodd : 2 * (p / 2) + 1 = p) :
    (∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      SX p X (((c : ℕ) : ℤ) : ZMod p)) = X - X / p := by
  rw [sum_erase_zero_eq_Icc_nat (fun c => SX p X (((c : ℕ) : ℤ) : ZMod p))]
  exact sum_SX_Icc X hodd

/-- PROOF-DRAFT: exact base-layer row count at the model level for even nu=2r. -/
theorem rowsK_model_base (s r K N : ℕ) (T : ℤ)
    (hodd : 2 * (p / 2) + 1 = p)
    (hTb : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ T) :
    (rowsK (beta s (2 * r) K N p) (2 * T - ⌊2 * ((K : ℝ) / p)⌋ - s) : ℚ) =
      ((p / 2 : ℕ) : ℚ) * T - (r : ℚ) * ((N - N / p : ℕ) : ℚ) := by
  let q : ℤ := ⌊2 * ((K : ℝ) / p)⌋
  have hrow (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
      (lrow (2 * T - q - s) (beta s (2 * r) K N p c) : ℚ) =
        (T : ℚ) - (r : ℚ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℚ) := by
    have hβ : beta s (2 * r) K N p c =
        2 * ((r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ)) -
          (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) - s + 1 := by
      unfold beta
      push_cast
      ring
    rw [hβ, lrow_model_level T _ q s _ (hTb c hc) (SX_two_values K hodd c hc)]
    have hInt : ((T - (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ)).toNat : ℤ) =
        T - (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) :=
      Int.toNat_of_nonneg (by linarith [hTb c hc])
    exact_mod_cast hInt
  unfold rowsK
  rw [Nat.cast_sum]
  calc
    _ = ∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
        ((T : ℚ) - (r : ℚ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℚ)) := by
      exact Finset.sum_congr rfl fun c hc => hrow c (Finset.mem_erase.mp hc).1
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
      have hcard : ((univ : Finset (Fin (p / 2 + 1))).erase 0).card = p / 2 := by simp
      rw [hcard, ← Nat.cast_sum, sum_SX_ordinary N hodd]
      rfl

/-- PROOF-DRAFT: two level increments add exactly one row per ordinary class. -/
theorem rowsK_model_plus_two (s r K N : ℕ) (T : ℤ)
    (hodd : 2 * (p / 2) + 1 = p)
    (hTb : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ T) :
    (rowsK (beta s (2 * r) K N p) (2 * T - ⌊2 * ((K : ℝ) / p)⌋ - s + 2) : ℚ) =
      (rowsK (beta s (2 * r) K N p) (2 * T - ⌊2 * ((K : ℝ) / p)⌋ - s) : ℚ) + (p / 2 : ℕ) := by
  have hTb' : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      (r : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ T + 1 := by
    intro c hc
    linarith [hTb c hc]
  rw [show 2 * T - ⌊2 * ((K : ℝ) / p)⌋ - (s : ℤ) + 2 =
    2 * (T + 1) - ⌊2 * ((K : ℝ) / p)⌋ - s by ring,
    rowsK_model_base s r K N (T + 1) hodd hTb', rowsK_model_base s r K N T hodd hTb]
  push_cast
  ring

end
end BInnerExplicit
