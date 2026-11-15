import Classes

/- E420, native Codex inner_explicit. PROOF-DRAFT helper development only. -/
open Finset
namespace BInnerExplicit
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget

/-- PROOF-DRAFT: literal ordinary offset identity; no model replacement. -/
lemma Bse_eq_beta (s ν K N p : ℕ) (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    BseS s ν p K N (c : ℕ) = (beta s ν K N p c : ℚ) + ((s : ℚ) - 1) := by
  have hc0 : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
  unfold BseS beta
  rw [if_neg hc0]
  push_cast
  ring

variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: uniform finite class-count bound on the fixed inner window. -/
lemma SX_le_two_mul_cutoff {K X M : ℕ} (hodd : 2 * (p / 2) + 1 = p)
    (hX : X ≤ K) (hKM : K < p * M) (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) ≤ 2 * M := by
  have hc1 : 1 ≤ (c : ℕ) := by
    have : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
    omega
  have hq : X / p < M :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith)
  rw [SX_class hodd hc1 (by omega)]
  unfold aCnt
  split_ifs <;> omega

/-- PROOF-DRAFT: both actual ordinary offsets are bounded independently of K. -/
lemma beta_bounds {s ν K N M : ℕ} (hodd : 2 * (p / 2) + 1 = p)
    (hNK : N ≤ K) (hKM : K < p * M) (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    -(2 * (M : ℤ)) - s + 1 ≤ beta s ν K N p c ∧
      beta s ν K N p c ≤ 2 * (ν : ℤ) * M - s + 1 := by
  have hK := SX_le_two_mul_cutoff hodd (le_refl K) hKM c hc
  have hN := SX_le_two_mul_cutoff hodd hNK hKM c hc
  have hN0 : (0 : ℤ) ≤ (ν : ℤ) * (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) := by positivity
  have hKN : (0 : ℤ) ≤ (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) := by positivity
  have hK' : (SX p K (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ 2 * M := by exact_mod_cast hK
  have hN' : (SX p N (((c : ℕ) : ℤ) : ZMod p) : ℤ) ≤ 2 * M := by exact_mod_cast hN
  have hNν := mul_le_mul_of_nonneg_left hN' (show (0 : ℤ) ≤ ν by positivity)
  unfold beta
  constructor <;> nlinarith

/-- PROOF-DRAFT: the posted reserve dominates all negative ordinary offsets. -/
lemma budget_ge_low (s ν M : ℕ) : s + 2 * M ≤ fillBudget s ν M := by
  unfold fillBudget
  nlinarith [Nat.zero_le (s * M), Nat.zero_le (ν * M)]

/-- PROOF-DRAFT: the posted reserve also dominates the positive offsets. -/
lemma budget_ge_high (s ν M : ℕ) : 2 * ν * M ≤ fillBudget s ν M := by
  unfold fillBudget
  nlinarith [Nat.zero_le (s * M), Nat.zero_le (ν * M)]

/-- PROOF-DRAFT: a reserve bound used in the exact zero-class flag. -/
lemma budget_ge_base (s ν M : ℕ) : 4 * (M + 1) ≤ fillBudget s ν M := by
  unfold fillBudget
  nlinarith [Nat.zero_le (s * M), Nat.zero_le (ν * M)]

/-- PROOF-DRAFT: actual search-window lower endpoint uses zero ordinary rows. -/
lemma rowsK_lower_eq_zero {s ν K N M : ℕ} (hodd : 2 * (p / 2) + 1 = p)
    (hNK : N ≤ K) (hKM : K < p * M) :
    rowsK (beta s ν K N p) (-(fillBudget s ν M : ℤ)) = 0 := by
  unfold rowsK
  refine Finset.sum_eq_zero fun c hc => ?_
  have hb := (beta_bounds (s := s) (ν := ν) hodd hNK hKM c (Finset.mem_erase.mp hc).1).1
  have hB : (s : ℤ) + 2 * M ≤ fillBudget s ν M := by exact_mod_cast budget_ge_low s ν M
  unfold lrow
  omega

/-- PROOF-DRAFT: literal explicit allocation has the correct row sum and
at least its posted zero-class reserve, as soon as that reserve fits. -/
lemma explicit_row_sum_and_reserve {s ν K N M : ℕ}
    (hodd : 2 * (p / 2) + 1 = p) (hNK : N ≤ K) (hKM : K < p * M)
    (hB : fillBudget s ν M ≤ K - N) :
    (∑ c, explicitAllocation s ν K N M p c) = K - N ∧
      fillBudget s ν M ≤ explicitAllocation s ν K N M p 0 := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let kf := kfSel β (K - N) B lo hi
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas : rowsK β kf + B ≤ K - N := kfSel_feasible β (K - N) B lo hi hlo
  change (∑ c, allocK β (K - N) kf c) = K - N ∧ B ≤ allocK β (K - N) kf 0
  constructor
  · exact sum_allocK β (K - N) kf (by omega)
  · unfold allocK
    rw [if_pos rfl]
    omega

/-- PROOF-DRAFT: the actual zero-class source offset is independent of s. -/
lemma Bse_zero_offset (s ν K N : ℕ) :
    BseS s ν p K N 0 - ((s : ℚ) - 1) =
      1 + 2 * ν * ((N / p : ℕ) : ℚ) - 2 * ((K / p : ℕ) : ℚ) := by
  unfold BseS
  simp only [if_pos, Nat.cast_zero, Int.cast_zero]
  rw [SX_zero, SX_zero]
  push_cast
  ring

/-- PROOF-DRAFT: explicit reserve proves the literal zero-top InnerOK flag. -/
lemma explicit_zero_condition {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hm1 : 1 ≤ p / 2)
    (hNK : N ≤ K) (hKM : K < p * M) (hB : fillBudget s ν M ≤ K - N) :
    tminS ((s : ℚ) - 1) hm1 (explicitAllocation s ν K N M p) (BseS s ν p K N) ≤
      2 * (explicitAllocation s ν K N M p 0 : ℚ) +
        (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2 := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let kf := kfSel β (K - N) B lo hi
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      BseS s ν p K N (c : ℕ) = (β c : ℚ) + ((s : ℚ) - 1) :=
    fun c hc => Bse_eq_beta s ν K N p c hc
  have htop := tmin_allocK_leS ((s : ℚ) - 1) hm1 (BseS s ν p K N) β hβ (K - N) kf
  have hkf : kf ≤ hi := kfSel_le β (K - N) B lo hi (by dsimp [lo, hi]; omega)
  have hkfQ : (kf : ℚ) ≤ (B : ℚ) + 4 * M + 4 := by
    have := (Int.cast_le (R := ℚ)).mpr hkf
    simpa [hi] using this
  have hL0 : (B : ℚ) ≤ (explicitAllocation s ν K N M p 0 : ℚ) := by
    exact_mod_cast (explicit_row_sum_and_reserve hodd hNK hKM hB).2
  have hb1 : (β ⟨1, by omega⟩ : ℚ) ≤ B := by
    have hb := (beta_bounds (s := s) (ν := ν) hodd hNK hKM (⟨1, by omega⟩ : Fin (p / 2 + 1))
      (by simp [Fin.ext_iff])).2
    have hBd : (2 : ℤ) * ν * M ≤ B := by exact_mod_cast budget_ge_high s ν M
    have : β ⟨1, by omega⟩ ≤ (B : ℤ) := by dsimp [β]; omega
    exact_mod_cast this
  have hq : K / p < M := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith)
  have hqQ : ((K / p : ℕ) : ℚ) ≤ M := by exact_mod_cast hq.le
  have hBbase : 4 * ((M : ℚ) + 1) ≤ B := by exact_mod_cast budget_ge_base s ν M
  have hbzero : (1 : ℚ) - 2 * M ≤ BseS s ν p K N 0 - ((s : ℚ) - 1) := by
    rw [Bse_zero_offset]
    have hN0 : (0 : ℚ) ≤ 2 * ν * ((N / p : ℕ) : ℚ) := by positivity
    linarith
  change tminS ((s : ℚ) - 1) hm1 (allocK β (K - N) kf) (BseS s ν p K N) ≤ _
  refine htop.trans ?_
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
  apply max_le <;> linarith

/-- PROOF-DRAFT: all allocation-dependent InnerOK conditions are conclusions.
Only the explicit finite structural inequalities are supplied here; the next
fixed-shape lemma discharges them eventually. -/
lemma explicit_innerOK_of_structural {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hm1 : 1 ≤ p / 2) (hsp : s ≤ p)
    (hNK : N ≤ K) (hKM : K < p * M) (hB : fillBudget s ν M ≤ K - N)
    (hsep : 2 * K < p ^ 2)
    (hdeg : s + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2) :
    InnerOK s ν K N p (explicitAllocation s ν K N M) := by
  refine ⟨hodd, hm1, hsp, Sep_PlK hsep, by nlinarith, hdeg, ?_, ?_⟩
  · exact (explicit_row_sum_and_reserve hodd hNK hKM hB).1
  · exact explicit_zero_condition hs hodd hm1 hNK hKM hB

/-- PROOF-DRAFT: explicit finite threshold discharges every InnerOK condition.
No selected-branch validity is assumed. The crude threshold is not optimized. -/
theorem explicit_innerOK_fixed_shape (s ν M n p : ℕ)
    (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M)
    (hn : fillBudget s ν M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hp : p.Prime) (hKM : 40 * n < p * M) :
    InnerOK s ν (40 * n) (3 * n) p
      (explicitAllocation s ν (40 * n) (3 * n) M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have hnM : M ^ 2 ≤ n := by
    nlinarith [Nat.zero_le (s * M)]
  have hnSM : s * M ≤ n := by
    nlinarith [Nat.zero_le (s * M)]
  have hns : s ≤ n := by
    have := Nat.mul_le_mul_left s hM
    nlinarith
  have hpbig : 40 * M < p := by
    by_contra h
    have hprod := Nat.mul_le_mul_right M (show p ≤ 40 * M by omega)
    nlinarith
  have hsp : s ≤ p := by
    by_contra h
    have hprod := Nat.mul_le_mul_right M (show p ≤ s by omega)
    nlinarith
  have hpmul := Nat.mul_lt_mul_of_pos_right hpbig hp.pos
  have h1600 : 1600 * n < p ^ 2 := by nlinarith
  have hodd : 2 * (p / 2) + 1 = p := by
    have := Nat.mod_add_div p 2
    rcases hp.eq_two_or_odd with h | h
    · omega
    · omega
  have hB : fillBudget s ν M ≤ 40 * n - 3 * n := by omega
  have hνn := Nat.mul_le_mul_right (3 * n) hν
  have hdeg : s + 2 * (ν * (3 * n) + 2 * (40 * n - 3 * n)) - 2 * (40 * n) + 1 < p ^ 2 := by
    have hsub : 40 * n - 3 * n = 37 * n := by omega
    have hraw : s + 2 * (ν * (3 * n) + 2 * (40 * n - 3 * n)) + 1 < p ^ 2 := by
      rw [hsub]
      nlinarith
    omega
  exact explicit_innerOK_of_structural hs hodd (by omega) hsp (by omega) hKM hB
    (by nlinarith) hdeg

/-- PROOF-DRAFT: eventual validity uniformly at every inner prime. -/
theorem eventual_explicit_innerOK (s ν M : ℕ) (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ p : ℕ, p.Prime → 40 * n < p * M →
      InnerOK s ν (40 * n) (3 * n) p (explicitAllocation s ν (40 * n) (3 * n) M) := by
  refine Filter.eventually_atTop.mpr ⟨fillBudget s ν M + (s + M + 1) ^ 2 + 1, ?_⟩
  intro n hn p hp hKM
  exact explicit_innerOK_fixed_shape s ν M n p hs hν hM hn hp hKM

/-- PROOF-DRAFT: the actual selected inner branch, with validity derived. -/
theorem selected_explicit_inner (s ν M n p : ℕ)
    (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M)
    (hn : fillBudget s ν M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n) :
    LpSharp s ν (40 * n) (3 * n) M p (explicitAllocation s ν (40 * n) (3 * n) M) =
      vSK ν (40 * n) (3 * n) p +
        ⌊2 * WI s ν (40 * n) (3 * n) p (explicitAllocation s ν (40 * n) (3 * n) M)⌋ := by
  have hOK := explicit_innerOK_fixed_shape s ν M n p hs hν hM hn hp hKM
  unfold LpSharp
  rw [if_neg (by omega), if_pos hin, if_pos hOK]

end
end BInnerExplicit
