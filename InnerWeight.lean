import CostBounds

/-!
E428, Codex native outer_sum, lane B, 2026-11-14. PROOF-DRAFT until parent gate.
Reverse weight bound for the SAME literal explicitAllocation. No optimization
over other allocations is asserted. PhiK is in weight units: WI <= PhiK,
equivalently 2*WI <= 2*PhiK. Actual imported models are unchanged.
CITED: Firsching/Paul-Lez mo271/Zeta5@be1c0d82, Apache2.0,
Apery/Arith/InnerAlloc.lean allocation/deficit architecture; source headers kept.
-/
open Finset
namespace BInnerWeight
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget BInnerExplicit

section Generic
variable {m : ℕ}

/-- PROOF-DRAFT: an increased ordinary row count pins the exact minimal top. -/
theorem tmin_eq_half_of_rows_lt (ℓ : ℚ) (hm : 1 ≤ m) (b : ℕ → ℚ)
    (β : Fin (m + 1) → ℤ)
    (hβ : ∀ c : Fin (m + 1), c ≠ 0 → b c = (β c : ℚ) + ℓ)
    (h : ℕ) (k : ℤ) (hrows : rowsK β k < rowsK β (k + 1)) :
    tminS ℓ hm (allocK β h k) b = (k : ℚ) / 2 := by
  apply le_antisymm
  · obtain ⟨c, hc, hlt⟩ := Finset.exists_lt_of_sum_lt hrows
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have hstep := lrow_succ k (β c)
    have htop : 2 * (lrow k (β c) : ℤ) + β c = k := by
      rcases hstep with heq | ⟨_, heq⟩
      · omega
      · exact heq
    have htopQ : 2 * (lrow k (β c) : ℚ) + β c = k := by exact_mod_cast htop
    have htopval : topwS ℓ (allocK β h k) b c = (k : ℚ) / 2 := by
      unfold topwS
      rw [show allocK β h k c = lrow k (β c) by simp [allocK, hc0], hβ c hc0]
      linarith
    exact (tmin_leS ℓ hm (allocK β h k) b hc0).trans_eq htopval
  · exact tmin_allocK_geS ℓ hm b β hβ h k

/-- PROOF-DRAFT: with exact half-level cap, the allocated weight is at most Phi.
This generic helper has an explicit cap premise; the actual selected allocation
below derives that premise from the search maximality. -/
theorem sum_wcap_allocK_le_of_cap (ℓ : ℚ) (hm : 1 ≤ m) (b : ℕ → ℚ)
    (β : Fin (m + 1) → ℤ)
    (hβ : ∀ c : Fin (m + 1), c ≠ 0 → b c = (β c : ℚ) + ℓ)
    (h : ℕ) (k : ℤ) (hrows : rowsK β k ≤ h)
    (hcap : tminS ℓ hm (allocK β h k) b ≤ (k : ℚ) / 2) :
    (∑ x, wcapS ℓ hm (allocK β h k) b x) ≤ PhiK β h k := by
  let L := allocK β h k
  rw [Fintype.sum_sigma]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  have hnz : ∀ c ∈ univ.erase (0 : Fin (m + 1)),
      (∑ i : Fin (L c), wcapS ℓ hm L b ⟨c, i⟩) ≤
        ∑ i ∈ range (lrow k (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    intro c hc
    have hc0 := (Finset.mem_erase.mp hc).1
    have hLc : L c = lrow k (β c) := by dsimp [L, allocK]; rw [if_neg hc0]
    calc
      _ ≤ (∑ i : Fin (L c), (((i : ℕ) : ℚ) + (β c : ℚ) / 2)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc
          wcapS ℓ hm L b ⟨c, i⟩ ≤ wrawS ℓ L b ⟨c, i⟩ := min_le_left _ _
          _ = _ := by
            unfold wrawS
            rw [if_neg hc0, hβ c hc0]
            ring
      _ = _ := by
        rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℚ) + (β c : ℚ) / 2) (L c), hLc]
  have hz : (∑ i : Fin (L 0), wcapS ℓ hm L b ⟨0, i⟩) ≤ (L 0 : ℚ) * k / 2 := by
    calc
      _ ≤ ∑ _i : Fin (L 0), (k : ℚ) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (min_le_right _ _).trans hcap
      _ = _ := by simp; ring
  have hL0 : (L 0 : ℚ) = (h : ℚ) - rowsK β k := by
    dsimp [L, allocK]
    push_cast [hrows]
    ring
  have hpsi : ∀ c ∈ univ.erase (0 : Fin (m + 1)), psiR k (β c) =
      (lrow k (β c) : ℚ) * k / 2 -
        ∑ i ∈ range (lrow k (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    intro c _
    unfold psiR
    rw [show (lrow k (β c) : ℚ) * k / 2 =
      ∑ _i ∈ range (lrow k (β c)), (k : ℚ) / 2 by simp; ring,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hΦ : PhiK β h k = (h : ℚ) * k / 2 - (rowsK β k : ℚ) * k / 2 +
      ∑ c ∈ univ.erase (0 : Fin (m + 1)),
        ∑ i ∈ range (lrow k (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    unfold PhiK
    rw [Finset.sum_congr rfl hpsi, Finset.sum_sub_distrib]
    unfold rowsK
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
    ring
  rw [hΦ]
  have hsum := Finset.sum_le_sum hnz
  rw [hL0] at hz
  change (∑ i : Fin (L 0), wcapS ℓ hm L b ⟨0, i⟩) +
    ∑ c ∈ univ.erase (0 : Fin (m + 1)), ∑ i : Fin (L c), wcapS ℓ hm L b ⟨c, i⟩ ≤ _
  linarith

end Generic

section Actual
variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: the literal search upper endpoint uses too many ordinary rows. -/
theorem upper_endpoint_infeasible {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hNK : N ≤ K) (hKM : K < p * M)
    (hpM : M + 1 < p) :
    K - N < rowsK (beta s ν K N p) ((fillBudget s ν M : ℤ) + 4 * M + 4) := by
  have hb : ∀ c : Fin (p / 2 + 1), c ≠ 0 → beta s ν K N p c ≤ fillBudget s ν M := by
    intro c hc
    have hβ := (beta_bounds (s := s) (ν := ν) hodd hNK hKM c hc).2
    have hB : (2 : ℤ) * ν * M ≤ fillBudget s ν M := by exact_mod_cast budget_ge_high s ν M
    omega
  have hrow : ∀ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0,
      2 * M + 2 ≤ lrow ((fillBudget s ν M : ℤ) + 4 * M + 4) (beta s ν K N p c) := by
    intro c hc
    have hc0 := (Finset.mem_erase.mp hc).1
    have hbc := hb c hc0
    unfold lrow
    omega
  have hsum : (2 * M + 2) * (p / 2) ≤
      rowsK (beta s ν K N p) ((fillBudget s ν M : ℤ) + 4 * M + 4) := by
    calc
      (2 * M + 2) * (p / 2) =
          ∑ _c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0, (2 * M + 2) := by
        simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hmM : M < 2 * (p / 2) := by omega
  have hmul : (2 * (p / 2) + 1) * M = p * M := congrArg (fun t : ℕ => t * M) hodd
  have hKN : K - N ≤ K := Nat.sub_le _ _
  nlinarith

/-- PROOF-DRAFT: the actual selected level is strictly below its literal upper window. -/
theorem selected_level_lt_upper {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hNK : N ≤ K) (hKM : K < p * M)
    (hpM : M + 1 < p) (hB : fillBudget s ν M ≤ K - N) :
    selectedLevel s ν K N M p < (fillBudget s ν M : ℤ) + 4 * M + 4 := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas := kfSel_feasible β (K - N) B lo hi hlo
  have hle := kfSel_le β (K - N) B lo hi (by dsimp [lo, hi]; omega)
  have hinfeas := upper_endpoint_infeasible (ν := ν) hs hodd hNK hKM hpM
  change K - N < rowsK β hi at hinfeas
  change kfSel β (K - N) B lo hi < hi
  by_contra h
  have heq : kfSel β (K - N) B lo hi = hi := by omega
  rw [heq] at hfeas
  omega

/-- PROOF-DRAFT: search maximality gives an actual ordinary row increase. -/
theorem selected_rows_lt_succ {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hNK : N ≤ K) (hKM : K < p * M)
    (hpM : M + 1 < p) (hB : fillBudget s ν M ≤ K - N) :
    rowsK (beta s ν K N p) (selectedLevel s ν K N M p) <
      rowsK (beta s ν K N p) (selectedLevel s ν K N M p + 1) := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let k := selectedLevel s ν K N M p
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas : rowsK β k + B ≤ K - N := kfSel_feasible β (K - N) B lo hi hlo
  have hk := selected_level_lt_upper hs hodd hNK hKM hpM hB
  change k < hi at hk
  have hmax : K - N < rowsK β (k + 1) + B :=
    kfSel_max β (K - N) B lo hi (by dsimp [k, selectedLevel, β, B, lo, hi]; omega)
      (by omega)
  change rowsK β k < rowsK β (k + 1)
  omega

/-- PROOF-DRAFT: exact actual minimum top for the literal explicit allocation. -/
theorem explicit_tmin_eq {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hm : 1 ≤ p / 2)
    (hNK : N ≤ K) (hKM : K < p * M)
    (hpM : M + 1 < p) (hB : fillBudget s ν M ≤ K - N) :
    tminS ((s : ℚ) - 1) hm (explicitAllocation s ν K N M p) (BseS s ν p K N) =
      (selectedLevel s ν K N M p : ℚ) / 2 := by
  apply tmin_eq_half_of_rows_lt ((s : ℚ) - 1) hm (BseS s ν p K N)
    (beta s ν K N p) (fun c hc => Bse_eq_beta s ν K N p c hc) (K - N)
    (selectedLevel s ν K N M p)
  exact selected_rows_lt_succ hs hodd hNK hKM hpM hB

/-- PROOF-DRAFT: the reverse inequality in weight units, on the actual allocation. -/
theorem explicit_weight_le_Phi {s ν K N M : ℕ} (hs : 1 ≤ s)
    (hodd : 2 * (p / 2) + 1 = p) (hm : 1 ≤ p / 2)
    (hNK : N ≤ K) (hKM : K < p * M)
    (hpM : M + 1 < p) (hB : fillBudget s ν M ≤ K - N) :
    WI s ν K N p (explicitAllocation s ν K N M) ≤
      PhiK (beta s ν K N p) (K - N) (selectedLevel s ν K N M p) := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let k := selectedLevel s ν K N M p
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas : rowsK β k + B ≤ K - N := kfSel_feasible β (K - N) B lo hi hlo
  have hcap := explicit_tmin_eq hs hodd hm hNK hKM hpM hB
  unfold WI
  rw [dif_pos hm]
  exact sum_wcap_allocK_le_of_cap ((s : ℚ) - 1) hm (BseS s ν p K N) β
    (fun c hc => Bse_eq_beta s ν K N p c hc) (K - N) k (by omega) hcap.le

/-- PROOF-DRAFT: matching lower weight bound at the literal selected level. -/
theorem explicit_weight_ge_selected_Phi {s ν K N M : ℕ}
    (hodd : 2 * (p / 2) + 1 = p) (hm : 1 ≤ p / 2)
    (hNK : N ≤ K) (hKM : K < p * M) (hB : fillBudget s ν M ≤ K - N) :
    PhiK (beta s ν K N p) (K - N) (selectedLevel s ν K N M p) -
      zeroDeficit s ν K N M p * (zeroDeficit s ν K N M p / 2 + 1) ≤
        WI s ν K N p (explicitAllocation s ν K N M) := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let k := selectedLevel s ν K N M p
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas : rowsK β k + B ≤ K - N := kfSel_feasible β (K - N) B lo hi hlo
  have hw := sum_wcap_allocKS ((s : ℚ) - 1) hm (BseS s ν p K N) β
    (fun c hc => Bse_eq_beta s ν K N p c hc) (K - N) k (by omega : rowsK β k ≤ K - N)
  unfold WI
  rw [dif_pos hm]
  exact hw

end Actual

/-- PROOF-DRAFT: exact upper weight bound at the already approved finite threshold. -/
theorem explicit_weight_le_Phi_fixed_shape (s ν M n p : ℕ)
    (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M)
    (hn : fillBudget s ν M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hp : p.Prime) (hKM : 40 * n < p * M) :
    WI s ν (40 * n) (3 * n) p (explicitAllocation s ν (40 * n) (3 * n) M) ≤
      PhiK (beta s ν (40 * n) (3 * n) p) (40 * n - 3 * n)
        (selectedLevel s ν (40 * n) (3 * n) M p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnM : M ^ 2 ≤ n := by nlinarith [Nat.zero_le (s * M)]
  have hpbig : 40 * M < p := by
    by_contra h
    have hprod := Nat.mul_le_mul_right M (show p ≤ 40 * M by omega)
    nlinarith
  obtain ⟨hodd, hm, _, _, _, _, _, _⟩ :=
    explicit_innerOK_fixed_shape s ν M n p hs hν hM hn hp hKM
  exact explicit_weight_le_Phi hs hodd hm (by omega) hKM (by omega) (by omega)

/-- PROOF-DRAFT: the actual weight differs from selected Phi by one explicit
parameter-only constant. The factor of two is not hidden in this normalization. -/
theorem explicit_weight_selected_Phi_abs (s ν M n p : ℕ)
    (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M)
    (hn : fillBudget s ν M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hp : p.Prime) (hKM : 40 * n < p * M) :
    |WI s ν (40 * n) (3 * n) p (explicitAllocation s ν (40 * n) (3 * n) M) -
      PhiK (beta s ν (40 * n) (3 * n) p) (40 * n - 3 * n)
        (selectedLevel s ν (40 * n) (3 * n) M p)| ≤
      ((fillBudget s ν M : ℚ) + 6 * M + 4) *
        (((fillBudget s ν M : ℚ) + 6 * M + 4) / 2 + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hodd, hm, _, _, _, _, _, _⟩ :=
    explicit_innerOK_fixed_shape s ν M n p hs hν hM hn hp hKM
  have hlo := explicit_weight_ge_selected_Phi hodd hm (by omega : 3 * n ≤ 40 * n) hKM
    (by omega : fillBudget s ν M ≤ 40 * n - 3 * n)
  have hhi := explicit_weight_le_Phi_fixed_shape s ν M n p hs hν hM hn hp hKM
  obtain ⟨hD0, hDE⟩ := zeroDeficit_bounds s ν (40 * n) (3 * n) M hKM
  let E : ℚ := (fillBudget s ν M : ℚ) + 6 * M + 4
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hDsq : zeroDeficit s ν (40 * n) (3 * n) M p * zeroDeficit s ν (40 * n) (3 * n) M p ≤ E * E :=
    mul_le_mul hDE hDE hD0 hE0
  rw [abs_le]
  change - (E * (E / 2 + 1)) ≤ _ ∧ _ ≤ E * (E / 2 + 1)
  constructor <;> nlinarith

section PhiComparison
variable {m : ℕ}

/-- PROOF-DRAFT: finite Phi arithmetic below a reference level. -/
theorem Phi_le_below (β : Fin (m + 1) → ℤ) (h : ℕ) (a k : ℤ) (C : ℚ)
    (hk : k ≤ a) (hrows : (rowsK β a : ℚ) ≤ (h : ℚ) + C) :
    PhiK β h k ≤ PhiK β h a + ((a - k : ℤ) : ℚ) * C / 2 := by
  obtain ⟨t, ha⟩ : ∃ t : ℕ, a = k + t := ⟨(a - k).toNat, by omega⟩
  have hstep : ∀ j : ℕ, j ≤ t →
      PhiK β h k ≤ PhiK β h (k + j) + (j : ℚ) * C / 2 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hr := rowsK_mono β (show k + (j : ℤ) + 1 ≤ a by omega)
      have hrQ : (rowsK β (k + (j : ℤ) + 1) : ℚ) ≤ (h : ℚ) + C := by
        exact (show (rowsK β (k + (j : ℤ) + 1) : ℚ) ≤ rowsK β a by exact_mod_cast hr).trans hrows
      rw [show k + ((j + 1 : ℕ) : ℤ) = (k + j) + 1 by push_cast; ring, PhiK_succ]
      push_cast
      linarith
  have hfinal := hstep t le_rfl
  rw [← ha] at hfinal
  have hcast : ((a - k : ℤ) : ℚ) = (t : ℚ) := by rw [ha]; push_cast; ring
  rw [hcast]
  exact hfinal

/-- PROOF-DRAFT: finite Phi arithmetic above a reference level. -/
theorem Phi_le_above (β : Fin (m + 1) → ℤ) (h : ℕ) (a k : ℤ) (C : ℚ)
    (hk : a ≤ k) (hrows : (h : ℚ) - C ≤ rowsK β (a + 1)) :
    PhiK β h k ≤ PhiK β h a + ((k - a : ℤ) : ℚ) * C / 2 := by
  obtain ⟨t, hk'⟩ : ∃ t : ℕ, k = a + t := ⟨(k - a).toNat, by omega⟩
  have hstep : ∀ j : ℕ, PhiK β h (a + j) ≤ PhiK β h a + (j : ℚ) * C / 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hr := rowsK_mono β (show a + 1 ≤ a + (j : ℤ) + 1 by omega)
      have hrQ : (h : ℚ) - C ≤ rowsK β (a + (j : ℤ) + 1) := by
        exact hrows.trans (show (rowsK β (a + 1) : ℚ) ≤ rowsK β (a + (j : ℤ) + 1) by exact_mod_cast hr)
      rw [show a + ((j + 1 : ℕ) : ℤ) = (a + j) + 1 by push_cast; ring, PhiK_succ]
      push_cast
      linarith
  have hfinal := hstep t
  rw [← hk'] at hfinal
  have hcast : ((k - a : ℤ) : ℚ) = (t : ℚ) := by rw [hk']; push_cast; ring
  rw [hcast]
  exact hfinal

/-- PROOF-DRAFT: near-peak comparison of discrete levels only. It is used only
for the literal selected allocation; it states no allocation optimization. -/
theorem Phi_le_max_adjacent (β : Fin (m + 1) → ℤ) (h : ℕ) (κ k : ℤ) (C : ℚ)
    (hC : 0 ≤ C) (hlo : (rowsK β κ : ℚ) ≤ (h : ℚ) + C)
    (hhi : (h : ℚ) - C ≤ rowsK β (κ + 2)) :
    PhiK β h k ≤ max (PhiK β h κ) (PhiK β h (κ + 1)) +
      (((|k - κ| : ℤ) : ℚ) + 2) * C / 2 := by
  by_cases hk : k ≤ κ
  · have hcmp := Phi_le_below β h κ k C hk hlo
    have habs : |k - κ| = κ - k := by rw [abs_of_nonpos (by omega)]; omega
    rw [habs]
    have hm := le_max_left (PhiK β h κ) (PhiK β h (κ + 1))
    linarith
  · have hk' : κ + 1 ≤ k := by omega
    have hh : (h : ℚ) - C ≤ rowsK β ((κ + 1) + 1) := by
      rw [show (κ + 1) + 1 = κ + 2 by ring]
      exact hhi
    have hcmp := Phi_le_above β h (κ + 1) k C hk' hh
    have habs : |k - κ| = k - κ := abs_of_nonneg (by omega)
    rw [habs]
    have hm := le_max_right (PhiK β h κ) (PhiK β h (κ + 1))
    have hcast : ((k - (κ + 1) : ℤ) : ℚ) = ((k - κ : ℤ) : ℚ) - 1 := by push_cast; ring
    rw [hcast] at hcmp
    linarith

end PhiComparison

#print axioms tmin_eq_half_of_rows_lt
#print axioms sum_wcap_allocK_le_of_cap
#print axioms explicit_weight_le_Phi
#print axioms explicit_weight_le_Phi_fixed_shape
#print axioms explicit_weight_selected_Phi_abs
#print axioms Phi_le_max_adjacent
end
end BInnerWeight
