import Allocation

/- E420, native Codex inner_explicit. PROOF-DRAFT finite discrete bounds.
CITED: Firsching/Paul-Lez Zeta5@be1c0d82, InnerAlloc.PhiK_le_kf,
sum_wcap_allocK and Growth/InnerPrime.lean179-251 architecture. These are
helper bounds for the actual explicit allocation, not the full rootGamma
identification or an optimization theorem over other allocations. -/

open Finset
namespace BInnerExplicit
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget

/-- The exact existing kfSel level used in the posted explicitAllocation. -/
def selectedLevel (s ν K N M p : ℕ) : ℤ :=
  kfSel (beta s ν K N p) (K - N) (fillBudget s ν M)
    (-(fillBudget s ν M : ℤ)) ((fillBudget s ν M : ℤ) + 4 * M + 4)

/-- Exact zero-class deficit appearing in the imported allocation estimate. -/
def zeroDeficit (s ν K N M p : ℕ) : ℚ :=
  max 0 ((selectedLevel s ν K N M p : ℚ) / 2 -
    (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2)

variable {p : ℕ} [hp : Fact p.Prime]

/-- PROOF-DRAFT: actual weight lower bound at every comparison level in the
approved bounded window. This is a finite algebraic helper, not rootGamma. -/
theorem explicit_weight_ge_Phi {s ν K N M : ℕ}
    (hodd : 2 * (p / 2) + 1 = p) (hm1 : 1 ≤ p / 2)
    (hNK : N ≤ K) (hKM : K < p * M) (hB : fillBudget s ν M ≤ K - N)
    (k : ℤ) (hklo : -(fillBudget s ν M : ℤ) ≤ k)
    (hkhi : k ≤ (fillBudget s ν M : ℤ) + 4 * M + 4) :
    PhiK (beta s ν K N p) (K - N) k -
        ((k + (fillBudget s ν M : ℤ) : ℤ) : ℚ) * fillBudget s ν M / 2 -
        zeroDeficit s ν K N M p * (zeroDeficit s ν K N M p / 2 + 1) ≤
      WI s ν K N p (explicitAllocation s ν K N M) := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  let lo : ℤ := -(B : ℤ)
  let hi : ℤ := (B : ℤ) + 4 * M + 4
  let kf := selectedLevel s ν K N M p
  have hlo : rowsK β lo + B ≤ K - N := by
    simpa [β, B, lo, rowsK_lower_eq_zero hodd hNK hKM] using hB
  have hfeas : rowsK β kf + B ≤ K - N := kfSel_feasible β (K - N) B lo hi hlo
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 →
      BseS s ν p K N (c : ℕ) = (β c : ℚ) + ((s : ℚ) - 1) :=
    fun c hc => Bse_eq_beta s ν K N p c hc
  have hW := sum_wcap_allocKS ((s : ℚ) - 1) hm1 (BseS s ν p K N) β hβ
    (K - N) kf (by omega : rowsK β kf ≤ K - N)
  have hΦ := PhiK_le_kf β (K - N) B lo hi hlo hklo hkhi
  change PhiK β (K - N) k ≤ PhiK β (K - N) kf + ((k - lo : ℤ) : ℚ) * B / 2 at hΦ
  change PhiK β (K - N) k - ((k + (B : ℤ) : ℤ) : ℚ) * B / 2 -
      zeroDeficit s ν K N M p * (zeroDeficit s ν K N M p / 2 + 1) ≤ _
  unfold WI
  rw [dif_pos hm1]
  change _ ≤ ∑ x, wcapS ((s : ℚ) - 1) hm1 (allocK β (K - N) kf) (BseS s ν p K N) x
  change PhiK β (K - N) kf -
      zeroDeficit s ν K N M p * (zeroDeficit s ν K N M p / 2 + 1) ≤ _ at hW
  have hcast : (((k - lo : ℤ) : ℚ)) = ((k + (B : ℤ) : ℤ) : ℚ) := by dsimp [lo]; ring
  rw [hcast] at hΦ
  linarith

/-- A displayed finite error depending only on the fixed parameters. -/
def discreteError (s ν M : ℕ) : ℚ :=
  let B : ℚ := fillBudget s ν M
  let E : ℚ := B + 6 * M + 4
  (2 * B + 4 * M + 4) * B + E ^ 2 + 2 * E + 1

/-- PROOF-DRAFT: the actual zero-class deficit is bounded independently of K. -/
lemma zeroDeficit_bounds (s ν K N M : ℕ) (hKM : K < p * M) :
    0 ≤ zeroDeficit s ν K N M p ∧
      zeroDeficit s ν K N M p ≤ (fillBudget s ν M : ℚ) + 6 * M + 4 := by
  let β := beta s ν K N p
  let B := fillBudget s ν M
  have hkf := kfSel_le β (K - N) B (-(B : ℤ)) ((B : ℤ) + 4 * M + 4) (by omega)
  have hkfQ : (selectedLevel s ν K N M p : ℚ) ≤ (B : ℚ) + 4 * M + 4 := by
    have := (Int.cast_le (R := ℚ)).mpr hkf
    simpa [selectedLevel, β, B] using this
  have hq : K / p < M := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by nlinarith)
  have hqQ : ((K / p : ℕ) : ℚ) ≤ M := by exact_mod_cast hq.le
  have hN0 : (0 : ℚ) ≤ 2 * ν * ((N / p : ℕ) : ℚ) := by positivity
  unfold zeroDeficit
  refine ⟨le_max_left _ _, max_le (by positivity) ?_⟩
  rw [Bse_zero_offset]
  change _ ≤ (B : ℚ) + 6 * M + 4
  nlinarith

/-- PROOF-DRAFT: actual selected cost, bounded by the discrete Phi comparison
with one explicit parameter-only error. This does not identify Phi with rootGamma. -/
theorem selected_cost_le_Phi (s ν M n p : ℕ)
    (hs : 1 ≤ s) (hν : ν ≤ 10) (hM : 40 ≤ M)
    (hn : fillBudget s ν M + (s + M + 1) ^ 2 + 1 ≤ n)
    (hp : p.Prime) (hKM : 40 * n < p * M) (hin : 3 * p ≤ 40 * n)
    (k : ℤ) (hklo : -(fillBudget s ν M : ℤ) ≤ k)
    (hkhi : k ≤ (fillBudget s ν M : ℤ) + 4 * M + 4) :
    -(LpSharp s ν (40 * n) (3 * n) M p (explicitAllocation s ν (40 * n) (3 * n) M) : ℚ) ≤
      -(vSK ν (40 * n) (3 * n) p : ℚ) -
        2 * PhiK (beta s ν (40 * n) (3 * n) p) (40 * n - 3 * n) k + discreteError s ν M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOK := explicit_innerOK_fixed_shape s ν M n p hs hν hM hn hp hKM
  obtain ⟨hodd, hm1, hsp, hsep, hKsq, hdeg, hsum, hZ⟩ := hOK
  have hW := explicit_weight_ge_Phi hodd hm1 (by omega : 3 * n ≤ 40 * n) hKM
    (by omega : fillBudget s ν M ≤ 40 * n - 3 * n) k hklo hkhi
  have hD := zeroDeficit_bounds s ν (40 * n) (3 * n) M hKM
  have hfl := Int.lt_floor_add_one
    (2 * WI s ν (40 * n) (3 * n) p (explicitAllocation s ν (40 * n) (3 * n) M))
  have hsel := selected_explicit_inner s ν M n p hs hν hM hn hp hKM hin
  rw [hsel]
  push_cast
  let B : ℚ := fillBudget s ν M
  let E : ℚ := B + 6 * M + 4
  have hkQ : ((k + (fillBudget s ν M : ℤ) : ℤ) : ℚ) ≤ 2 * B + 4 * M + 4 := by
    have hki : k + (fillBudget s ν M : ℤ) ≤ 2 * (fillBudget s ν M : ℤ) + 4 * M + 4 := by omega
    dsimp [B]
    push_cast
    exact_mod_cast hki
  have hprod := mul_le_mul_of_nonneg_right hkQ (show 0 ≤ B by positivity)
  have hDsq : zeroDeficit s ν (40 * n) (3 * n) M p * zeroDeficit s ν (40 * n) (3 * n) M p ≤ E * E :=
    mul_le_mul hD.2 hD.2 hD.1 (by dsimp [E, B]; positivity)
  change _ ≤ -(vSK ν (40 * n) (3 * n) p : ℚ) -
      2 * PhiK (beta s ν (40 * n) (3 * n) p) (40 * n - 3 * n) k +
      ((2 * B + 4 * M + 4) * B + E ^ 2 + 2 * E + 1)
  change _ - ((k + (fillBudget s ν M : ℤ) : ℤ) : ℚ) * B / 2 - _ ≤ _ at hW
  have hDupper : zeroDeficit s ν (40 * n) (3 * n) M p ≤ E := hD.2
  nlinarith [hD.1, hDupper]

end
end BInnerExplicit
