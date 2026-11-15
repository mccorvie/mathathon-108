/- Author Codex GPT-6 U52/E247. PROOF-DRAFT.
Adapted lane-B E414/E415 reductions, themselves Firsching mo271/Zeta5@be1c0d82;
Fauzan re-derivation; Comparator metadata Paul-Lez; Apache-2.0. See source-map.json. -/
import AnalyticInterface

/-!
E414 conditional analytic staging, Codex lane B. PROOF-DRAFT until gate.
Scalar-only prior input copied/adapted from mo271/Zeta5@be1c0d82,
Apery/RealBound.lean:36-85 (Firsching; Paul-Lez), Apache-2.0.
No configuration-energy theorem or full real-bound target is proved here.
-/
open MeasureTheory Set Filter Topology Polynomial Finset Apery
namespace U52

lemma D_eq_legacy (m : ℕ) : AperyS.D m = Apery.D m := rfl

lemma scalar_fixed_eq (n : ℕ) :
    AperyS.SS 6 (40 * n) (3 * n) (37 * n) = Apery.S n := rfl

lemma scalar_pos (ν K N h : ℕ) : 0 < (AperyS.SS ν K N h : ℝ) := by
  have hprod : (0 : ℚ) < ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  have hq : (0 : ℚ) < AperyS.SS ν K N h := by
    unfold AperyS.SS
    positivity
  exact_mod_cast hq

lemma FS_pos (s : ℕ) (hs : 2 ≤ s) (ν K N h : ℕ) :
    0 < aeval (BAnalyticPoles.zetaS s) (AperyS.FS s ν K N h) := by
  have hS := scalar_pos ν K N h
  have hD := BAnalyticGram.delta_pos s hs ν K N h
  simpa only [AperyS.FS, map_mul, aeval_C, eq_ratCast] using mul_pos hS hD

-- Scalar-only prior proof; same constant and shape, no zeta index appears.
lemma log_legacy_S_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (S n) ≤ (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 * Real.log (Kr n) +
      Cstar * Kr n ^ 2 + 6 * (37 * n) * Real.log (Kr n) + 6 * (37 * n) := by
  have hS : ((S n : ℚ) : ℝ) = ((40 * n).factorial : ℝ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) /
      (((3 * n).factorial : ℝ) ^ (12 * (37 * n)) *
        ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2) := by
    simp only [S]; push_cast; rfl
  have hprod : (0 : ℝ) < ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  rw [hS, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_prod (fun i _ => by positivity)]
  simp only [Real.log_pow, ← Finset.mul_sum]
  have h1 := log_factorial_le (m := 40 * n) (by omega)
  have h2 := log_factorial_ge (3 * n)
  have h3 := sum_log_factorial_two_mul_ge (h := 37 * n) (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : Real.log (3 * (n : ℝ)) = Real.log (3 / 40) + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have h2h : Real.log (2 * (37 * (n : ℝ))) = Real.log (37 / 20) + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hlog37 : Real.log (37 / 20) ≤ 0.85 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 37 / 20); linarith
  have hlog40 : 3 ≤ Real.log (40 * (n : ℝ)) := by
    have hexp : Real.exp 3 < 40 := by
      have h := Real.exp_one_lt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      calc Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := by gcongr
        _ < 40 := by norm_num
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (40 * n) := Real.log_le_log (Real.exp_pos 3) (by linarith)
  have hh1 : ((37 * n - 1 : ℕ) : ℝ) = 37 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hC : Cstar = -2 * (37 / 40) + 12 * (3 / 40) * (37 / 40) * (1 - Real.log (3 / 40)) +
      3 * (37 / 40) ^ 2 - 2 * (37 / 40) ^ 2 * Real.log (37 / 20) := by
    unfold Cstar; norm_num
  rw [hC, hh1]
  push_cast at h1 h2 h3 ⊢
  rw [hN] at h2
  rw [h2h] at h3
  simp only [Kr, lam, alph]
  have hA : 0 ≤ 37 * (n : ℝ) - 1 := by linarith
  have hB : 0 ≤ 4 * (37 * (n : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog4 hA, mul_le_mul_of_nonneg_left hlog37 hB,
    mul_le_mul_of_nonneg_left hlog40 (by positivity : (0 : ℝ) ≤ 37 * n)]

lemma log_SS_fixed_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (AperyS.SS 6 (40 * n) (3 * n) (37 * n) : ℝ) ≤
      (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 * Real.log (Kr n) +
        Cstar * Kr n ^ 2 + 6 * (37 * n) * Real.log (Kr n) + 6 * (37 * n) := by
  rw [scalar_fixed_eq]
  exact log_legacy_S_le n hn
end U52
