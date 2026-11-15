import BAnalyticMoments
import Mathlib.Analysis.SpecificLimits.Normed

/-!
B10 / E412, Codex range_targets worker, lane B, 2026-11-14.
PROOF-DRAFT until the parent repository gate; no human comparison is claimed.
The actual density w is imported unchanged from the gated B6/E407 probe.
The majorant is the classical rising-factorial / negative-binomial series.
Mathlib sources are recorded in README/source-map metadata; no novelty claim.
No pole moment, determinant or energy statement is asserted here.
-/

open Filter Topology

namespace BAnalyticEnvelope

/-- Initial faithful target: exact exponential rate2pi, for the actual B6 density. -/
def EnvelopeStatement : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ (y : ℝ), 0 < y →
    BAnalyticMoments.w s y ≤
      (1 / Real.pi) * (1 + 2 * Real.pi * y) ^ s * Real.exp (-(2 * Real.pi * y))

lemma shifted_power_geometric_le (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ m * q ^ (n + 1)) ≤
      (m.factorial : ℝ) * q / (1 - q) ^ (m + 1) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hs0 : Summable fun n : ℕ => (n : ℝ) ^ m * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one m hnorm
  have hs1 := (summable_nat_add_iff 1).mpr hs0
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1) ^ m * q ^ (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs1
  have hm : Summable fun n : ℕ =>
      ((m.factorial : ℝ) * q) * ((Nat.choose (n + m) m : ℝ) * q ^ n) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one m hnorm).summable.mul_left _
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) ^ m * q ^ (n + 1) ≤
      ((m.factorial : ℝ) * q) * ((Nat.choose (n + m) m : ℝ) * q ^ n) := by
    intro n
    have hn := Nat.pow_succ_le_ascFactorial (n + 1) m
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at hn
    have hc : ((n : ℝ) + 1) ^ m ≤ (m.factorial : ℝ) * (Nat.choose (n + m) m : ℝ) := by
      exact_mod_cast hn
    calc ((n : ℝ) + 1) ^ m * q ^ (n + 1)
        ≤ ((m.factorial : ℝ) * (Nat.choose (n + m) m : ℝ)) * q ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hq0 _)
      _ = ((m.factorial : ℝ) * q) * ((Nat.choose (n + m) m : ℝ) * q ^ n) := by
          rw [pow_succ]
          ring
  calc (∑' n : ℕ, ((n : ℝ) + 1) ^ m * q ^ (n + 1))
      ≤ ∑' n : ℕ, ((m.factorial : ℝ) * q) * ((Nat.choose (n + m) m : ℝ) * q ^ n) :=
        hs.tsum_le_tsum hterm hm
    _ = (m.factorial : ℝ) * q / (1 - q) ^ (m + 1) := by
      rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one m hnorm]
      ring

lemma wSeries_le (s : ℕ) (hs : 1 ≤ s) {y : ℝ} (hy : 0 < y) :
    BAnalyticMoments.wSeries s y ≤
      ((s - 1).factorial : ℝ) * Real.exp (-(2 * Real.pi * y)) /
        (1 - Real.exp (-(2 * Real.pi * y))) ^ s := by
  let q : ℝ := Real.exp (-(2 * Real.pi * y))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have hpos : 0 < 2 * Real.pi * y := by positivity
    linarith
  have hexp : ∀ n : ℕ, Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * y)) = q ^ (n + 1) := by
    intro n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc BAnalyticMoments.wSeries s y
      = ∑' n : ℕ, ((n : ℝ) + 1) ^ (s - 1) * q ^ (n + 1) := by
        unfold BAnalyticMoments.wSeries
        exact tsum_congr fun n => by rw [hexp n]
    _ ≤ ((s - 1).factorial : ℝ) * q / (1 - q) ^ ((s - 1) + 1) :=
      shifted_power_geometric_le (s - 1) hq0 hq1
    _ = ((s - 1).factorial : ℝ) * Real.exp (-(2 * Real.pi * y)) /
        (1 - Real.exp (-(2 * Real.pi * y))) ^ s := by
      rw [Nat.sub_add_cancel hs]

lemma exp_ratio_le {x : ℝ} (hx : 0 < x) :
    x / (1 - Real.exp (-x)) ≤ 1 + x := by
  have hq : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-x) := by linarith
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hprod] at he
  rw [div_le_iff₀ hden]
  nlinarith

/-- Exact-rate density envelope for the unchanged actual B6 density. -/
theorem density_envelope (s : ℕ) (hs : 1 ≤ s) {y : ℝ} (hy : 0 < y) :
    BAnalyticMoments.w s y ≤
      (1 / Real.pi) * (1 + 2 * Real.pi * y) ^ s * Real.exp (-(2 * Real.pi * y)) := by
  let a : ℝ := 2 * Real.pi
  let q : ℝ := Real.exp (-(a * y))
  let f : ℝ := (s - 1).factorial
  have ha : 0 < a := by dsimp [a]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hden : 0 < 1 - q := by linarith
  have hseries : BAnalyticMoments.wSeries s y ≤ f * q / (1 - q) ^ s :=
    wSeries_le s hs hy
  have hcoef : 0 ≤ 2 * a ^ (s - 1) * y ^ s / f := by positivity
  have hpow : a ^ s = a ^ (s - 1) * a := by
    calc a ^ s = a ^ ((s - 1) + 1) := by rw [Nat.sub_add_cancel hs]
      _ = a ^ (s - 1) * a := pow_succ _ _
  have hratio : a * y / (1 - q) ≤ 1 + a * y :=
    exp_ratio_le (by positivity : 0 < a * y)
  have hp : (a * y / (1 - q)) ^ s ≤ (1 + a * y) ^ s :=
    pow_le_pow_left₀ (by positivity) hratio s
  calc BAnalyticMoments.w s y
      = (2 * a ^ (s - 1) * y ^ s / f) * BAnalyticMoments.wSeries s y := rfl
    _ ≤ (2 * a ^ (s - 1) * y ^ s / f) * (f * q / (1 - q) ^ s) :=
      mul_le_mul_of_nonneg_left hseries hcoef
    _ = (1 / Real.pi) * (a * y / (1 - q)) ^ s * q := by
      rw [div_pow, mul_pow a y s, hpow]
      field_simp [hf.ne', hden.ne', Real.pi_pos.ne']
      dsimp [a]
    _ ≤ (1 / Real.pi) * (1 + a * y) ^ s * q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) hq0.le
    _ = (1 / Real.pi) * (1 + 2 * Real.pi * y) ^ s *
          Real.exp (-(2 * Real.pi * y)) := rfl

theorem envelope_statement : EnvelopeStatement := by
  intro s hs y hy
  exact density_envelope s hs hy

#print axioms BAnalyticEnvelope.shifted_power_geometric_le
#print axioms BAnalyticEnvelope.wSeries_le
#print axioms BAnalyticEnvelope.exp_ratio_le
#print axioms BAnalyticEnvelope.density_envelope
#print axioms BAnalyticEnvelope.envelope_statement

end BAnalyticEnvelope
