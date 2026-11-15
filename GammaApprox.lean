import UniformClasses
import ClassRows
import GammaCells

/- E420 native Codex inner_explicit. PROOF-DRAFT actual ordinary Gamma
Riemann comparison. This is one component of the two-sided allocation bridge.
-/
open Finset
namespace BInnerExplicit
noncomputable section
open AperyS Mathathon.P108 UniformClasses

/-- PROOF-DRAFT: exact fixed-shape fractional argument. -/
lemma alpha_shape (n p : ℕ) :
    (3 / 40 : ℝ) * (((40 * n : ℕ) : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
  push_cast
  ring

/-- PROOF-DRAFT: actual ordinary row polynomial sum versus the literal
rootGamma integrand, with explicit uniform O_(s,M)(1) error. -/
theorem ordinary_gamma_approx (s ν n M p : ℕ) (hν : ν ≤ 10)
    (hp : p.Prime) (hodd : 2 * (p / 2) + 1 = p)
    (hKM : 40 * n < p * M) :
    |(∑ c ∈ Icc 1 (p / 2),
        (Tc (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) -
            (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
          (Tc (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) +
              (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
            (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))) -
      (p : ℝ) * ∫ z in (0 : ℝ)..(1 / 2),
        gammaIntegrand (s : ℝ) (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) z| ≤
      90 * ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let x : ℝ := ((40 * n : ℕ) : ℝ) / p
  let T : ℝ := Tc (ν : ℝ) (3 / 40) x
  let qK : ℝ := (40 * n / p : ℕ)
  let qN : ℝ := (3 * n / p : ℕ)
  let h := BInnerLimit.gammaTable (s : ℝ) (ν : ℝ) T qN qK
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxM : x ≤ M := by
    dsimp [x]
    rw [div_le_iff₀ hpR]
    exact_mod_cast (show 40 * n ≤ M * p by nlinarith)
  have hqK : qK ≤ M := by
    have hq : 40 * n / p < M := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith)
    dsimp [qK]
    exact_mod_cast hq.le
  have hqN : qN ≤ M := by
    have hq : 3 * n / p < M := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith)
    dsimp [qN]
    exact_mod_cast hq.le
  have hH0 : 0 ≤ Hc (ν : ℝ) (3 / 40) := by unfold Hc; positivity
  have hH : Hc (ν : ℝ) (3 / 40) ≤ 6 := by
    have hνR : (ν : ℝ) ≤ 10 := by exact_mod_cast hν
    unfold Hc
    linarith
  have hT0 : 0 ≤ T := by
    have : (0 : ℤ) ≤ ⌊2 * Hc (ν : ℝ) (3 / 40) * x⌋ := Int.floor_nonneg.mpr (by positivity)
    dsimp [T, Tc]
    exact_mod_cast this
  have hT : T ≤ 12 * M := by
    have hfloor := Int.floor_le (2 * Hc (ν : ℝ) (3 / 40) * x)
    have hprod := mul_le_mul_of_nonneg_right hH hx0
    dsimp [T, Tc]
    nlinarith
  have hbound (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
      |h a b| ≤ ((s : ℝ) + 40 * ((M : ℝ) + 1)) ^ 2 := by
    simpa only [h, BInnerLimit.gammaTable, rowTable] using
      rowTable_bound (s : ℝ) (ν : ℝ) T qK qN (M : ℝ) (by positivity)
        (by positivity) (by exact_mod_cast hν) hT0 hT
        (by dsimp [qK]; positivity) hqK (by dsimp [qN]; positivity) hqN (by positivity) b a hb ha
  have happrox := ContinuousClasses.finite_class_integral_approx hodd
    (Nat.mod_lt (3 * n) hp.pos) (Nat.mod_lt (40 * n) hp.pos) h
  have hcoeff := sum_abs_bcoef_le h _ (sq_nonneg _) hbound
  have hsum : (∑ c ∈ Icc 1 (p / 2),
        (T - (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
          (T + (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
            (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))) =
      ∑ c ∈ Icc 1 (p / 2), h (ClassSums.aCnt p (3 * n % p) c) (ClassSums.aCnt p (40 * n % p) c) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [SX_class hodd (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2,
      SX_class hodd (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2]
    dsimp [h, BInnerLimit.gammaTable, qK, qN]
    push_cast
    rfl
  have hgamma : (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand (s : ℝ) (ν : ℝ) (3 / 40) x z) =
      ∫ z in (0 : ℝ)..(1 / 2),
        h (ContinuousClasses.aCount (((3 * n % p : ℕ) : ℝ) / p) z)
          (ContinuousClasses.aCount (((40 * n % p : ℕ) : ℝ) / p) z) := by
    rw [BInnerLimit.integral_gamma_cells, ContinuousClasses.class_integral]
    dsimp [BInnerLimit.gammaCells, h]
    rw [show (3 / 40 : ℝ) * x = ((3 * n : ℕ) : ℝ) / p by exact alpha_shape n p,
      floor_nat_div, floor_nat_div,
      Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod]
    rfl
  change |(∑ c ∈ Icc 1 (p / 2),
        (T - (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ)) *
          (T + (ν : ℝ) / 2 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) -
            (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℝ) - (s : ℝ))) - _| ≤ _
  rw [hsum, hgamma]
  nlinarith

end
end BInnerExplicit
