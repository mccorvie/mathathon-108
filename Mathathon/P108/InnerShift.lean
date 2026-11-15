import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# #108: the inner s-shift of the (s, ν) bound package (EVENT WORK)

Formalizer (Claude Opus 5.5), Fri Nov 13 2026, started 22:14 PT. Lean v4.35.0, Mathlib v4.35.0.

Claim formalized (criterion5, `derivation.md` §2, Proposition 1, "in particular"; E13):
for the inner limiting function of Fauzan's package with the zeta index `s` and the numerator
power `ν` kept apart,

  R_(s,ν)(x) − R_(s',ν)(x) = (s − s') λ x,   λ = 1 − α,

where (derivation.md (2.2); theta.py `Pkg.R`, reading 'S', c_in = s)

  Γ_(s,ν)(x) = ∫_0^(1/2) (T − b)(T + b − ℓ − s) dz + σ (2T − ⌊2x⌋ − s) + (σ − n₊)₊,
  b = (ν/2) ℓ(αx, z),  ℓ(x, z) = ⌊x − z⌋ + ⌊x + z⌋ + 1,  H = λ + (ν/2) α,
  T = ⌊2Hx⌋,  σ = Hx − T/2,  n₊ = {2x}/2,
  N_ν(x) = 2λx⌊x⌋ − 2νλx⌊αx⌋ − 2J(λx),  J(u) = m u − m(m+1)/4 with m = ⌊2u⌋,
  R_(s,ν) = −Γ_(s,ν) − N_ν.

Here s, s', ν, α, x are arbitrary reals: the identity needs no parity, range or size hypothesis.
Consequences formalized: the inner prime-sum s-step ∫_3^M (R_(s+2,ν) − R_(s,ν)) x⁻³ dx =
2λ(1/3 − 1/M), and, with the crude range (s+1)λ/M, the exact per-step inner cost 2λ/3.

The key lemma is `integral_ell`: ∫_0^(1/2) ℓ(y, z) dz = y for every real y.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-- Fauzan's `ℓ(x, z) = ⌊x − z⌋ + ⌊x + z⌋ + 1` (floor brackets, as in Lai (103), Zeta5
`scripts/appendixB.py` and theta.py `ell`). -/
def ell (x z : ℝ) : ℝ := (⌊x - z⌋ : ℝ) + (⌊x + z⌋ : ℝ) + 1

lemma intervalIntegrable_floor (a b : ℝ) :
    IntervalIntegrable (fun w : ℝ => (⌊w⌋ : ℝ)) volume a b :=
  Monotone.intervalIntegrable (fun x y h => by exact_mod_cast Int.floor_mono h)

lemma integral_floor_zero_one : ∫ w in (0:ℝ)..1, (⌊w⌋ : ℝ) = 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0:ℝ))]
  · simp
  · intro w hw
    simp [Int.floor_eq_zero_iff.mpr ⟨hw.1.le, hw.2⟩]

/-- `∫_c^(c+1) ⌊w⌋ dw = c` for every real `c`. -/
lemma integral_floor_unit (c : ℝ) : ∫ w in c..c + 1, (⌊w⌋ : ℝ) = c := by
  have hper : Function.Periodic (fun w : ℝ => (⌊w⌋ : ℝ) - w) 1 := by
    intro w
    simp only [Int.floor_add_one, Int.cast_add, Int.cast_one]
    ring
  have h1 := hper.intervalIntegral_add_eq c 0
  rw [intervalIntegral.integral_sub (intervalIntegrable_floor _ _)
      (continuous_id'.intervalIntegrable _ _),
    intervalIntegral.integral_sub (intervalIntegrable_floor _ _)
      (continuous_id'.intervalIntegrable _ _),
    zero_add, integral_floor_zero_one, integral_id, integral_id] at h1
  linarith

lemma ell_intervalIntegrable (y : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun z : ℝ => ell y z) volume a b := by
  have hA : IntervalIntegrable (fun z : ℝ => (⌊y - z⌋ : ℝ)) volume a b :=
    Antitone.intervalIntegrable (fun u v h => by exact_mod_cast Int.floor_mono (by linarith))
  have hB : IntervalIntegrable (fun z : ℝ => (⌊y + z⌋ : ℝ)) volume a b :=
    Monotone.intervalIntegrable (fun u v h => by exact_mod_cast Int.floor_mono (by linarith))
  exact (hA.add hB).add intervalIntegrable_const

/-- **Key lemma.** `∫_0^(1/2) ℓ(y, z) dz = y` for every real `y`
(derivation.md §2, proof of Prop. 1: "∫ ℓ = x"). -/
lemma integral_ell (y : ℝ) : ∫ z in (0:ℝ)..(1/2), ell y z = y := by
  have hA : IntervalIntegrable (fun z : ℝ => (⌊y - z⌋ : ℝ)) volume 0 (1/2) :=
    Antitone.intervalIntegrable (fun u v h => by exact_mod_cast Int.floor_mono (by linarith))
  have hB : IntervalIntegrable (fun z : ℝ => (⌊y + z⌋ : ℝ)) volume 0 (1/2) :=
    Monotone.intervalIntegrable (fun u v h => by exact_mod_cast Int.floor_mono (by linarith))
  unfold ell
  rw [intervalIntegral.integral_add (hA.add hB) intervalIntegrable_const,
    intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_comp_sub_left (fun w => (⌊w⌋ : ℝ)) y,
    intervalIntegral.integral_comp_add_left (fun w => (⌊w⌋ : ℝ)) y]
  simp only [sub_zero, add_zero]
  rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_floor _ _)
    (intervalIntegrable_floor _ _)]
  have h := integral_floor_unit (y - 1/2)
  rw [show y - 1/2 + 1 = y + 1/2 by ring] at h
  rw [h, intervalIntegral.integral_const]
  simp

lemma abs_ell_le (y z : ℝ) (_hz0 : 0 ≤ z) (_hz1 : z ≤ 1/2) : |ell y z| ≤ 2 * |y| + 2 := by
  unfold ell
  have h1 := Int.floor_le (y - z)
  have h2 := Int.lt_floor_add_one (y - z)
  have h3 := Int.floor_le (y + z)
  have h4 := Int.lt_floor_add_one (y + z)
  have h5 := le_abs_self y
  have h6 := neg_abs_le y
  rw [abs_le]
  constructor <;> linarith

/-- `H = λ + (ν/2) α` with `λ = 1 − α` (Lai (8): 23/20 at ν = 6, α = 3/40). -/
def Hc (ν α : ℝ) : ℝ := (1 - α) + ν / 2 * α

/-- `T = ⌊2Hx⌋`. -/
def Tc (ν α x : ℝ) : ℝ := (⌊2 * Hc ν α * x⌋ : ℝ)

/-- `σ = Hx − T/2`. -/
def sigmaC (ν α x : ℝ) : ℝ := Hc ν α * x - Tc ν α x / 2

/-- `n₊ = {2x}/2`. -/
def nplus (x : ℝ) : ℝ := (2 * x - (⌊2 * x⌋ : ℝ)) / 2

/-- The integrand of `Γ`: `(T − b)(T + b − ℓ(x, z) − s)` with `b = (ν/2) ℓ(αx, z)`. -/
def gammaIntegrand (s ν α x z : ℝ) : ℝ :=
  (Tc ν α x - ν / 2 * ell (α * x) z) * (Tc ν α x + ν / 2 * ell (α * x) z - ell x z - s)

/-- `Γ_(s,ν)(x) = ∫_0^(1/2) (T − b)(T + b − ℓ − s) dz + σ(2T − ⌊2x⌋ − s) + (σ − n₊)₊`
(derivation.md (2.2); Fauzan (5.4)-(5.6) at (s, ν) = (5, 6); theta.py `Pkg.R`, reading 'S'). -/
def innerGamma (s ν α x : ℝ) : ℝ :=
  (∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z)
    + sigmaC ν α x * (2 * Tc ν α x - (⌊2 * x⌋ : ℝ) - s) + max (sigmaC ν α x - nplus x) 0

/-- `J(u) = m u − m(m+1)/4` with `m = ⌊2u⌋` (theta.py `Jfun`). -/
def Jfun (u : ℝ) : ℝ := (⌊2 * u⌋ : ℝ) * u - (⌊2 * u⌋ : ℝ) * ((⌊2 * u⌋ : ℝ) + 1) / 4

/-- `N_ν(x) = 2λx⌊x⌋ − 2νλx⌊αx⌋ − 2J(λx)`, `λ = 1 − α`. -/
def innerN (ν α x : ℝ) : ℝ :=
  2 * (1 - α) * x * (⌊x⌋ : ℝ) - 2 * ν * (1 - α) * x * (⌊α * x⌋ : ℝ) - 2 * Jfun ((1 - α) * x)

/-- The inner limiting function `R_(s,ν) = −Γ_(s,ν) − N_ν`. -/
def innerR (s ν α x : ℝ) : ℝ := -innerGamma s ν α x - innerN ν α x

lemma gammaIntegrand_integrable (s ν α x : ℝ) :
    IntervalIntegrable (fun z => gammaIntegrand s ν α x z) volume 0 (1/2) := by
  have hF : IntervalIntegrable (fun z => Tc ν α x - ν / 2 * ell (α * x) z) volume 0 (1/2) :=
    intervalIntegrable_const.sub ((ell_intervalIntegrable _ _ _).const_mul _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hF ⊢
  have hF' : Integrable (fun z => Tc ν α x - ν / 2 * ell (α * x) z)
      (volume.restrict (Ioc (0:ℝ) (1/2))) := hF
  have hmeas : Measurable (fun z => Tc ν α x + ν / 2 * ell (α * x) z - ell x z - s) := by
    unfold ell; fun_prop
  refine Integrable.mul_bdd (c := |Tc ν α x| + |ν / 2| * (2 * |α * x| + 2) + (2 * |x| + 2) + |s|)
    hF' hmeas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
  intro z hz
  have e2 := abs_le.mp (abs_ell_le x z hz.1.le hz.2)
  have e3 : |ν / 2 * ell (α * x) z| ≤ |ν / 2| * (2 * |α * x| + 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_ell_le (α * x) z hz.1.le hz.2) (abs_nonneg _)
  have e3' := abs_le.mp e3
  have t1 := le_abs_self (Tc ν α x)
  have t2 := neg_abs_le (Tc ν α x)
  have t3 := le_abs_self s
  have t4 := neg_abs_le s
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [e2.1, e2.2, e3'.1, e3'.2]

/-- **R-shift identity** (criterion5 derivation.md §2, Proposition 1, "in particular"; E13):
for all real `s, s', ν, α, x`, `R_(s,ν)(x) − R_(s',ν)(x) = (s − s') λ x` with `λ = 1 − α`. -/
theorem innerR_shift (s s' ν α x : ℝ) :
    innerR s ν α x - innerR s' ν α x = (s - s') * (1 - α) * x := by
  have key : (∫ z in (0:ℝ)..(1/2), gammaIntegrand s' ν α x z)
      - (∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z)
      = (s - s') * (Tc ν α x / 2 - ν / 2 * (α * x)) := by
    rw [← intervalIntegral.integral_sub (gammaIntegrand_integrable _ _ _ _)
      (gammaIntegrand_integrable _ _ _ _)]
    have h : ∀ z, gammaIntegrand s' ν α x z - gammaIntegrand s ν α x z
        = (s - s') * (Tc ν α x - ν / 2 * ell (α * x) z) := by
      intro z; unfold gammaIntegrand; ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const
        ((ell_intervalIntegrable _ _ _).const_mul _),
      intervalIntegral.integral_const_mul, integral_ell, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  unfold innerR innerGamma sigmaC Hc
  linear_combination key

/-- **Inner prime-sum s-step** (derivation.md §2, Corollary "inner s-cost", first half): for every
`M ≥ 3`, `∫_3^M (R_(s+2,ν)(x) − R_(s,ν)(x)) x⁻³ dx = 2λ(1/3 − 1/M)`.
(Stated with the difference inside one integral; `inner_crude_sstep` splits it.) -/
theorem inner_sstep_integral (s ν α M : ℝ) (hM : 3 ≤ M) :
    ∫ x in (3:ℝ)..M, (innerR (s + 2) ν α x - innerR s ν α x) / x ^ 3
      = 2 * (1 - α) * (1 / 3 - 1 / M) := by
  have h : EqOn (fun x : ℝ => (innerR (s + 2) ν α x - innerR s ν α x) / x ^ 3)
      (fun x : ℝ => 2 * (1 - α) * x ^ (-2 : ℤ)) (uIcc (3:ℝ) M) := by
    intro x hx
    rw [uIcc_of_le hM] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simp only
    rw [innerR_shift, zpow_neg, zpow_ofNat]
    field_simp
    ring
  have hint2 : ∫ x in (3:ℝ)..M, x ^ (-2 : ℤ) = 1 / 3 - 1 / M := by
    rw [integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
    · have hM0 : M ≠ 0 := by linarith
      rw [show ((-2 : ℤ) + 1) = -1 by norm_num, zpow_neg_one, zpow_neg_one]
      push_cast
      field_simp
      ring
    · rw [uIcc_of_le hM]
      intro h0
      linarith [h0.1]
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, hint2]

/-- **Inner plus crude s-step** (derivation.md §2, Corollary "inner s-cost"): with the crude
small-prime term `(s+1)λ/M` (Lai Thm 9.3 RHS; Fauzan (3.12), (5.11)),
`[(s+3)λ/M + ∫_3^M R_(s+2,ν)/x³] − [(s+1)λ/M + ∫_3^M R_(s,ν)/x³] = 2λ/3` for every `M ≥ 3`.
Hypothesis `hint`: `x ↦ R_(s,ν)(x)/x³` is interval integrable on `[3, M]` (true, since `R` is
piecewise affine, but not formalized here; without it both Lean integrals could be junk `0`). -/
theorem inner_crude_sstep (s ν α M : ℝ) (hM : 3 ≤ M)
    (hint : IntervalIntegrable (fun x => innerR s ν α x / x ^ 3) volume 3 M) :
    ((s + 2) + 1) * (1 - α) / M + (∫ x in (3:ℝ)..M, innerR (s + 2) ν α x / x ^ 3)
      - ((s + 1) * (1 - α) / M + ∫ x in (3:ℝ)..M, innerR s ν α x / x ^ 3)
      = 2 * (1 - α) / 3 := by
  have hdiff : IntervalIntegrable
      (fun x => (innerR (s + 2) ν α x - innerR s ν α x) / x ^ 3) volume 3 M := by
    have hc : ContinuousOn (fun x : ℝ => 2 * (1 - α) * x ^ (-2 : ℤ)) (uIcc 3 M) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.zpow₀ continuousOn_id
      intro x hx
      rw [uIcc_of_le hM] at hx
      left; exact (by linarith [hx.1] : (0:ℝ) < x).ne'
    refine (hc.intervalIntegrable).congr ?_
    intro x hx
    rw [uIoc_of_le hM] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simp only
    rw [innerR_shift, zpow_neg, zpow_ofNat]
    field_simp
    ring
  have h2 : IntervalIntegrable (fun x => innerR (s + 2) ν α x / x ^ 3) volume 3 M := by
    refine (hdiff.add hint).congr ?_
    intro x _
    simp only
    ring
  have hsplit := intervalIntegral.integral_sub h2 hint
  have hval := inner_sstep_integral s ν α M hM
  have hfun : (fun x => (innerR (s + 2) ν α x - innerR s ν α x) / x ^ 3)
      = (fun x => innerR (s + 2) ν α x / x ^ 3 - innerR s ν α x / x ^ 3) := by
    funext x; ring
  rw [hfun, hsplit] at hval
  have hM0 : M ≠ 0 := by linarith
  field_simp at hval ⊢
  linarith

end

end Mathathon.P108
