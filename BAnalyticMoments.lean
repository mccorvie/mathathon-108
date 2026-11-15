import BAnalyticIntegral
import Zeta5S.Monomial

/-!
B6/E407: actual-density polynomial moments, by Codex lane B (PROOF-DRAFT until gate).
Source pattern: mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/Weight.lean:15-34 and Apery/Moments.lean:48-142, Firsching; Paul-Lez,
Apache-2.0. Generalized from s=5 to arbitrary s>=2. See NOTICE and source_map.json.
No pole-moment identity, energy or determinant bound is claimed here.
-/

open MeasureTheory Set Filter Topology Finset

namespace BAnalyticMoments

/-- The actual positive density's series, indexed by l+1. -/
noncomputable def wSeries (s : ℕ) (y : ℝ) : ℝ :=
  ∑' l : ℕ, ((l : ℝ) + 1) ^ (s - 1) * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))

/-- The natural density from B4, without replacing it by an abstract moment functional. -/
noncomputable def w (s : ℕ) (y : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ (s - 1) * y ^ s / ((s - 1).factorial : ℝ) * wSeries s y

-- Generalizes Apery/Weight.lean:21-34, with exponent s-1.
lemma summable_wSeries (s : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun l : ℕ => ((l : ℝ) + 1) ^ (s - 1) *
      Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (s - 1)
    (r := 2 * Real.pi * y) (by positivity)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun l => ?_
  push_cast
  ring_nf

lemma w_pos (s : ℕ) {y : ℝ} (hy : 0 < y) : 0 < w s y := by
  have hseries : 0 < wSeries s y :=
    (summable_wSeries s hy).tsum_pos (fun l => by positivity) 0 (by positivity)
  unfold w
  positivity

-- Generalizes Apery/Moments.lean:48-50.
noncomputable def momTerm (s e l : ℕ) (y : ℝ) : ℝ :=
  (2 * (2 * Real.pi) ^ (s - 1) / ((s - 1).factorial : ℝ)) * ((l : ℝ) + 1) ^ (s - 1) *
    (y ^ (2 * e + s) * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)))

noncomputable def momentFactor (s e : ℕ) : ℝ :=
  2 * ((2 * e + s).factorial : ℝ) / (((s - 1).factorial : ℝ) * (2 * Real.pi) ^ (2 * e + 2))

lemma momTerm_nonneg (s e l : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ momTerm s e l y := by
  unfold momTerm; positivity

lemma integrableOn_momTerm (s e l : ℕ) : IntegrableOn (momTerm s e l) (Ioi 0) := by
  unfold momTerm
  exact (BAnalyticIntegral.integrableOn_pow_mul_exp_neg_mul (2 * e + s)
    (r := 2 * Real.pi * ((l : ℝ) + 1)) (by positivity)).const_mul _

-- Generalizes Apery/Moments.lean:62-74.
lemma integral_momTerm (s : ℕ) (hs : 2 ≤ s) (e l : ℕ) :
    ∫ y in Ioi 0, momTerm s e l y =
      momentFactor s e * (1 / ((l : ℝ) + 1) ^ (2 * e + 2)) := by
  unfold momTerm momentFactor
  rw [integral_const_mul, BAnalyticIntegral.integral_pow_mul_exp_neg_mul _ (by positivity)]
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hf : (0 : ℝ) < ((s - 1).factorial : ℝ) := by positivity
  rw [mul_pow (2 * Real.pi) ((l : ℝ) + 1)]
  have hexp : 2 * e + s + 1 = (s - 1) + (2 * e + 2) := by omega
  rw [hexp]
  simp only [pow_add]
  field_simp

lemma monomial_eq_tsum (s e : ℕ) (y : ℝ) :
    y ^ (2 * e) * w s y = ∑' l, momTerm s e l y := by
  have hterm : ∀ l, momTerm s e l y =
      (y ^ (2 * e) * (2 * (2 * Real.pi) ^ (s - 1) * y ^ s / ((s - 1).factorial : ℝ))) *
        (((l : ℝ) + 1) ^ (s - 1) * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))) := by
    intro l
    unfold momTerm
    rw [pow_add]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  unfold w wSeries
  ring

-- Adapts the p-series norm argument of Apery/Moments.lean:88-99.
lemma summable_integral_norm (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    Summable fun l => ∫ y in Ioi 0, ‖momTerm s e l y‖ := by
  have hnorm : ∀ l, ∫ y in Ioi 0, ‖momTerm s e l y‖ = ∫ y in Ioi 0, momTerm s e l y := by
    intro l
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    exact Real.norm_of_nonneg (momTerm_nonneg s e l hy)
  simp_rw [hnorm, integral_momTerm s hs]
  refine Summable.mul_left _ ?_
  have hp := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * e + 2))
  refine hp.congr fun l => ?_
  push_cast; ring

/-- Honest standalone Gamma/series expression, prior to even-zeta rewriting. -/
theorem integral_monomial_gamma (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    ∫ y in Ioi 0, y ^ (2 * e) * w s y =
      momentFactor s e * (∑' l : ℕ, 1 / ((l : ℝ) + 1) ^ (2 * e + 2)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => monomial_eq_tsum s e y),
    ← integral_tsum_of_summable_integral_norm (fun l => integrableOn_momTerm s e l)
      (summable_integral_norm s hs e)]
  simp_rw [integral_momTerm s hs]
  rw [tsum_mul_left]

/-- Integrability follows from the positive explicit Gamma-series value. -/
theorem integrableOn_monomial (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * w s y) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_monomial_gamma s hs]
  apply ne_of_gt
  have hp : Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ (2 * e + 2)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * e + 2))
    exact h.congr (fun l => by push_cast; ring)
  have hpos : 0 < ∑' l : ℕ, 1 / ((l : ℝ) + 1) ^ (2 * e + 2) :=
    hp.tsum_pos (fun l => by positivity) 0 (by positivity)
  unfold momentFactor
  positivity

-- Adapts the even-zeta rewrite of Apery/Moments.lean:117-129; s stays symbolic.
lemma even_zeta_sum (e : ℕ) :
    (∑' l : ℕ, 1 / ((l : ℝ) + 1) ^ (2 * e + 2)) =
      (-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * (e + 1) - 1) * Real.pi ^ (2 * (e + 1)) *
        (bernoulli (2 * (e + 1)) : ℝ) / (2 * (e + 1)).factorial := by
  have hz := hasSum_zeta_nat (k := e + 1) (by omega)
  have hz1 := (hasSum_nat_add_iff' 1).mpr hz
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
    Nat.mul_eq_zero, OfNat.ofNat_ne_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, or_self,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at hz1
  rw [← hz1.tsum_eq]
  refine tsum_congr fun l => ?_
  push_cast; ring_nf

/-- The actual density integrates to the actual byte-copied lane-L moment definition. -/
theorem integral_monomial (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    ∫ y in Ioi 0, y ^ (2 * e) * w s y = (AperyS.μmonoS s e : ℝ) := by
  rw [integral_monomial_gamma s hs, even_zeta_sum]
  unfold momentFactor AperyS.μmonoS
  push_cast
  rw [show 2 * (e + 1) = 2 * e + 2 by omega,
      show 2 * e + 2 - 1 = 2 * e + 1 by omega]
  have hpow : (2 : ℝ) ^ (2 * e + 2) = 2 * (2 : ℝ) ^ (2 * e + 1) := by
    rw [show 2 * e + 2 = (2 * e + 1) + 1 by omega, pow_succ]
    ring
  have hsign : (-1 : ℝ) ^ (e + 1 + 1) = (-1 : ℝ) ^ e := by simp [pow_add]
  rw [hsign, mul_pow, hpow]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hf : (0 : ℝ) < ((s - 1).factorial : ℝ) := by positivity
  have hf2 : (0 : ℝ) < ((2 * e + 2).factorial : ℝ) := by positivity
  field_simp

/-- Combined moment identity and integrability, as in upstream mono_moment. -/
theorem mono_moment (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * w s y) (Ioi 0) ∧
      ∫ y in Ioi 0, y ^ (2 * e) * w s y = (AperyS.μmonoS s e : ℝ) :=
  ⟨integrableOn_monomial s hs e, integral_monomial s hs e⟩

#print axioms BAnalyticMoments.w_pos
#print axioms BAnalyticMoments.integral_monomial_gamma
#print axioms BAnalyticMoments.integrableOn_monomial
#print axioms BAnalyticMoments.integral_monomial
#print axioms BAnalyticMoments.mono_moment
end BAnalyticMoments
