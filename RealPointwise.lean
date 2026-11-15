/- Author Codex GPT-6 U52/E247. PROOF-DRAFT.
Adapted lane-B E414/E415 reductions, themselves Firsching mo271/Zeta5@be1c0d82;
Fauzan re-derivation; Comparator metadata Paul-Lez; Apache-2.0. See source-map.json. -/
import RealScalar
import RealDeterminant

/-!
E414 conditional analytic staging, Codex lane B. PROOF-DRAFT until gate.
Adapted from mo271/Zeta5@be1c0d82 Apery/EnergyBound.lean:67-194,
Firsching; Paul-Lez, Apache-2.0. The literal named configuration statement
is the only energy premise. Degree-dependent terms become s; field constants stay fixed.
-/
open MeasureTheory Set Filter Topology Polynomial Finset Apery
namespace U52

-- Verbatim reindexing helper from Apery/EnergyAtoms.lean:19-25; namespace changed.
lemma sum_Icc_eq_sum_range' (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ j ∈ Finset.range m, f (j + 1) := by
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

-- Verbatim density-independent helpers from Apery/EnergyBound.lean:27-64; enclosing namespace changed.
lemma aeval_D_eq (m : ℕ) (s : ℝ) : aeval s (D m) = ∏ j ∈ Icc 1 m, (s + (j : ℝ) ^ 2) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]

lemma sum_Ioi_card_mul_two (h : ℕ) : (∑ i : Fin h, (Finset.Ioi i).card) * 2 = h * (h - 1) := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i) h, Finset.sum_range_reflect (fun i => i) h,
    Finset.sum_range_id_mul_two]

lemma sum_Ioi_const (h : ℕ) (c : ℝ) :
    ∑ i : Fin h, ∑ _j ∈ Finset.Ioi i, c = (h : ℝ) * ((h : ℝ) - 1) / 2 * c := by
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  have := sum_Ioi_card_mul_two h
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have hcast : ((∑ i : Fin h, (Finset.Ioi i).card : ℕ) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
    have h2 : (((∑ i : Fin h, (Finset.Ioi i).card) * 2 : ℕ) : ℝ) = ((h * (h - 1) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h)] at h2 ⊢
    linarith
  rw [← hcast]
  push_cast
  ring

/-- `log D_m(y²) = 2m log K + ∑_{j<m} log(t + ((j+1)/K)²)` with `t = (y/K)²`. -/
lemma log_aeval_D (m : ℕ) {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    Real.log (aeval (y ^ 2) (D m)) =
      2 * m * Real.log K + ∑ j ∈ range m, Real.log ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
  rw [aeval_D_eq, Real.log_prod (fun j _ => by positivity), sum_Icc_eq_sum_range']
  have : ∀ j : ℕ, Real.log (y ^ 2 + ((j + 1 : ℕ) : ℝ) ^ 2) =
      2 * Real.log K + Real.log ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
    intro j
    have e : y ^ 2 + ((j + 1 : ℕ) : ℝ) ^ 2 = K ^ 2 * ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
      push_cast; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

noncomputable def Aconst (T : ℝ) (n : ℕ) : ℝ :=
  2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
    (lam * T - Irho) * Kr n ^ 2 + 16 * (37 * n) * Real.log (Kr n) +
      (12 * Real.log 2 + 17) * (37 * n)

noncomputable def gK (s n : ℕ) (y : ℝ) : ℝ :=
  (1 + 2 * Real.pi * y) ^ s * Real.exp (-(1 / Kr n * y))

/-- Actual-density pointwise comparison under only the posted configuration-energy premise. -/
theorem integrand_le {T : ℝ} (hConfig : U48.ConfigurationStatement T)
    (s : ℕ) (hs : 2 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (37 * n) → ℝ) (hy : ∀ i, 0 < y i) (hinj : Function.Injective y) :
    (Matrix.vandermonde fun j => y j ^ 2).det ^ 2 *
        ∏ j, BAnalyticGram.gramWeight s 6 (40 * n) (3 * n) (y j) ≤
      Real.exp (Aconst T n) * ∏ i, gK s n (y i) := by
  set K : ℝ := Kr n with hKdef
  have hK : 0 < K := by simp only [hKdef, Kr]; positivity
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK1 : 1 ≤ K := by
    simp only [hKdef, Kr]
    linarith
  set t : Fin (37 * n) → ℝ := fun i => (y i / K) ^ 2 with htdef
  have ht : ∀ i, 0 < t i := fun i => by
    simp only [htdef]; have := hy i; positivity
  have htinj : Function.Injective t := by
    intro i j hij
    simp only [htdef] at hij
    have := (pow_left_inj₀ (div_pos (hy i) hK).le (div_pos (hy j) hK).le two_ne_zero).mp hij
    exact hinj ((div_left_inj' hK.ne').mp this)
  -- positivity of both sides
  have hdet : (Matrix.vandermonde fun j => y j ^ 2).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact hinj ((pow_left_inj₀ (hy i).le (hy j).le two_ne_zero).mp hij)
  have hν : ∀ j, 0 < BAnalyticGram.gramWeight s 6 (40 * n) (3 * n) (y j) := fun j => BAnalyticGram.gramWeight_pos s 6 (40 * n) (3 * n) (hy j)
  have hL : 0 < (Matrix.vandermonde fun j => y j ^ 2).det ^ 2 * ∏ j, BAnalyticGram.gramWeight s 6 (40 * n) (3 * n) (y j) :=
    mul_pos (by positivity) (Finset.prod_pos fun j _ => hν j)
  have hg : ∀ i, 0 < gK s n (y i) := fun i => by unfold gK; have := hy i; positivity
  have hR : 0 < Real.exp (Aconst T n) * ∏ i, gK s n (y i) :=
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun i _ => hg i)
  rw [← Real.log_le_log_iff hL hR]
  -- log of the left-hand side
  have hne : ∀ i j : Fin (37 * n), j ∈ Finset.Ioi i → y j ^ 2 - y i ^ 2 ≠ 0 := by
    intro i j hj h0
    have : y j ^ 2 = y i ^ 2 := by linarith
    exact (Finset.mem_Ioi.mp hj).ne' (hinj ((pow_left_inj₀ (hy j).le (hy i).le two_ne_zero).mp this))
  have hdet2 : Real.log ((Matrix.vandermonde fun j => y j ^ 2).det ^ 2) =
      ∑ i, ∑ j ∈ Finset.Ioi i, (4 * Real.log K + 2 * Real.log |t j - t i|) := by
    rw [Matrix.det_vandermonde]
    simp only [← Finset.prod_pow]
    rw [Real.log_prod (fun i _ =>
      (Finset.prod_pos fun j hj => lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hne i j hj)))).ne')]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_prod (fun j hj => pow_ne_zero 2 (hne i j hj))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have e : y j ^ 2 - y i ^ 2 = K ^ 2 * (t j - t i) := by
      simp only [htdef]; field_simp
    have hne' : t j - t i ≠ 0 := by
      intro h0; apply hne i j hj; rw [e, h0, mul_zero]
    rw [Real.log_pow, e, ← Real.log_abs, abs_mul, Real.log_mul (by positivity)
      (abs_pos.mpr hne').ne', abs_of_pos (by positivity : (0:ℝ) < K ^ 2), Real.log_pow]
    push_cast; ring
  -- log of each weight
  have hν_le : ∀ i, Real.log (BAnalyticGram.gramWeight s 6 (40 * n) (3 * n) (y i)) ≤
      (12 * (3 * n) - 2 * (40 * n)) * Real.log K - K * Vfield (t i) + 12 * Real.log (2 * K) + 12 +
        (s : ℝ) * Real.log (1 + 2 * Real.pi * y i) := by
    intro i
    have hyi := hy i
    have hDN := aeval_D_pos (3 * n) (t := y i ^ 2) (by positivity)
    have hDK := aeval_D_pos (40 * n) (t := y i ^ 2) (by positivity)
    have hw := BAnalyticMoments.w_pos s hyi
    unfold BAnalyticGram.gramWeight
    rw [D_eq_legacy (3 * n), D_eq_legacy (40 * n)]
    rw [Real.log_mul (by positivity) hw.ne', Real.log_div (by positivity) hDK.ne', Real.log_pow,
      log_aeval_D _ hK hyi, log_aeval_D _ hK hyi]
    -- comparison lemmas
    have hN : ((3 * n : ℕ) : ℝ) / K = 3 / 40 := by
      simp only [hKdef, Kr]; push_cast; field_simp
    have hKK : ((40 * n : ℕ) : ℝ) / K = 1 := by
      simp only [hKdef, Kr]; push_cast; field_simp
    have h1 := sum_log_le_integral (ht i) hK1 (m := 3 * n) (by omega)
      (by simp only [hKdef, Kr]; push_cast; linarith [(by exact_mod_cast hn : (1:ℝ) ≤ n)])
    have h2 := integral_le_sum_log (ht i) hK (40 * n)
    rw [hN] at h1
    rw [hKK] at h2
    -- the weight
    have hw' : Real.log (BAnalyticMoments.w s (y i)) ≤ (s : ℝ) * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
      calc Real.log (BAnalyticMoments.w s (y i)) ≤ Real.log (1 / Real.pi * (1 + 2 * Real.pi * y i) ^ s *
            Real.exp (-(2 * Real.pi * y i))) := Real.log_le_log hw (BAnalyticEnvelope.density_envelope s (by omega) hyi)
        _ = Real.log (1 / Real.pi) + (s : ℝ) * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
              Real.log_exp, Real.log_pow]
            ring
        _ ≤ (s : ℝ) * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
            have : Real.log (1 / Real.pi) ≤ 0 := by
              rw [one_div, Real.log_inv]; linarith [Real.log_nonneg (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)]
            linarith
    -- `√t = y/K`
    have hsqrt : Real.sqrt (t i) = y i / K := by
      simp only [htdef]; exact Real.sqrt_sq (by positivity)
    have hV : K * Vfield (t i) = 2 * Real.pi * y i + K * (∫ u in (0:ℝ)..1, Real.log (t i + u ^ 2)) -
        6 * (K * ∫ u in (0:ℝ)..(3 / 40), Real.log (t i + u ^ 2)) := by
      unfold Vfield; rw [hsqrt]; field_simp
    push_cast at h1 h2 ⊢
    rw [hV]
    nlinarith [h1, h2, hw']
  -- assemble
  rw [Real.log_mul (by positivity) (Finset.prod_pos fun j _ => hν j).ne', hdet2,
    Real.log_prod (fun j _ => (hν j).ne'), Real.log_mul (Real.exp_pos _).ne'
    (Finset.prod_pos fun i _ => hg i).ne', Real.log_exp, Real.log_prod (fun i _ => (hg i).ne')]
  have hE := hConfig n hn t ht htinj
  have hsqrt : ∀ i, Real.sqrt (t i) = y i / K := fun i => by
    simp only [htdef]; exact Real.sqrt_sq (div_pos (hy i) hK).le
  simp_rw [hsqrt] at hE
  have hgi : ∀ i, Real.log (gK s n (y i)) = (s : ℝ) * Real.log (1 + 2 * Real.pi * y i) - y i / K := by
    intro i
    unfold gK
    rw [Real.log_mul (by have := hy i; positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
    ring
  simp_rw [hgi]
  simp only [Finset.sum_add_distrib, sum_Ioi_const]
  have hsum_le := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hν_le i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum_le
  have hlog2K : Real.log (2 * K) = Real.log 2 + Real.log K := Real.log_mul two_ne_zero hK.ne'
  rw [hlog2K] at hsum_le
  unfold Aconst
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [← Finset.mul_sum] at hE
  rw [← hKdef] at *
  push_cast at *
  linarith [hE, hsum_le]
end U52
