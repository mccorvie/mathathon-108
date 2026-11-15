import Scalar

/- E422 lane B driver. PROOF-DRAFT until gate.
CITED source patterns from prior Deicyde/zeta7-irrational@be55b3a4:
InnerLimiting.lean434-445,1126-1176; PrimeSumBound853-943.
Actual SS/vSK and actual root legendreTerm/Jfun retained unchanged. -/
open Finset
namespace BOuterScalar
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 BOuterAboveK

theorem floor_natCast_div (a b : ℕ) (hb : 0 < b) : ⌊(a : ℝ) / b⌋ = ((a / b : ℕ) : ℤ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (b : ℝ) * ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) = a := by
    exact_mod_cast Nat.div_add_mod a b
  have h2 : ((a % b : ℕ) : ℝ) + 1 ≤ b := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt a hb)
  have h3 : (0 : ℝ) ≤ ((a % b : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Int.floor_eq_iff, Int.cast_natCast, le_div_iff₀ hbR, div_lt_iff₀ hbR]
  constructor <;> linarith

/-- For `1 ≤ a ≤ m` the class count (43) is the floor count (64):
`ℓ_A(a) = ⌊A/p - a/p⌋ + ⌊A/p + a/p⌋ + 1 = ℓ(A/p, a/p)`. -/

theorem jfun_sum_bounds {p : ℕ} (hp : 2 ≤ p) (h : ℕ) :
    0 ≤ (p : ℝ) * Mathathon.P108.Jfun ((h : ℝ) / p) - ∑ i ∈ range h, ((2 * i / p : ℕ) : ℝ) ∧
      (p : ℝ) * Mathathon.P108.Jfun ((h : ℝ) / p) - ∑ i ∈ range h, ((2 * i / p : ℕ) : ℝ)
        ≤ ((2 * h / p : ℕ) : ℝ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hJ : ∀ k : ℕ, (p : ℝ) * Mathathon.P108.Jfun ((k : ℝ) / p)
      = ((2 * k / p : ℕ) : ℝ) * k
        - p * ((2 * k / p : ℕ) : ℝ) * (((2 * k / p : ℕ) : ℝ) + 1) / 4 := by
    intro k
    have hfl : ⌊2 * ((k : ℝ) / p)⌋ = ((2 * k / p : ℕ) : ℤ) := by
      rw [show 2 * ((k : ℝ) / p) = ((2 * k : ℕ) : ℝ) / p by push_cast; ring]
      exact floor_natCast_div _ _ hp0
    rw [Mathathon.P108.Jfun, hfl, Int.cast_natCast]
    have hk : (p : ℝ) * ((k : ℝ) / p) = k := mul_div_cancel₀ _ hpR.ne'
    linear_combination ((2 * k / p : ℕ) : ℝ) * hk
  induction h with
  | zero =>
    rw [hJ 0]
    simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [hJ] at ih1 ih2 ⊢
    rw [Finset.sum_range_succ]
    have hA := Nat.div_add_mod (2 * k) p
    have hB := Nat.mod_lt (2 * k) hp0
    have hC := Nat.div_add_mod (2 * (k + 1)) p
    have hmono : 2 * k / p ≤ 2 * (k + 1) / p := Nat.div_le_div_right (by omega)
    have hcase : 2 * (k + 1) / p = 2 * k / p ∨ 2 * (k + 1) / p = 2 * k / p + 1 := by
      have hlt : 2 * (k + 1) / p < 2 * k / p + 2 := by
        rw [Nat.div_lt_iff_lt_mul hp0]
        have hA2 := hA
        have hB2 := hB
        generalize 2 * k / p = m at hA2 ⊢
        generalize 2 * k % p = r at hA2 hB2
        linarith
      omega
    have hA' : (p : ℝ) * ((2 * k / p : ℕ) : ℝ) + ((2 * k % p : ℕ) : ℝ) = 2 * k := by
      exact_mod_cast hA
    have hB' : ((2 * k % p : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hB
    have hC' : (p : ℝ) * ((2 * (k + 1) / p : ℕ) : ℝ) + ((2 * (k + 1) % p : ℕ) : ℝ)
        = 2 * (k + 1) := by exact_mod_cast hC
    have hr0 : (0 : ℝ) ≤ ((2 * k % p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr0' : (0 : ℝ) ≤ ((2 * (k + 1) % p : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases hcase with hc | hc
    · rw [hc] at hC' ⊢
      push_cast
      constructor <;> linarith
    · rw [hc] at hC' ⊢
      push_cast at hC' ⊢
      constructor <;> linarith

theorem sum_six_max {P H : ℝ} {m : ℕ} (hP : 0 < P) (hm : m ≤ 5)
    (hlo : (m : ℝ) * P ≤ 2 * H) (hhi : 2 * H < ((m : ℝ) + 1) * P) :
    (∑ j ∈ Finset.range 6, max (2 * H - ((j : ℝ) + 1) * P) 0) =
      2 * (m : ℝ) * H - P * m * ((m : ℝ) + 1) / 2 := by
  interval_cases m <;> norm_num [Finset.sum_range_succ] at *
  all_goals
    repeat first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
    ring

theorem K_mul_legendre (n p : ℕ) (hn : 1 ≤ n) (hp : 0 < p) :
    ((40 * n : ℕ) : ℝ) * legendreTerm (3 / 40)
        ((p : ℝ) / ((40 * n : ℕ) : ℝ)) =
      -2 * ((37 * n : ℕ) : ℝ) * ((40 * n / p : ℕ) : ℝ) +
        ∑ j ∈ Finset.range 6, max (2 * ((37 * n : ℕ) : ℝ) - ((j : ℝ) + 1) * p) 0 := by
  have hK : (0 : ℝ) < (40 * n : ℕ) := by positivity
  have hfloor : ⌊1 / ((p : ℝ) / ((40 * n : ℕ) : ℝ))⌋₊ = 40 * n / p := by
    rw [one_div_div, Nat.floor_div_natCast, Nat.floor_natCast]
  have hlam : ((40 * n : ℕ) : ℝ) * (1 - 3 / 40) = (37 * n : ℕ) := by
    push_cast
    ring
  have hdiv : ((40 * n : ℕ) : ℝ) * ((p : ℝ) / ((40 * n : ℕ) : ℝ)) = p :=
    mul_div_cancel₀ _ hK.ne'
  unfold legendreTerm
  rw [hfloor, mul_add, Finset.mul_sum]
  congr 1
  · linear_combination (-2 * ((40 * n / p : ℕ) : ℝ)) * hlam
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_max_of_nonneg _ _ hK.le, mul_zero]
    congr 1
    linear_combination 2 * hlam - ((j : ℝ) + 1) * hdiv

theorem vSK_outer_formula (ν n p : ℕ) (hn : 1 ≤ n) (hpp : p.Prime)
    (h3 : 40 * n < 3 * p) :
    (vSK ν (40 * n) (3 * n) p : ℝ) =
      2 * ((37 * n : ℕ) : ℝ) * ((40 * n / p : ℕ) : ℝ) -
        2 * ∑ i ∈ Finset.range (37 * n), ((2 * i / p : ℕ) : ℝ) := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hp0 : 0 < p := hpp.pos
  have h13 : 13 * n + 1 ≤ p := by omega
  have h14 : 14 ≤ p := by omega
  have hsq : 2 * (37 * n) < p ^ 2 := by
    calc
      _ < (13 * n + 1) * 14 := by omega
      _ ≤ p * p := Nat.mul_le_mul h13 h14
      _ = p ^ 2 := (sq p).symm
  have hK2 : 40 * n < p ^ 2 := by omega
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  have hKval := factorial_val_small (p := p) hK2
  have hNval : padicValNat p (3 * n).factorial = 0 := factorial_val_lt (by omega)
  have h4val : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
    have := Nat.le_of_dvd (by norm_num : 0 < 4) h
    omega)
  have hrange : ∑ i ∈ Finset.Icc 1 (37 * n - 1), ((2 * i / p : ℕ) : ℝ) =
      ∑ i ∈ Finset.range (37 * n), ((2 * i / p : ℕ) : ℝ) := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      omega
    · intro i hi hni
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc, not_and_or, not_le] at hni
      have hi0 : i = 0 := by omega
      subst hi0
      simp
  have hfac : ∀ i ∈ Finset.Icc 1 (37 * n - 1),
      padicValNat p (2 * i).factorial = 2 * i / p := by
    intro i hi
    apply factorial_val_small
    have := (Finset.mem_Icc.mp hi).2
    omega
  have hv := congrArg (fun z : ℤ => (z : ℝ)) (vSK_formula ν (40 * n) (3 * n) p)
  rw [hshape, hKval, hNval, h4val] at hv
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_sum, Int.cast_zero, Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat,
    mul_zero, add_zero, sub_zero] at hv
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun t : ℕ => (t : ℝ)) (hfac i hi)), hrange] at hv
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv

theorem scalar_legendre_bounds (ν n p : ℕ) (hn : 1 ≤ n) (hpp : p.Prime)
    (h3 : 40 * n < 3 * p) :
    0 ≤ (vSK ν (40 * n) (3 * n) p : ℝ) + ((40 * n : ℕ) : ℝ) *
        legendreTerm (3 / 40) ((p : ℝ) / ((40 * n : ℕ) : ℝ)) ∧
    (vSK ν (40 * n) (3 * n) p : ℝ) + ((40 * n : ℕ) : ℝ) *
        legendreTerm (3 / 40) ((p : ℝ) / ((40 * n : ℕ) : ℝ)) ≤ 10 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hm5 : 2 * (37 * n) / p ≤ 5 := by
    have : 2 * (37 * n) / p < 6 := (Nat.div_lt_iff_lt_mul hpp.pos).mpr (by omega)
    omega
  have hdmR : (p : ℝ) * ((2 * (37 * n) / p : ℕ) : ℝ) +
      ((2 * (37 * n) % p : ℕ) : ℝ) = 2 * (37 * n : ℕ) := by
    exact_mod_cast Nat.div_add_mod (2 * (37 * n)) p
  have hmlR : ((2 * (37 * n) % p : ℕ) : ℝ) < p := by
    exact_mod_cast Nat.mod_lt (2 * (37 * n)) hpp.pos
  have hr0 : (0 : ℝ) ≤ ((2 * (37 * n) % p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm1 : ((2 * (37 * n) / p : ℕ) : ℝ) * p ≤ 2 * (37 * n : ℕ) := by linarith
  have hm2 : 2 * (37 * n : ℕ) < (((2 * (37 * n) / p : ℕ) : ℝ) + 1) * p := by linarith
  have hsum := sum_six_max hpR hm5 hm1 hm2
  have hpJ : 4 * ((p : ℝ) * Jfun ((37 * n : ℕ) / p)) =
      4 * ((2 * (37 * n) / p : ℕ) : ℝ) * (37 * n : ℕ) -
        p * ((2 * (37 * n) / p : ℕ) : ℝ) * (((2 * (37 * n) / p : ℕ) : ℝ) + 1) := by
    have hfl : ⌊2 * ((37 * n : ℕ) / (p : ℝ))⌋ = ((2 * (37 * n) / p : ℕ) : ℤ) := by
      rw [show 2 * ((37 * n : ℕ) / (p : ℝ)) = ((2 * (37 * n) : ℕ) : ℝ) / p by push_cast; ring]
      exact floor_natCast_div _ _ hpp.pos
    rw [Jfun, hfl, Int.cast_natCast]
    have hk : (p : ℝ) * ((37 * n : ℕ) / (p : ℝ)) = (37 * n : ℕ) := mul_div_cancel₀ _ hpR.ne'
    linear_combination (4 * ((2 * (37 * n) / p : ℕ) : ℝ)) * hk
  obtain ⟨hJ1, hJ2⟩ := jfun_sum_bounds hpp.two_le (37 * n)
  have hm5R : ((2 * (37 * n) / p : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hm5
  rw [vSK_outer_formula ν n p hn hpp h3, K_mul_legendre n p hn hpp.pos, hsum]
  constructor <;> linarith

#print axioms scalar_legendre_bounds

end
end BOuterScalar
