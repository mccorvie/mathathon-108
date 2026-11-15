import OuterScalar

/- E424 lane B driver. PROOF-DRAFT until gate. Source architecture:
PRIOR Deicyde/zeta7-irrational@be55b3a4/InnerLimiting.lean1180-1246.
Actual arbitrary-nu SS/vSK and root innerN/Jfun are unchanged. -/
open Finset
namespace BInnerScalar
noncomputable section
open AperyS AperyS.AssemblyTarget Mathathon.P108 BOuterAboveK BOuterScalar

theorem vSK_small_square_formula (ν n p : ℕ) (hn : 1 ≤ n) (hpp : p.Prime)
    (hp5 : 5 ≤ p) (hK2 : 40 * n < p ^ 2) (hH2 : 2 * (37 * n) < p ^ 2) :
    (vSK ν (40 * n) (3 * n) p : ℝ) =
      2 * ((37 * n : ℕ) : ℝ) * ((40 * n / p : ℕ) : ℝ) -
        2 * (ν : ℝ) * ((37 * n : ℕ) : ℝ) * ((3 * n / p : ℕ) : ℝ) -
        2 * ∑ i ∈ Finset.range (37 * n), ((2 * i / p : ℕ) : ℝ) := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hshape : 40 * n - 3 * n = 37 * n := by omega
  have hKval := factorial_val_small (p := p) hK2
  have hNval := factorial_val_small (p := p) (k := 3 * n) (by omega)
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
    Int.cast_ofNat, Int.cast_sum, Int.cast_zero, Nat.cast_zero, Nat.cast_mul,
    Nat.cast_ofNat, mul_zero, add_zero, sub_zero] at hv
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun t : ℕ => (t : ℝ)) (hfac i hi)), hrange] at hv
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv

theorem scalar_inner_bounds (ν n M p : ℕ) (hn : 1 ≤ n) (hpp : p.Prime)
    (hp5 : 5 ≤ p) (hK2 : 40 * n < p ^ 2) (hH2 : 2 * (37 * n) < p ^ 2)
    (hKM : 40 * n < p * M) :
    0 ≤ (vSK ν (40 * n) (3 * n) p : ℝ) - (p : ℝ) *
        innerN (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) ∧
      (vSK ν (40 * n) (3 * n) p : ℝ) - (p : ℝ) *
        innerN (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) ≤ 4 * M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hfl1 : ⌊((40 * n : ℕ) : ℝ) / p⌋ = ((40 * n / p : ℕ) : ℤ) :=
    floor_natCast_div _ _ hpp.pos
  have hαx : (3 / 40 : ℝ) * (((40 * n : ℕ) : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
    push_cast
    ring
  have hfl2 : ⌊(3 / 40 : ℝ) * (((40 * n : ℕ) : ℝ) / p)⌋ = ((3 * n / p : ℕ) : ℤ) := by
    rw [hαx]
    exact floor_natCast_div _ _ hpp.pos
  have hlamx : (1 - 3 / 40 : ℝ) * (((40 * n : ℕ) : ℝ) / p) = ((37 * n : ℕ) : ℝ) / p := by
    push_cast
    ring
  have hplamx : (p : ℝ) * (1 - 3 / 40) * (((40 * n : ℕ) : ℝ) / p) = (37 * n : ℕ) := by
    rw [mul_assoc, hlamx, mul_div_cancel₀ _ hpR.ne']
  have hpN : (p : ℝ) * innerN (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p) =
      2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) -
        2 * (ν : ℝ) * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) -
        2 * ((p : ℝ) * Jfun ((37 * n : ℕ) / p)) := by
    rw [innerN, hfl1, hfl2, hlamx]
    simp only [Int.cast_natCast]
    linear_combination (2 * ((40 * n / p : ℕ) : ℝ) -
      2 * (ν : ℝ) * ((3 * n / p : ℕ) : ℝ)) * hplamx
  obtain ⟨hJ1, hJ2⟩ := jfun_sum_bounds hpp.two_le (37 * n)
  have h2h : ((2 * (37 * n) / p : ℕ) : ℝ) ≤ 2 * M := by
    have h : 2 * (37 * n) / p ≤ 2 * M := by
      apply Nat.div_le_of_le_mul
      nlinarith
    exact_mod_cast h
  rw [vSK_small_square_formula ν n p hn hpp hp5 hK2 hH2, hpN]
  constructor <;> linarith

theorem scalar_inner_fixed_shape (ν n M p : ℕ) (hM : 40 ≤ M) (hn : M ^ 2 ≤ n)
    (hpp : p.Prime) (hKM : 40 * n < p * M) :
    |(vSK ν (40 * n) (3 * n) p : ℝ) - (p : ℝ) *
      innerN (ν : ℝ) (3 / 40) (((40 * n : ℕ) : ℝ) / p)| ≤ 4 * M := by
  have hn1 : 1 ≤ n := by nlinarith
  have hpbig : 40 * M < p := by
    by_contra h
    have hprod := Nat.mul_le_mul_right M (show p ≤ 40 * M by omega)
    nlinarith
  have hpmul := Nat.mul_lt_mul_of_pos_right hpbig hpp.pos
  have h1600 : 1600 * n < p ^ 2 := by nlinarith
  obtain ⟨h0, h1⟩ := scalar_inner_bounds ν n M p hn1 hpp (by omega)
    (by nlinarith) (by nlinarith) hKM
  rw [abs_of_nonneg h0]
  exact h1

#print axioms scalar_inner_bounds
#print axioms scalar_inner_fixed_shape
end
end BInnerScalar
