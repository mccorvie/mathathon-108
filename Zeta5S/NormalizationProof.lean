import Zeta5S.AssemblyProof

/-!
L7 stage 4 / E305, Codex lane L, 2026-11-14.
Finite raw arithmetic normalization, following Firsching/Paul-Lez,
mo271/Zeta5@be1c0d82 Apery/Norm.lean:157-293, Apache-2.0.
Large-prime Delta integrality is the general-s scope lemma from E302.
No asymptotic exponent or analytic zeta identification is asserted.
-/

open Finset Polynomial

namespace AperyS.AssemblyTarget

variable {p : ℕ} [hp : Fact p.Prime]

/-- The finite normalizer is positive, so the integer lift does not
arise by multiplying the determinant by zero. Adapted from Norm.lean:92-97. -/
theorem normalizer_pos (s ν K N M : ℕ) (L : Allocations) :
    0 < normalizer s ν K N M L := by
  unfold normalizer
  apply Finset.prod_pos
  intro p hp
  have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast hp0) _

lemma inverse_factorial_integral {k : ℕ} (hk : k < p) :
    VG p ((k.factorial : ℚ)⁻¹) 0 := by
  have hz : padicValNat p k.factorial = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by
      have := hp.out.dvd_factorial.mp h
      omega)
  have hle : (padicValRat p (k.factorial : ℚ) : ℚ) ≤ 0 := by
    rw [padicValRat.of_nat, hz]
    norm_num
  simpa using VG.inv (p := p) (r := 0) (by positivity : (k.factorial : ℚ) ≠ 0) hle

lemma scalar_integral_big (ν K N h : ℕ) (hNp : N < p) (hhp : 2 * h < p) :
    VG p (SS ν K N h) 0 := by
  have hnum : VG p ((K.factorial : ℚ) ^ (2 * h) * 4 ^ (h - 1)) 0 := by
    simpa using ((VG.natCast (p := p) K.factorial).pow (2 * h)).mul
      ((VG.natCast (p := p) 4).pow (h - 1))
  have hN : VG p (((N.factorial : ℚ) ^ (2 * ν * h))⁻¹) 0 := by
    rw [← inv_pow]
    simpa using (inverse_factorial_integral hNp).pow (2 * ν * h)
  have hP : VG p (∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2)⁻¹ 0 := by
    rw [← Finset.prod_inv_distrib]
    have hprod := VG.prod (p := p) (Icc 1 (h - 1))
      (f := fun i => (((2 * i).factorial : ℚ) ^ 2)⁻¹)
      (r := fun _ => 0) (fun i hi => by
        rw [← inv_pow]
        have hki : 2 * i < p := by
          have := Finset.mem_Icc.mp hi
          omega
        simpa using (inverse_factorial_integral hki).pow 2)
    simpa using hprod
  unfold SS
  rw [div_eq_mul_inv, mul_inv_rev]
  simpa using hnum.mul (hP.mul hN)

lemma GV_FS_big (s ν K N : ℕ) (hodd : Odd s) (hs : 3 ≤ s)
    (hν : 2 ≤ ν) (hNK : N < K) (hα : 6 * N ≤ K)
    (hbudget : K + (ν - 2) * N ≤ ((s - 1) / 2) * K)
    (hbig : primeBound s K N < p) :
    GV p (FS s ν K N (K - N)) 0 := by
  have hKp : K < p := by unfold primeBound at hbig; omega
  have hps : s ≤ p := by unfold primeBound at hbig; omega
  have hp7 : 7 ≤ p := by unfold primeBound at hbig; omega
  have hNp : N < p := by omega
  have hhp : 2 * (K - N) < p := by unfold primeBound at hbig; omega
  have hm : 2 * (p / 2) + 1 = p := by
    obtain ⟨a, ha⟩ := hp.out.odd_of_ne_two (by omega)
    omega
  have hDelta := determinant_integral_above_K hm s ν N K hodd hs hps hν
    (by omega) hp7 hKp hbudget
  have hScalar := scalar_integral_big ν K N (K - N) hNp hhp
  unfold FS
  simpa using GV.C_mul hScalar hDelta

-- Adapted from Apery/Norm.lean:218-244 (original padicValRat_mN).
lemma padicValRat_normalizer (s ν K N M p : ℕ) (L : Allocations) [Fact p.Prime] :
    padicValRat p (normalizer s ν K N M L) =
      if p ≤ primeBound s K N then -Lp s ν K N M p L else 0 := by
  unfold normalizer
  rw [padicValRat_finset_prod _ _ (fun q hq => by
    have := (Finset.mem_filter.mp hq).2.pos
    exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [padicValRat.zpow, padicValRat.of_nat]
  have hval : ∀ q ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
      (padicValNat p q : ℤ) = if q = p then 1 else 0 := by
    intro q hq
    have hq' : q.Prime := (Finset.mem_filter.mp hq).2
    haveI := Fact.mk hq'
    split_ifs with h
    · subst h; simp [padicValNat.self (Fact.out : q.Prime).one_lt]
    · rw [padicValNat_primes (Ne.symm h)]; rfl
  rw [Finset.sum_congr rfl (fun q hq => by rw [hval q hq])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : p ≤ primeBound s K N
  · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Fact.out⟩), if_pos h]
  · rw [if_neg (fun hm => h (by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega)),
      if_neg h]

-- Adapted from Apery/Norm.lean:247-267 (original rat_int_of_VG).
lemma rational_int_of_all_primes {q : ℚ}
    (h : ∀ p : ℕ, ∀ _ : Fact p.Prime, VG p q 0) : ∃ z : ℤ, q = z := by
  by_contra hne
  have hden : q.den ≠ 1 := fun h1 => hne ⟨q.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩
  set p := q.den.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime hden
  haveI := Fact.mk hpp
  have hdvd : p ∣ q.den := Nat.minFac_dvd _
  rcases h p ‹_› with h0 | hv
  · exact hne ⟨0, by simp [h0]⟩
  · have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hd
      have hc := q.reduced
      have : p ∣ Nat.gcd q.num.natAbs q.den :=
        Nat.dvd_gcd (Int.natCast_dvd.mp hd) hdvd
      rw [hc] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hdvd
    have e : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
    have hlt : padicValRat p q < 0 := by rw [e, h1]; omega
    have : (padicValRat p q : ℚ) < 0 := by exact_mod_cast hlt
    linarith

theorem normalization (s ν K N M : ℕ) (L : Allocations)
    (hodd : Odd s) (hs : 3 ≤ s) (hν : 2 ≤ ν) (hNK : N < K)
    (hα : 6 * N ≤ K) (hbudget : K + (ν - 2) * N ≤ ((s - 1) / 2) * K)
    (hshape : 2 * K ≤ degreeBound s ν K N) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizer s ν K N M L) * FS s ν K N (K - N) := by
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      GV p (C (normalizer s ν K N M L) * FS s ν K N (K - N)) 0 := by
    intro p hp
    letI : Fact p.Prime := hp
    have hm : VG p (normalizer s ν K N M L)
        (if p ≤ primeBound s K N then -Lp s ν K N M p L else 0 : ℤ) := by
      right
      rw [padicValRat_normalizer]
    by_cases hbig : p ≤ primeBound s K N
    · rw [if_pos hbig] at hm
      have h := GV.C_mul hm (local_valuation s ν K N M L hodd hs hν hNK hshape)
      refine h.mono ?_
      push_cast
      linarith
    · rw [if_neg hbig] at hm
      simpa using GV.C_mul hm (GV_FS_big s ν K N hodd hs hν hNK hα hbudget (by omega))
  have hcoef : ∀ k, ∃ z : ℤ,
      (C (normalizer s ν K N M L) * FS s ν K N (K - N)).coeff k = z := fun k =>
    rational_int_of_all_primes fun p hp => hall p hp k
  have hlift : C (normalizer s ν K N M L) * FS s ν K N (K - N) ∈
      lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

theorem normalization_statement : NormalizationStatement := by
  intro s ν K N M L hodd hs _heven hν hNK _hM hα hbudget hshape
  exact normalization s ν K N M L hodd hs hν hNK hα hbudget hshape

end AperyS.AssemblyTarget
