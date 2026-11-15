import Zeta5S.SharpOuterScope

/-!
L12/E311, Codex lane L, 2026-11-14. Status: PROOF-DRAFT pending gate.
Separately named sharp finite assembly, preserving E303/E305 raw definitions.
The exponent/normalizer architecture and integer lift adapt Firsching/Paul-Lez,
mo271/Zeta5@be1c0d82,Apery/Norm.lean:27-90,146-155,218-293,Apache-2.0.
These are the E305 arguments with only the outer correction strengthened by E310.
-/
open Finset Polynomial
namespace AperyS.AssemblyTarget

noncomputable section

def LpSharp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WOsharp s ν K N p⌋
  else Lsmall s ν K N p

def normalizerSharp (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-LpSharp s ν K N M p L)

/-- This target is deliberately separate from the approved raw NormalizationStatement. -/
def SharpNormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizerSharp s ν K N M L) * FS s ν K N (K - N)

theorem Lp_le_LpSharp (s ν K N M p : ℕ) (L : Allocations) :
    Lp s ν K N M p L ≤ LpSharp s ν K N M p L := by
  classical
  unfold Lp LpSharp
  split_ifs
  all_goals first | exact le_rfl |
    exact add_le_add le_rfl (Int.floor_mono (WO_le_WOsharp s ν K N p))

theorem local_valuation_sharp {p : ℕ} [Fact p.Prime]
    (s ν K N M : ℕ) (L : Allocations)
    (hodd : Odd s) (hs : 3 ≤ s) (hν : 2 ≤ ν) (hNK : N < K)
    (hshape : 2 * K ≤ degreeBound s ν K N) :
    GV p (FS s ν K N (K - N)) (LpSharp s ν K N M p L) := by
  unfold LpSharp
  split_ifs with h1 h2 h3 h4
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape
  · exact_mod_cast GV_FS_inner s ν K N L hodd hs h3
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape
  · exact_mod_cast GV_FS_outer_sharp s ν K N p hodd hs hν (by omega) h4
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape

theorem normalizerSharp_pos (s ν K N M : ℕ) (L : Allocations) :
    0 < normalizerSharp s ν K N M L := by
  unfold normalizerSharp
  apply Finset.prod_pos
  intro p hp
  have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast hp0) _

theorem normalizerSharp_le_raw (s ν K N M : ℕ) (L : Allocations) :
    normalizerSharp s ν K N M L ≤ normalizer s ν K N M L := by
  unfold normalizerSharp normalizer
  first
  | apply Finset.prod_le_prod₀
  | apply Finset.prod_le_prod
  · intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    positivity
  · intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hpp.one_le
    exact zpow_le_zpow_right₀ hp1 (neg_le_neg (Lp_le_LpSharp s ν K N M p L))

lemma padicValRat_normalizerSharp (s ν K N M p : ℕ) (L : Allocations) [Fact p.Prime] :
    padicValRat p (normalizerSharp s ν K N M L) =
      if p ≤ primeBound s K N then -LpSharp s ν K N M p L else 0 := by
  unfold normalizerSharp
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

theorem normalization_sharp (s ν K N M : ℕ) (L : Allocations)
    (hodd : Odd s) (hs : 3 ≤ s) (hν : 2 ≤ ν) (hNK : N < K)
    (hα : 6 * N ≤ K) (hbudget : K + (ν - 2) * N ≤ ((s - 1) / 2) * K)
    (hshape : 2 * K ≤ degreeBound s ν K N) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizerSharp s ν K N M L) * FS s ν K N (K - N) := by
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      GV p (C (normalizerSharp s ν K N M L) * FS s ν K N (K - N)) 0 := by
    intro p hp
    letI : Fact p.Prime := hp
    have hm : VG p (normalizerSharp s ν K N M L)
        (if p ≤ primeBound s K N then -LpSharp s ν K N M p L else 0 : ℤ) := by
      right
      rw [padicValRat_normalizerSharp]
    by_cases hbig : p ≤ primeBound s K N
    · rw [if_pos hbig] at hm
      have h := GV.C_mul hm (local_valuation_sharp s ν K N M L hodd hs hν hNK hshape)
      refine h.mono ?_
      push_cast
      linarith
    · rw [if_neg hbig] at hm
      simpa using GV.C_mul hm (GV_FS_big s ν K N hodd hs hν hNK hα hbudget (by omega))
  have hcoef : ∀ k, ∃ z : ℤ,
      (C (normalizerSharp s ν K N M L) * FS s ν K N (K - N)).coeff k = z := fun k =>
    rational_int_of_all_primes fun p hp => hall p hp k
  have hlift : C (normalizerSharp s ν K N M L) * FS s ν K N (K - N) ∈
      lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

theorem normalization_sharp_statement : SharpNormalizationStatement := by
  intro s ν K N M L hodd hs _heven hν hNK _hM hα hbudget hshape
  exact normalization_sharp s ν K N M L hodd hs hν hNK hα hbudget hshape

theorem LpSharp5_outer17 : LpSharp 5 6 40 3 400 17 upstreamAlloc = -100 := by
  rw [LpSharp, if_neg (by decide), if_neg (by decide), if_pos outer17_flag5, VS17, WOsharp5_17]
  norm_num

theorem LpSharp7_outer17 : LpSharp 7 6 40 3 400 17 upstreamAlloc = -128 := by
  rw [LpSharp, if_neg (by decide), if_neg (by decide), if_pos outer17_flag7, VS17, WOsharp7_17]
  norm_num

end
end AperyS.AssemblyTarget
