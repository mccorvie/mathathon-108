import Zeta5S.AssemblyData

/-!
L7 stage 4 / E303, Codex lane L, Sat Nov 14 2026.
Adapted from Firsching/Paul-Lez mo271/Zeta5@be1c0d82,
Apery/Norm.lean:112-155, Apache-2.0. Local finite valuation assembly only.
The raw outer rank loss and arbitrary allocation/fallback scope are unchanged.
Claim status is assigned by the driver's repository gate and ledger.
-/

open Finset Polynomial

namespace AperyS.AssemblyTarget

variable {p : ℕ} [Fact p.Prime]

lemma GV_FS_of_Delta (s ν K N : ℕ) {r : ℚ}
    (h : GV p (ΔS s ν K N (K - N)) r) :
    GV p (FS s ν K N (K - N)) ((vSK ν K N p : ℚ) + r) := by
  unfold FS
  have hS : VG p (SS ν K N (K - N)) (vSK ν K N p) := Or.inr (le_refl _)
  exact GV.C_mul hS h

/-- All-prime fallback, not restricted by the branch cutoff p*M<=K. -/
theorem GV_FS_Lsmall (s ν K N : ℕ) (hodd : Odd s) (hs : 3 ≤ s)
    (hNK : N < K) (hshape : 2 * K ≤ degreeBound s ν K N) :
    GV p (FS s ν K N (K - N)) (Lsmall s ν K N p) := by
  have h := small_prime_boundS (p := p) s hodd hs ν K N (K - N)
    (by omega) (by omega) hshape
  simpa only [Lsmall, degreeBound, Int.cast_neg, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Nat.cast_add, Nat.cast_one, Int.cast_one] using h

lemma GV_FS_inner (s ν K N : ℕ) (L : Allocations) (hodd : Odd s) (hs : 3 ≤ s)
    (hflag : InnerOK s ν K N p L) :
    GV p (FS s ν K N (K - N)) (vSK ν K N p + ⌊2 * WI s ν K N p L⌋) := by
  obtain ⟨hm, hm1, hps, hsep, hK, hdeg, hsum, hZ⟩ := hflag
  have hΔ := inner_bound_capS s hodd hs hps hm hm1 ν K N (K - N)
    (L p) hsum hsep hK hdeg hZ
  have hW : WI s ν K N p L =
      ∑ x, wcapS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) x := by
    unfold WI; rw [dif_pos hm1]
  rw [← hW] at hΔ
  have h := GV_FS_of_Delta s ν K N hΔ
  refine h.mono ?_
  push_cast
  have := Int.floor_le (2 * WI s ν K N p L)
  linarith

lemma GV_FS_outer (s ν K N : ℕ) (hodd : Odd s) (hs : 3 ≤ s)
    (hν : 2 ≤ ν) (hNK : N ≤ K) (hflag : OuterOK s K N p) :
    GV p (FS s ν K N (K - N)) (vSK ν K N p + ⌊WO s ν K N p⌋) := by
  obtain ⟨hm, hps, hp7, hK3, hK, hpN⟩ := hflag
  have hΔ := outer_boundS_clamped hm s ν N K hodd hs hps hν hNK hp7 hK3 hK hpN
  have hW : WO s ν K N p =
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1)) : ℕ) : ℚ) := by
    unfold WO; rw [dif_pos (Fact.out : p.Prime), dif_pos hm]
  rw [← hW] at hΔ
  have h := GV_FS_of_Delta s ν K N hΔ
  refine h.mono ?_
  push_cast
  have := Int.floor_le (WO s ν K N p)
  linarith

/-- Finite raw local exponent, valid for every prime, every supplied allocation,
and every cutoff M. Failed finite side conditions use the all-prime fallback. -/
theorem local_valuation (s ν K N M : ℕ) (L : Allocations)
    (hodd : Odd s) (hs : 3 ≤ s) (hν : 2 ≤ ν) (hNK : N < K)
    (hshape : 2 * K ≤ degreeBound s ν K N) :
    GV p (FS s ν K N (K - N)) (Lp s ν K N M p L) := by
  unfold Lp
  split_ifs with h1 h2 h3 h4
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape
  · exact_mod_cast GV_FS_inner s ν K N L hodd hs h3
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape
  · exact_mod_cast GV_FS_outer s ν K N hodd hs hν (by omega) h4
  · exact GV_FS_Lsmall s ν K N hodd hs hNK hshape

/-- The exact proposition approved by the integrator at 13:35 PT. -/
theorem local_valuation_statement : LocalValuationStatement := by
  intro s ν K N M L hodd hs _heven hν hNK _hM _hα _hbudget hshape p hp
  letI : Fact p.Prime := hp
  exact local_valuation s ν K N M L hodd hs hν hNK hshape

end AperyS.AssemblyTarget
