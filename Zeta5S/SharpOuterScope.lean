import Zeta5S.SharpOuterMain

/-!
L11/E310, Codex lane L. Status: PROOF-DRAFT pending repository gate.
Same finite hypotheses as outer_boundS_clamped, with the sharper
min(raw rank, exact number of zero outer rows) of Fauzan (4.13)-(4.14).
No change to the already approved raw assembly definitions.
-/
open Finset Polynomial
namespace AperyS
variable {p m : ℕ} [Fact p.Prime]

theorem outer_boundS_sharp_clamped
    (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hodd : Odd s) (hs : 3 ≤ s) (hps : s ≤ p) (hν : 2 ≤ ν) (hNK : N ≤ K)
    (hp7 : 7 ≤ p) (hK3 : K < 3 * p) (hK : 2 * K < p ^ 2) (hpN : N < p) :
    GV p (ΔS s ν K N (K - N))
      (2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (AssemblyTarget.rawRank s ν K N p) (outerZeroCount hm s ν N K) : ℕ) : ℚ)) := by
  have hcut := momentCutS_spec s p hodd hs (by omega)
  have hq : 1 ≤ ((s - 1) / 2) * (p - 1) := by
    unfold momentCutS at hcut
    omega
  have h := outer_boundS_sharp hm s ν N K hodd (by omega) hps (by omega)
    (momentCutS s p) (le_of_eq hcut.2) hcut.1 hp7 hK3 hK hpN
  simpa only [momentCutS, outer_rank_loss_eq ν K N _ hν hNK hq,
    AssemblyTarget.rawRank] using h

namespace AssemblyTarget
noncomputable def WOsharp (s ν K N p : ℕ) : ℚ := by
  classical
  exact if hpp : p.Prime then
    letI : Fact p.Prime := ⟨hpp⟩
    if hm : 2 * (p / 2) + 1 = p then
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (rawRank s ν K N p) (outerZeroCount hm s ν N K) : ℕ) : ℚ)
    else 0
  else 0

theorem WO_le_WOsharp (s ν K N p : ℕ) : WO s ν K N p ≤ WOsharp s ν K N p := by
  classical
  unfold WO WOsharp
  split_ifs with hp hm
  · letI : Fact p.Prime := ⟨hp⟩
    have h : (min (rawRank s ν K N p) (outerZeroCount hm s ν N K) : ℕ) ≤
        rawRank s ν K N p := min_le_left _ _
    have hq : ((min (rawRank s ν K N p) (outerZeroCount hm s ν N K) : ℕ) : ℚ) ≤
        (rawRank s ν K N p : ℚ) := by exact_mod_cast h
    unfold rawRank at hq ⊢
    linarith
  all_goals exact le_rfl

theorem GV_FS_outer_sharp (s ν K N p : ℕ) [Fact p.Prime]
    (hodd : Odd s) (hs : 3 ≤ s) (hν : 2 ≤ ν) (hNK : N ≤ K)
    (hflag : OuterOK s K N p) :
    GV p (FS s ν K N (K - N)) (vSK ν K N p + ⌊WOsharp s ν K N p⌋) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hm, hps, hp7, hK3, hK, hpN⟩ := hflag
  have h := outer_boundS_sharp_clamped hm s ν N K hodd hs hps hν hNK hp7 hK3 hK hpN
  have he : GV p (ΔS s ν K N (K - N)) (WOsharp s ν K N p) := by
    simpa only [WOsharp, dif_pos hp, dif_pos hm] using h
  have hv : VG p (SS ν K N (K - N)) (vSK ν K N p : ℚ) := by
    exact Or.inr le_rfl
  unfold FS
  exact (GV.C_mul hv he).mono (by
    have := Int.floor_le (WOsharp s ν K N p)
    push_cast
    linarith)

theorem sharp_zero17_s5 : @outerZeroCount 17 8 (by exact ⟨by decide⟩) (by decide) 5 6 3 40 = 17 := by
  decide +kernel

theorem sharp_zero17_s7 : @outerZeroCount 17 8 (by exact ⟨by decide⟩) (by decide) 7 6 3 40 = 14 := by
  decide +kernel

theorem WOsharp5_17 : WOsharp 5 6 40 3 17 = -124 := by
  decide +kernel

theorem WOsharp7_17 : WOsharp 7 6 40 3 17 = -152 := by
  decide +kernel

end AssemblyTarget
end AperyS
