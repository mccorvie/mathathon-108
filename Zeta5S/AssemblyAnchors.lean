import Zeta5S.AtFiveNormData
import Zeta5S.AssemblyProof
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000
open AperyS
/-!
L7/E304 concrete non-vacuity anchors, Codex lane L, 2026-11-14.
Upstream allocation and exponent definitions copied (not their proofs) from
Firsching/Paul-Lez mo271/Zeta5@be1c0d82 Apery/Norm.lean:26-82, Apache-2.0.
All closed computations use decide +kernel; status assigned by the gate.
-/
namespace AperyS.AssemblyTarget
noncomputable def upstreamAlloc : Allocations := fun p => Upstream.allocI 1 p (p / 2)
theorem alloc13 : List.ofFn (upstreamAlloc 13) = [15,3,2,2,5,5,5] := by decide +kernel
theorem alloc13_sum : ∑ c, upstreamAlloc 13 c = 37 := by decide +kernel
theorem inner13_zero5 :
    tminS (5-1) (by decide : 1 ≤ 13/2) (upstreamAlloc 13) (BseS 5 6 13 40 3) ≤
    2 * (upstreamAlloc 13 0 : ℚ) + (BseS 5 6 13 40 3 0 - (5-1)) / 2 := by
  apply (tmin_leS (5-1) (by decide : 1 ≤ 13/2) (upstreamAlloc 13) (BseS 5 6 13 40 3)
    (c := ⟨2, by decide⟩) (by decide)).trans
  decide +kernel
theorem inner13_zero7 :
    tminS (7-1) (by decide : 1 ≤ 13/2) (upstreamAlloc 13) (BseS 7 6 13 40 3) ≤
    2 * (upstreamAlloc 13 0 : ℚ) + (BseS 7 6 13 40 3 0 - (7-1)) / 2 := by
  apply (tmin_leS (7-1) (by decide : 1 ≤ 13/2) (upstreamAlloc 13) (BseS 7 6 13 40 3)
    (c := ⟨2, by decide⟩) (by decide)).trans
  decide +kernel
theorem WI5 : WI 5 6 40 3 13 upstreamAlloc = -117/2 := by decide +kernel
theorem WI7 : WI 7 6 40 3 13 upstreamAlloc = -94 := by decide +kernel
theorem VS13 : vSK 6 40 3 13 = 50 := by decide +kernel
theorem VS17 : vSK 6 40 3 17 = 24 := by decide +kernel
theorem WO5 : WO 5 6 40 3 17 = -127 := by decide +kernel
theorem WO7 : WO 7 6 40 3 17 = -152 := by decide +kernel




theorem inner13_flag5 : InnerOK 5 6 40 3 13 upstreamAlloc := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, alloc13_sum, inner13_zero5⟩
  unfold Sep
  decide +kernel

theorem inner13_flag7 : InnerOK 7 6 40 3 13 upstreamAlloc := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, alloc13_sum, inner13_zero7⟩
  unfold Sep
  decide +kernel

theorem outer17_flag5 : OuterOK 5 40 3 17 := by unfold OuterOK; decide

theorem outer17_flag7 : OuterOK 7 40 3 17 := by unfold OuterOK; decide

theorem not_inner2_5 : ¬ InnerOK 5 6 40 3 2 upstreamAlloc := by
  rintro ⟨_, _, hps, _⟩
  norm_num at hps

theorem exponent5_fallback2 : Lp 5 6 40 3 400 2 upstreamAlloc = -1665 := by
  rw [Lp, if_neg (by decide), if_pos (by decide), if_neg not_inner2_5]
  decide +kernel

theorem exponent5_small2 : Lp 5 6 40 3 20 2 upstreamAlloc = -1665 := by
  rw [Lp, if_pos (by decide)]
  decide +kernel

theorem exponent5_inner13 : Lp 5 6 40 3 400 13 upstreamAlloc = -67 := by
  rw [Lp, if_neg (by decide), if_pos (by decide), if_pos inner13_flag5, VS13, WI5]
  norm_num

theorem exponent7_inner13 : Lp 7 6 40 3 400 13 upstreamAlloc = -138 := by
  rw [Lp, if_neg (by decide), if_pos (by decide), if_pos inner13_flag7, VS13, WI7]
  norm_num

theorem exponent5_outer17 : Lp 5 6 40 3 400 17 upstreamAlloc = -103 := by
  rw [Lp, if_neg (by decide), if_neg (by decide), if_pos outer17_flag5, VS17, WO5]
  norm_num

theorem exponent7_outer17 : Lp 7 6 40 3 400 17 upstreamAlloc = -128 := by
  rw [Lp, if_neg (by decide), if_neg (by decide), if_pos outer17_flag7, VS17, WO7]
  norm_num

theorem upstream_inner13_flag : Upstream.InnerOK 1 13 := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, ?_, ?_⟩
  · unfold Sep; decide +kernel
  · simpa [upstreamAlloc] using alloc13_sum
  · simpa [upstreamAlloc, Upstream.tmin_eq_tminS, Upstream.Bse_eq_BseS,
      show (5 : ℚ) - 1 = 4 by norm_num] using inner13_zero5

theorem upstream_exponent2 : Upstream.Lp 1 2 = -1665 := by
  have hn : ¬ Upstream.InnerOK 1 2 := by rintro ⟨_, _, hp, _⟩; norm_num at hp
  rw [Upstream.Lp, if_neg (by decide), if_pos (by decide), if_neg hn]
  decide +kernel

theorem upstream_exponent13 : Upstream.Lp 1 13 = -67 := by
  rw [Upstream.Lp, if_neg (by decide), if_pos (by decide), if_pos upstream_inner13_flag]
  have hv : Upstream.vSK 1 13 = 50 := by decide +kernel
  have hw : Upstream.WI 1 13 = -117/2 := by decide +kernel
  rw [hv, hw]
  norm_num

theorem upstream_exponent17 : Upstream.Lp 1 17 = -103 := by
  have ho : Upstream.OuterOK 1 17 := by unfold Upstream.OuterOK; decide
  rw [Upstream.Lp, if_neg (by decide), if_neg (by decide), if_pos ho]
  have hv : Upstream.vSK 1 17 = 24 := by decide +kernel
  have hw : Upstream.WO 1 17 = -127 := by decide +kernel
  rw [hv, hw]
  norm_num

theorem exponent5_upstream_anchors :
    Lp 5 6 40 3 400 2 upstreamAlloc = Upstream.Lp 1 2 ∧
    Lp 5 6 40 3 400 13 upstreamAlloc = Upstream.Lp 1 13 ∧
    Lp 5 6 40 3 400 17 upstreamAlloc = Upstream.Lp 1 17 := by
  rw [exponent5_fallback2, upstream_exponent2, exponent5_inner13, upstream_exponent13,
    exponent5_outer17, upstream_exponent17]
  exact ⟨rfl, rfl, rfl⟩

end AperyS.AssemblyTarget
