import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.IntervalCases
import Mathathon.P108.DeltaEq.HankelCheck
import Mathathon.P108.DeltaEq.Pt.X01
import Mathathon.P108.DeltaEq.Pt.Points

/-!
# #108 L4: `det G_40(X) = DeltaLit(X)`, sorry-free, without importing `LaiSkip`

EVENT WORK (#108, lane L task L4, Claude Opus 5.5, Sat Nov 14 2026, started 15:33 PT).

`Delta_eq'` is `Skip.Delta_eq` (`Mathathon/P108/LaiSkip.lean`) stated with `DetG0`'s verbatim
copies of the definitions, so that `LaiSkip.lean` can import this file and close its `sorry` by
`exact DeltaEq.Delta_eq'` (the kernel unfolds the copies; `Main.lean` checks exactly this).
Route (lane L's E306 proposal, with an `O(n²)` Hankel checker instead of `L D Lᵀ`):
1. degree: `natDegree (det G_40) ≤ 37`, `natDegree DeltaLit ≤ 37` (`Bridge.lean`);
2. bridge: a `true` point certificate `ptCheck x` gives `det G_40(x) = DeltaLit(x)`
   (`Bridge.lean`, from `hankel_det_of_pass` in `Hankel.lean` and `hankel_lits`);
3. certificates at the 38 points `x = 0, 1, …, 37` (`Pt/X01.lean`, `Pt/Points.lean`);
4. interpolation: `Polynomial.eq_of_degrees_lt_of_eval_finset_eq`.
No `sorry`, no `native_decide`, no axiom.
-/

namespace Mathathon.P108.Skip.DeltaEq

open Polynomial

theorem ptCheck_all : ∀ n < 38, ptCheck ((n : ℕ) : ℚ) = true := by
  intro n hn
  interval_cases n
  exacts [ptCheck_00, ptCheck_01, ptCheck_02, ptCheck_03, ptCheck_04, ptCheck_05, ptCheck_06,
    ptCheck_07, ptCheck_08, ptCheck_09, ptCheck_10, ptCheck_11, ptCheck_12, ptCheck_13,
    ptCheck_14, ptCheck_15, ptCheck_16, ptCheck_17, ptCheck_18, ptCheck_19, ptCheck_20,
    ptCheck_21, ptCheck_22, ptCheck_23, ptCheck_24, ptCheck_25, ptCheck_26, ptCheck_27,
    ptCheck_28, ptCheck_29, ptCheck_30, ptCheck_31, ptCheck_32, ptCheck_33, ptCheck_34,
    ptCheck_35, ptCheck_36, ptCheck_37]

/-- **`det G_40(X) = DeltaLit(X)`** (`s = 11`, `ν = 2`, `K = 40`), with `DetG0`'s copies of the
definitions: the statement of `Skip.Delta_eq` up to unfolding `Skip.Delta`. -/
theorem Delta_eq' : (DetG0.G 11 2 1).det = DeltaLit' := by
  have hcard : ((Finset.range 38).image (fun n : ℕ => (n : ℚ))).card = 38 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  refine eq_of_degrees_lt_of_eval_finset_eq ((Finset.range 38).image (fun n : ℕ => (n : ℚ)))
    ?_ ?_ ?_
  · rw [hcard]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le Delta_natDegree_le)
  · rw [hcard]
    exact degree_le_natDegree.trans_lt
      (by exact_mod_cast Nat.lt_succ_of_le DeltaLit_natDegree_le)
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    exact eval_Delta_of_check hankel_lits _ (ptCheck_all n (Finset.mem_range.1 hn))

end Mathathon.P108.Skip.DeltaEq
