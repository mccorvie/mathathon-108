import Zeta5S.LowRank

/-!
L11/E310, Codex lane L, 2026-11-14. Status: PROOF-DRAFT pending gate.
The raw low-rank estimate is Firsching/Paul-Lez, mo271/Zeta5@be1c0d82,
Apery/Arith/LowRank.lean:17-59, Apache-2.0. The separate zero-count bound
implements the sharper correction described in Fauzan (4.10)-(4.14).
No novelty claim; no claim that arbitrary rational negative weights suffice.
-/
open Finset Polynomial Matrix
namespace AperyS
variable {p : ℕ} [Fact p.Prime]

noncomputable def zeroWeightCount {h : ℕ} (w : Fin h → ℚ) : ℕ :=
  (Finset.univ.filter fun s => w s = 0).card

/-- Negative row weights must be at most -1/2. -/
theorem det_zero_count_bound {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X])
    (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ)
    (hgap : ∀ s, w s = 0 ∨ w s ≤ -1 / 2)
    (hA : ∀ s t, GV p (A s t) (w s + w t))
    (hU : ∀ s u, VG p (U s u) 0) (hV : ∀ u t, VG p (V u t) 0) :
    GV p (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det
      (2 * ∑ s, w s - zeroWeightCount w) := by
  classical
  let w' : Fin h → ℚ := fun s => if w s = 0 then -1 / 2 else w s
  have hle : ∀ s, w' s ≤ w s := by
    intro s; dsimp [w']; split_ifs with hz <;> first | linarith | exact le_rfl
  have hhalf : ∀ s, w' s ≤ -1 / 2 := by
    intro s; dsimp [w']; split_ifs with hz
    · exact le_rfl
    · exact (hgap s).resolve_left hz
  have hinv : VG p ((p : ℚ)⁻¹) (-1) := by
    simpa using VG.primePow (p := p) (-1)
  have hcorr : ∀ s t, GV p
      ((((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X])) s t) (w' s + w' t) := by
    intro s t
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    have huv : VG p (∑ u, U s u * V u t) 0 := by
      exact VG.sum _ fun u _ => by simpa using (hU s u).mul (hV u t)
    exact (GV.C (hinv.mul huv)).mono (by linarith [hhalf s, hhalf t])
  have hd := det_GV (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X])))
    w' w' (fun s t => ((hA s t).mono (add_le_add (hle s) (hle t))).add (hcorr s t))
  have hw' : ∀ s, w' s = w s - (if w s = 0 then (1 / 2 : ℚ) else 0) := by
    intro s; dsimp [w']; split_ifs with hz <;> norm_num [hz]
  have hsum : 2 * ∑ s, w' s = 2 * ∑ s, w s - zeroWeightCount w := by
    simp_rw [hw']
    rw [Finset.sum_sub_distrib]
    have hc : (∑ s : Fin h, if w s = 0 then (1 / 2 : ℚ) else 0) =
        (zeroWeightCount w : ℚ) / 2 := by
      simp [zeroWeightCount, ← Finset.sum_filter, Finset.sum_const]
      ring
    rw [hc]
    ring
  convert hd using 1
  linarith [hsum]

theorem det_lowrank_zero_bound {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X])
    (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ)
    (hgap : ∀ s, w s = 0 ∨ w s ≤ -1 / 2)
    (hA : ∀ s t, GV p (A s t) (w s + w t))
    (hU : ∀ s u, VG p (U s u) 0) (hV : ∀ u t, VG p (V u t) 0) :
    GV p (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det
      (2 * ∑ s, w s - (min r (zeroWeightCount w) : ℕ)) := by
  have hw : ∀ s, w s ≤ 0 := by intro s; rcases hgap s with hz | hh <;> linarith
  by_cases hr : r ≤ zeroWeightCount w
  · simpa only [min_eq_left hr] using det_lowrank_bound A U V w hw hA hU hV
  · simpa only [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hr))] using
      det_zero_count_bound A U V w hgap hA hU hV

end AperyS
