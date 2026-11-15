import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open Finset
namespace U11
noncomputable section

def logPoly (q : ℝ) (n : ℕ) : ℝ :=
  - ∑ i ∈ Finset.range n, (1-q) ^ (i+1) / ((i:ℝ)+1)

def logError (q : ℝ) (n : ℕ) : ℝ :=
  |1-q| ^ (n+1) / (1-|1-q|)

theorem logPoly_bounds (q : ℝ) (n : ℕ) (hq : |1-q|<1) :
    logPoly q n - logError q n ≤ Real.log q ∧
    Real.log q ≤ logPoly q n + logError q n := by
  have h := Real.abs_log_sub_add_sum_range_le hq n
  have he : (1-(1-q):ℝ)=q := by ring
  rw [he] at h
  have ha := abs_le.mp h
  dsimp [logPoly, logError]
  constructor <;> linarith [ha.1, ha.2]

theorem sqrt_bounds (q l u : ℝ) (hq : 0≤q) (_hl : 0≤l) (hu : 0≤u)
    (hls : l*l≤q) (hus : q≤u*u) :
    l≤Real.sqrt q ∧ Real.sqrt q≤u := by
  have hs := Real.sq_sqrt hq
  have hp := Real.sqrt_nonneg q
  constructor <;> nlinarith

theorem log_interval (x a b l u : ℝ) (ha : 0<a) (hax : a≤x) (hxb : x≤b)
    (hl : l≤Real.log a) (hu : Real.log b≤u) : l≤Real.log x ∧ Real.log x≤u := by
  constructor
  · exact hl.trans (Real.log_le_log ha hax)
  · exact (Real.log_le_log (ha.trans_le hax) hxb).trans hu

theorem log2_bounds : (69314718055:ℝ)/100000000000 ≤ Real.log 2 ∧ Real.log 2 ≤ 69314718057/100000000000 := by
  have h := logPoly_bounds (3/2) 40 (by norm_num)
  have h2 := logPoly_bounds (4/3) 40 (by norm_num)
  have he : Real.log (3/2) + Real.log (4/3) = Real.log (2:ℝ) := by
    rw [←Real.log_mul (by norm_num : (3/2:ℝ)≠0) (by norm_num : (4/3:ℝ)≠0)]
    norm_num
  norm_num [logPoly, logError, Finset.sum_range_succ] at h h2
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem log_scale (q r : ℝ) (k : ℤ) (hr : 0<r) (hqr : q=(2:ℝ)^k*r) :
    Real.log q = (k:ℝ)*Real.log 2 + Real.log r := by
  rw [hqr, Real.log_mul (zpow_ne_zero _ (by norm_num : (2:ℝ)≠0)) hr.ne', Real.log_zpow]

end
end U11
