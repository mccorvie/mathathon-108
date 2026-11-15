import Prefix40
import PackageTail.Primitive
import Mathlib.Analysis.Calculus.Deriv.ZPow
/- U66/E261, Codex. PROOF-DRAFT: unchanged U53 analytic helpers extracted without numerical chunks. -/
noncomputable section
open MeasureTheory Set Real Mathathon.P108
namespace U53
/-- PROOF-DRAFT: primitive vanishes at the smaller period boundary. -/
lemma G40 : U22.G 40 = 0 := by
  norm_num [U22.G,U22.B,U22.P,U22.frac,U22.lam,U22.alpha]

lemma power_cont (n : ℤ) {M : ℝ} (hM : 40≤M) :
    ContinuousOn (fun x : ℝ=>x^n) (uIcc (40:ℝ) M) := by
  apply ContinuousOn.zpow₀ continuousOn_id
  intro x hx
  rw [uIcc_of_le hM] at hx
  left
  change x≠0
  linarith [hx.1]

lemma power_integral2 {M : ℝ} (hM : 40≤M) :
    (∫ x in (40:ℝ)..M,x^(-2:ℤ))=1/40-M^(-1:ℤ) := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
    ring
  · rw [uIcc_of_le hM]
    intro h
    linarith [h.1]

lemma power_integral3 {M : ℝ} (hM : 40≤M) :
    (∫ x in (40:ℝ)..M,x^(-3:ℤ))=(1/1600-M^(-2:ℤ))/2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num,?_⟩)]
  · norm_num
    ring
  · rw [uIcc_of_le hM]
    intro h
    linarith [h.1]

/-- PROOF-DRAFT: integrability of the literal package tail from40. -/
lemma R_tail_integrable {M : ℝ} (hM : 40 ≤ M) :
    IntervalIntegrable (fun x=>innerR 7 6 U22.alpha x/x^3) volume 40 M := by
  exact (innerR_div_intervalIntegrable 7 6 U22.alpha 40 (by norm_num)).symm.trans
    (innerR_div_intervalIntegrable 7 6 U22.alpha M (by linarith))

end U53
