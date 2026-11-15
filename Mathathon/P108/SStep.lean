import Mathathon.P108.InnerShift
import Mathathon.P108.Integrable
import Mathathon.P108.OuterValues

/-!
# #108: the U-free s-step of the package margin (EVENT WORK)

Formalizer (Claude Opus 5.5), Fri Nov 13 2026. Claims formalized (criterion5 derivation.md §5,
Corollary 4; E14; sstep_exact.out):

  Θ(s+2, ν; M, ρ) − Θ(s, ν; M, ρ) = 2λ/3 + I_out(s+2, ν) − I_out(s, ν)   for every M and every U,

with Θ(s, ν, α; M, U) = U + I_out(s, ν, α) + (s+1)λ/M + ∫_3^M R_(s,ν)(x) x⁻³ dx (derivation §5; Lai
Thm 9.3 RHS without E_M, plus U), and at α = 3/40: 751/768 for ν = 6, s = 5 → 7, and 12817/14400 for
ν = 8, s = 5 → 7.

Differences from the claim (read before citing):
* `U` is an arbitrary real (the analytic bound U(ν; ρ) = λM₀ − I(ρ) + C*(ν) is not formalized; the
  point is that it is the same number on both sides, which is Xu's statement that U is s-free);
* no integrability hypothesis: `innerR_div_intervalIntegrable` (Integrable.lean) proves that
  `x ↦ R_(s,ν)(x)/x³` is interval integrable on [3, M] for all real s, ν, α;
* `I_out` and `R` are the definitions in `OuterDefs.lean` / `InnerShift.lean` (transcriptions of the
  advocate's formulas and code), not a formal derivation of them from Fauzan's valuation bounds.
-/

open MeasureTheory Set

namespace Mathathon.P108

noncomputable section

/-- The package margin `Θ(s, ν, α; M, U) = U + I_out(s, ν, α) + (s+1)λ/M + ∫_3^M R_(s,ν)(x)/x³ dx`,
`λ = 1 − α` (criterion5 derivation.md §5 with `U = U(ν, α; ρ)` left as a parameter). -/
def thetaPkg (s ν α M U : ℝ) : ℝ :=
  U + Iout s ν α + (s + 1) * (1 - α) / M + ∫ x in (3:ℝ)..M, innerR s ν α x / x ^ 3

/-- **Corollary 4 (general s).** For all real `s, ν, α, U` and `M ≥ 3`,
`Θ(s+2) − Θ(s) = 2λ/3 + I_out(s+2) − I_out(s)`: independent of `M` and of `U`. -/
theorem thetaPkg_sstep (s ν α M U : ℝ) (hM : 3 ≤ M) :
    thetaPkg (s + 2) ν α M U - thetaPkg s ν α M U
      = 2 * (1 - α) / 3 + (Iout (s + 2) ν α - Iout s ν α) := by
  have h := inner_crude_sstep s ν α M hM (innerR_div_intervalIntegrable s ν α M hM)
  unfold thetaPkg
  linarith

/-- The exact U-free s-step at ν = 6, α = 3/40, s = 5 → 7: `2λ/3 + I_out(7,6) − I_out(5,6) = 751/768`
(= 37/60 + 1387/3840). -/
theorem sstep_value_nu6 :
    2 * (1 - (3/40 : ℝ)) / 3 + (Iout 7 6 (3/40) - Iout 5 6 (3/40)) = 751 / 768 := by
  rw [Iout_7_6, Iout_5_6]; norm_num

/-- The exact U-free s-step at ν = 8, α = 3/40, s = 5 → 7: `12817/14400` (= 37/60 + 3937/14400). -/
theorem sstep_value_nu8 :
    2 * (1 - (3/40 : ℝ)) / 3 + (Iout 7 8 (3/40) - Iout 5 8 (3/40)) = 12817 / 14400 := by
  rw [Iout_7_8, Iout_5_8]; norm_num

/-- **E14, ν = 6:** `Θ(7, 6; M, U) − Θ(5, 6; M, U) = 751/768` at α = 3/40, for every `M ≥ 3` and
every real `U`. -/
theorem theta_sstep_7_6 (M U : ℝ) (hM : 3 ≤ M) :
    thetaPkg 7 6 (3/40) M U - thetaPkg 5 6 (3/40) M U = 751 / 768 := by
  have h := thetaPkg_sstep 5 6 (3/40) M U hM
  norm_num at h
  rw [← sstep_value_nu6]
  norm_num
  linarith

/-- **E14, ν = 8:** `Θ(7, 8; M, U) − Θ(5, 8; M, U) = 12817/14400` at α = 3/40, for every `M ≥ 3`
and every real `U`. -/
theorem theta_sstep_7_8 (M U : ℝ) (hM : 3 ≤ M) :
    thetaPkg 7 8 (3/40) M U - thetaPkg 5 8 (3/40) M U = 12817 / 14400 := by
  have h := thetaPkg_sstep 5 8 (3/40) M U hM
  norm_num at h
  rw [← sstep_value_nu8]
  norm_num
  linarith

end

end Mathathon.P108
