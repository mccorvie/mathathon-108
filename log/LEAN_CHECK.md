# Lean check
Run 2026-11-14T22:21-08:00 on `MergeEntry` in `/Users/mathathon/code/mathathon/problems/108-zeta-odd-autopsy/evidence/L-merge/project`.
**Overall: PASS**


## Versions
- PASS: Lean v4.35.0, Mathlib v4.35.0

## Build
- PASS

## Declarations

| Declaration | Verdict | Axioms | Problem |
|---|---|---|---|
| `AperyS.tauXs_direct` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.normalization_statement` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.local_valuation_sharp` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.normalization_sharp_statement` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.thetaPkg_sstep` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.theta_sstep_7_6` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.sstep_ge` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.thetaPkg_odd_ge` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.gain58_formal` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U18.arithmetic_allM_strict` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U18.theta_allM_gt` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `BFullBridge.explicit_normalizer_limit_statement` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `BFullBridge.zeta_seven_explicit_margin_positive_statement` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U44.optimized_energy_floor_real` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U44.fieldSup_ne_top` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U44.package_margin_optimized` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U44.optimal_energy_floor_real` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U43.V6_coercive` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U42.fieldSup_ne_bot` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U42.sigma_comparison_class` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `BZetaIdentification.riemannZeta_eq_zetaS` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.WI_sstep_bounds` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.Lp_inner_sstep` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.switch_Lp5` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.switch_Lp7` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `AperyS.AssemblyTarget.selected_Lp_can_increase` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.classLoss_witness` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.lai_offset_gap_7_2` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.Skip.lai_skip_witness` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `Mathathon.P108.Skip.Delta_eq` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCompactWithClosing.irrational_five` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCompactCurrent.irrational_five` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCertificateSplit.irrational_five` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCertificateSplit.finite_real_bound` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CSplitField.local_field_certificate` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `BSymbolicCriterion.criterion_standard` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `LMergeCompactAnalytic.finite_real_bound` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCertificateSplit.closing` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `SplitClosing.closing_neg` | **PASS** | propext, Classical.choice, Quot.sound |  |

## Statements (a human must compare each with the claim in the report)

### `AperyS.tauXs_direct`
```lean
@AperyS.tauXs_direct : ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (s : ℕ),
  2 ≤ s →
    s ≤ p →
      ∀ (κ : ℚ),
        AperyS.VG p κ 0 →
          ∀ (Z : Multiset ℤ) (Pl : Finset ℤ),
            AperyS.Sep p Pl →
              (∀ r ∈ Pl, AperyS.dd r < p ^ 2) →
                Z.card - Pl.card + 1 < p ^ 2 →
                  ∀ (β : ℚ),
                    (∀ (c : ZMod p), β ≤ ↑(AperyS.cnt p Z c) - ↑(AperyS.plc p Pl c).card) →
                      AperyS.GV p (AperyS.tauXs s (AperyS.numOf κ Z) Pl) (β - (↑s - 1))
```
### `AperyS.AssemblyTarget.normalization_statement`
```lean
AperyS.AssemblyTarget.normalization_statement : AperyS.AssemblyTarget.NormalizationStatement
```
### `AperyS.AssemblyTarget.local_valuation_sharp`
```lean
@AperyS.AssemblyTarget.local_valuation_sharp : ∀ {p : ℕ} [Fact (Nat.Prime p)] (s ν K N M : ℕ)
  (L : AperyS.AssemblyTarget.Allocations),
  Odd s →
    3 ≤ s →
      2 ≤ ν →
        N < K →
          2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
            AperyS.GV p (AperyS.FS s ν K N (K - N)) ↑(AperyS.AssemblyTarget.LpSharp s ν K N M p L)
```
### `AperyS.AssemblyTarget.normalization_sharp_statement`
```lean
AperyS.AssemblyTarget.normalization_sharp_statement : AperyS.AssemblyTarget.SharpNormalizationStatement
```
### `Mathathon.P108.thetaPkg_sstep`
```lean
Mathathon.P108.thetaPkg_sstep : ∀ (s ν α M U : ℝ),
  3 ≤ M →
    Mathathon.P108.thetaPkg (s + 2) ν α M U - Mathathon.P108.thetaPkg s ν α M U =
      2 * (1 - α) / 3 + (Mathathon.P108.Iout (s + 2) ν α - Mathathon.P108.Iout s ν α)
```
### `Mathathon.P108.theta_sstep_7_6`
```lean
Mathathon.P108.theta_sstep_7_6 : ∀ (M U : ℝ),
  3 ≤ M → Mathathon.P108.thetaPkg 7 6 (3 / 40) M U - Mathathon.P108.thetaPkg 5 6 (3 / 40) M U = 751 / 768
```
### `Mathathon.P108.sstep_ge`
```lean
Mathathon.P108.sstep_ge : ∀ (s ν : ℝ),
  7 ≤ s →
    ν ≤ 10 →
      167 / 300 ≤ 2 * (1 - 3 / 40) / 3 + (Mathathon.P108.Iout (s + 2) ν (3 / 40) - Mathathon.P108.Iout s ν (3 / 40))
```
### `Mathathon.P108.thetaPkg_odd_ge`
```lean
Mathathon.P108.thetaPkg_odd_ge : ∀ (n : ℕ) (ν M U : ℝ),
  ν ≤ 10 →
    3 ≤ M →
      Mathathon.P108.thetaPkg 7 ν (3 / 40) M U + ↑n * (167 / 300) ≤ Mathathon.P108.thetaPkg (7 + 2 * ↑n) ν (3 / 40) M U
```
### `Mathathon.P108.gain58_formal`
```lean
Mathathon.P108.gain58_formal : ∫ (y : ℝ) in 1 / 3..17 / 40,
    Mathathon.P108.Tout 5 8 (3 / 40) y - y * Mathathon.P108.innerR 5 8 (3 / 40) (1 / y) =
  1159 / 28800
```
### `U18.arithmetic_allM_strict`
```lean
U18.arithmetic_allM_strict : ∀ (M : ℝ), 40 ≤ M → 229 / 100 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M 0
```
### `U18.theta_allM_gt`
```lean
U18.theta_allM_gt : ∀ (M U : ℝ), 40 ≤ M → -139 / 100 < U → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M U
```
### `BFullBridge.explicit_normalizer_limit_statement`
```lean
BFullBridge.explicit_normalizer_limit_statement : Mathathon.P108.InnerExplicitTarget.ExplicitNormalizerLimitStatement
```
### `BFullBridge.zeta_seven_explicit_margin_positive_statement`
```lean
BFullBridge.zeta_seven_explicit_margin_positive_statement : Mathathon.P108.InnerExplicitTarget.ZetaSevenExplicitMarginPositiveStatement
```
### `U44.optimized_energy_floor_real`
```lean
U44.optimized_energy_floor_real : ∀ (rho : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure rho]
  [MeasureTheory.NullSingletonClass rho] {R : ℝ},
  (∀ᵐ (x : ℝ) ∂rho, |x| ≤ R) →
    rho Set.univ = ENNReal.ofReal U11.lam →
      MeasureTheory.Integrable (fun p => Real.log |p.1 - p.2|) (rho.prod rho) →
        -139 / 100 < U11.lam * (U42.fieldSup rho).toReal - U42.selfEnergy rho + U11.C6
```
### `U44.fieldSup_ne_top`
```lean
U44.fieldSup_ne_top : ∀ (rho : MeasureTheory.Measure ℝ) {R : ℝ},
  (∀ᵐ (y : ℝ) ∂rho, |y| ≤ R) → rho Set.univ = ENNReal.ofReal U11.lam → U42.fieldSup rho ≠ ⊤
```
### `U44.package_margin_optimized`
```lean
U44.package_margin_optimized : ∀ (M : ℝ),
  40 ≤ M →
    ∀ (rho : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure rho] [MeasureTheory.NullSingletonClass rho]
      {R : ℝ},
      (∀ᵐ (x : ℝ) ∂rho, |x| ≤ R) →
        rho Set.univ = ENNReal.ofReal U11.lam →
          MeasureTheory.Integrable (fun p => Real.log |p.1 - p.2|) (rho.prod rho) →
            9 / 10 <
              Mathathon.P108.thetaPkg 7 6 (3 / 40) M (U11.lam * (U42.fieldSup rho).toReal - U42.selfEnergy rho + U11.C6)
```
### `U44.optimal_energy_floor_real`
```lean
U44.optimal_energy_floor_real : -139 / 100 < U42.optimalEnergy.toReal
```
### `U43.V6_coercive`
```lean
@U43.V6_coercive : ∀ {t : ℝ}, 0 ≤ t → 5 * √t - 3 ≤ U16.V6 t
```
### `U42.fieldSup_ne_bot`
```lean
U42.fieldSup_ne_bot : ∀ (rho : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure rho]
  [MeasureTheory.NullSingletonClass rho] {R : ℝ},
  (∀ᵐ (x : ℝ) ∂rho, |x| ≤ R) →
    rho Set.univ = ENNReal.ofReal U11.lam →
      MeasureTheory.Integrable (fun p => Real.log |p.1 - p.2|) (rho.prod rho) → U42.fieldSup rho ≠ ⊥
```
### `U42.sigma_comparison_class`
```lean
U42.sigma_comparison_class : U42.ComparisonClass U20.sigma
```
### `BZetaIdentification.riemannZeta_eq_zetaS`
```lean
BZetaIdentification.riemannZeta_eq_zetaS : ∀ (s : ℕ), 2 ≤ s → riemannZeta ↑s = ↑(BAnalyticPoles.zetaS s)
```
### `AperyS.AssemblyTarget.WI_sstep_bounds`
```lean
AperyS.AssemblyTarget.WI_sstep_bounds : ∀ (s ν K N p : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  1 ≤ p / 2 →
    ∑ c, L p c = K - N →
      AperyS.AssemblyTarget.WI s ν K N p L - ↑(K - N) ≤ AperyS.AssemblyTarget.WI (s + 2) ν K N p L ∧
        AperyS.AssemblyTarget.WI (s + 2) ν K N p L ≤ AperyS.AssemblyTarget.WI s ν K N p L
```
### `AperyS.AssemblyTarget.Lp_inner_sstep`
```lean
AperyS.AssemblyTarget.Lp_inner_sstep : ∀ (s ν K N M p : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  K < p * M →
    3 * p ≤ K →
      AperyS.AssemblyTarget.InnerOK s ν K N p L →
        AperyS.AssemblyTarget.InnerOK (s + 2) ν K N p L →
          AperyS.AssemblyTarget.Lp s ν K N M p L - 2 * ↑(K - N) ≤ AperyS.AssemblyTarget.Lp (s + 2) ν K N M p L ∧
            AperyS.AssemblyTarget.Lp (s + 2) ν K N M p L ≤ AperyS.AssemblyTarget.Lp s ν K N M p L
```
### `AperyS.AssemblyTarget.switch_Lp5`
```lean
AperyS.AssemblyTarget.switch_Lp5 : AperyS.AssemblyTarget.Lp 5 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation =
  -444
```
### `AperyS.AssemblyTarget.switch_Lp7`
```lean
AperyS.AssemblyTarget.switch_Lp7 : AperyS.AssemblyTarget.Lp 7 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation =
  -119
```
### `AperyS.AssemblyTarget.selected_Lp_can_increase`
```lean
AperyS.AssemblyTarget.selected_Lp_can_increase : AperyS.AssemblyTarget.Lp 5 6 40 3 400 13
    AperyS.AssemblyTarget.switchAllocation <
  AperyS.AssemblyTarget.Lp 7 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation
```
### `Mathathon.P108.classLoss_witness`
```lean
Mathathon.P108.classLoss_witness : padicValRat 13 Mathathon.P108.entry.1 = -10 ∧
  padicValRat 13 Mathathon.P108.entry.2 = 0 ∧
    Mathathon.P108.beta = -4 ∧
      Mathathon.P108.beta - min (padicValRat 13 Mathathon.P108.entry.1) (padicValRat 13 Mathathon.P108.entry.2) = 6
```
### `Mathathon.P108.lai_offset_gap_7_2`
```lean
Mathathon.P108.lai_offset_gap_7_2 : (∫ (x : ℝ) in 3..200, Mathathon.P108.innerR 7 2 (3 / 40) x / x ^ 3) -
    ∫ (x : ℝ) in 3..200, Mathathon.P108.innerR 1 2 (3 / 40) x / x ^ 3 =
  21867 / 12000
```
### `Mathathon.P108.Skip.lai_skip_witness`
```lean
Mathathon.P108.Skip.lai_skip_witness : Mathathon.P108.Skip.laiSkips 11 40 17 ∧
  Mathathon.P108.Skip.HasContentVal 17 (Mathathon.P108.Skip.F 11 2 1) (-247) ∧
    ¬∀ (i : ℕ), 0 ≤ padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff i)
```
### `Mathathon.P108.Skip.Delta_eq`
```lean
Mathathon.P108.Skip.Delta_eq : Mathathon.P108.Skip.Delta 11 2 1 = Mathathon.P108.Skip.DeltaLit
```
### `CCompactWithClosing.irrational_five`
```lean
CCompactWithClosing.irrational_five : CCompact.FiniteRealBoundStatement → ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```
### `CCompactCurrent.irrational_five`
```lean
CCompactCurrent.irrational_five : CCompact.FiniteRealBoundStatement →
  CCompact.ClosingStatement → ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```
### `CCertificateSplit.irrational_five`
```lean
CCertificateSplit.irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```
### `CCertificateSplit.finite_real_bound`
```lean
CCertificateSplit.finite_real_bound : CCompact.FiniteRealBoundStatement
```
### `CSplitField.local_field_certificate`
```lean
CSplitField.local_field_certificate : U48.LocalFieldStatement (-32999 / 5000)
```
### `BSymbolicCriterion.criterion_standard`
```lean
BSymbolicCriterion.criterion_standard : ∀ (s ν M : ℕ),
  Mathathon.P108.RangeBridgeTarget.ParameterScope s ν →
    40 ≤ M →
      ∀ (u : ℝ),
        BSymbolicCriterion.AnalyticLeadingStatement s ν u →
          Mathathon.P108.thetaPkg (↑s) (↑ν) (3 / 40) (↑M) u < 0 → ∃ x, Irrational x ∧ riemannZeta ↑s = ↑x
```
### `LMergeCompactAnalytic.finite_real_bound`
```lean
LMergeCompactAnalytic.finite_real_bound : ∀ (s n : ℕ),
  2 ≤ s →
    1 ≤ n →
      0 < (Polynomial.aeval (BAnalyticPoles.zetaS s)) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n)) ∧
        Real.log ((Polynomial.aeval (BAnalyticPoles.zetaS s)) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n))) ≤
          -2650371 / 2000000 * ↑(40 * n) ^ 2 + (↑s + 23) * ↑(37 * n) * Real.log ↑(40 * n) +
            (12 * Real.log 2 + 23 + Real.log (BAnalyticIntegral.C s (2 * Real.pi))) * ↑(37 * n)
```
### `CCertificateSplit.closing`
```lean
CCertificateSplit.closing : CCompact.ClosingStatement
```
### `SplitClosing.closing_neg`
```lean
SplitClosing.closing_neg : Mathathon.P108.thetaPkg 5 6 (3 / 40) 1000000 (-2650371 / 2000000) < 0
```

## Source scan (warnings)
No forbidden tokens.
