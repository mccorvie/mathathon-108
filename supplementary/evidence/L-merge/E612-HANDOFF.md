# E612 receiving handoff

**LEAN-CHECKED:** selected39/39 pass the official final gate in this receiver; no label upgrade.

The E607 snapshot is checkpoints/e607-2112/. Other report declaration names are retained; changed CCompact hypothesis constants are explicit below.

**COMPUTED source footprint:** merged360 files/70158 lines/3875621 bytes; standalone C258 files/34746 lines. These are distinct metrics.

Cache+build158.485s. The integrator owns export, the judged-clone gate, report edits and statement comparisons.

```lean
CCertificateSplit.irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```

```lean
CCertificateSplit.finite_real_bound : CCompact.FiniteRealBoundStatement
```

```lean
CSplitField.local_field_certificate : U48.LocalFieldStatement (-32999 / 5000)
```

```lean
LMergeCompactAnalytic.finite_real_bound : ∀ (s n : ℕ),
  2 ≤ s →
    1 ≤ n →
      0 < (Polynomial.aeval (BAnalyticPoles.zetaS s)) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n)) ∧
        Real.log ((Polynomial.aeval (BAnalyticPoles.zetaS s)) (AperyS.FS s 6 (40 * n) (3 * n) (37 * n))) ≤
          -2650371 / 2000000 * ↑(40 * n) ^ 2 + (↑s + 23) * ↑(37 * n) * Real.log ↑(40 * n) +
            (12 * Real.log 2 + 23 + Real.log (BAnalyticIntegral.C s (2 * Real.pi))) * ↑(37 * n)
```

```lean
CCertificateSplit.closing : CCompact.ClosingStatement
```

```lean
SplitClosing.closing_neg : Mathathon.P108.thetaPkg 5 6 (3 / 40) 1000000 (-2650371 / 2000000) < 0
```

Verbatim Lean definition prints:

```lean
def U48.LocalFieldStatement : ℝ → Prop :=
fun T => ∀ (t : ℝ), 0 < t → t ≤ 2 → 2 * Apery.Uρ t - Apery.Vfield t ≤ T
def CCompact.FiniteRealBoundStatement : Prop :=
∀ (n : ℕ),
  1 ≤ n →
    0 < (Polynomial.aeval CCompact.ξ) (CCompact.F n) ∧
      Real.log ((Polynomial.aeval CCompact.ξ) (CCompact.F n)) ≤
        CCompact.u * CCompact.K n ^ 2 + 28 * ↑(37 * n) * Real.log (CCompact.K n) +
          (12 * Real.log 2 + 23 + Real.log (BAnalyticIntegral.C 5 (2 * Real.pi))) * ↑(37 * n)
def CCompact.ClosingStatement : Prop :=
Mathathon.P108.thetaPkg 5 6 (3 / 40) 1000000 CCompact.u < 0
def CCompact.u : ℝ :=
-2650371 / 2000000
def CCompact.m : ℕ → ℚ :=
fun n =>
  AperyS.AssemblyTarget.normalizerSharp 5 6 (40 * n) (3 * n) 1000000
    (Mathathon.P108.RangeBridgeTarget.explicitAllocation 5 6 (40 * n) (3 * n) 1000000)
def CCompact.A : ℝ :=
Mathathon.P108.InnerExplicitTarget.arithmeticPackage 5 6 1000000
```

No new threshold is stated under the old U49.local_field_certificate name. No upstream numerical energy table is imported.
