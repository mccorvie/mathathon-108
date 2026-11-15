# Lean project: Fauzan's ζ(5) method for symbolic odd s

Lean v4.35.0, Mathlib v4.35.0, pinned in `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`.

Lane C's project of record, after E616 memory checks and E615/C8 simplifications.
**COMPUTED:** 435 local Lean source files, 45,175 physical source lines, including
helpers, numerical data, comments and the isolated Comparator challenge; external
Mathlib/PNT sources are excluded. The memory-fixed baseline has 444files/47,275lines.
C8 saves 2,100lines; the separate memory engineering costs 1,570lines relative to
the earlier357file/45,705line snapshot. These are whole-project source counts.

**LEAN-CHECKED:** the final gate passes55/55 declarations on4.35.0, with standard
axioms only. Both MergeEntry and Mathathon.Zeta5Comparator.Solution build. All40
previous report statements print identically. Report labels and different-family
statement comparisons remain the integrator's responsibility.

```bash
lake exe cache get
lake build            # default target: MergeEntry
```

**LEAN-CHECKED:** every declaration listed below builds with no `sorry` in its dependencies and only the axioms `propext`, `Classical.choice`, `Quot.sound`
(`#print axioms <name>`). The report prints each statement and says how it differs from the claim it supports.
Nothing here proves anything about ζ(7) itself, and the ζ(5) theorem is a re-derivation of Fauzan's theorem that
reuses Moritz Firsching's formalisation (see `NOTICE`); it is not a new or independent proof.

The default target also imports [`Mathathon/Claims.lean`](Mathathon/Claims.lean), a statement sheet
with the same three layers and a `#check` for each headline declaration. To print it:

```bash
lake env lean Mathathon/Claims.lean
```

## What is in here, in three layers

**Layer 1. Statements for symbolic parameters (not about ζ(5) in particular).**

| Report claim | Declaration | File |
|---|---|---|
| 1. The arithmetic for odd s, even ν: class loss s − 1 | `AperyS.tauXs_direct` | `Zeta5S/DirectPoly.lean` |
| 1. Valuation bound at every prime (sharp outer loss) | `AperyS.AssemblyTarget.local_valuation_sharp` | `Zeta5S/SharpAssembly.lean` |
| 1. Integer normalisation | `AperyS.AssemblyTarget.normalization_sharp_statement`, `AperyS.AssemblyTarget.normalization_statement` | `Zeta5S/SharpAssembly.lean`, `Zeta5S/NormalizationProof.lean` |
| 2. The exact s-step of the margin formula | `Mathathon.P108.thetaPkg_sstep`, `Mathathon.P108.theta_sstep_7_6` | `Mathathon/P108/SStep.lean` |
| 2. The step is at least 167/300 for s ≥ 7 | `Mathathon.P108.sstep_ge`, `Mathathon.P108.thetaPkg_odd_ge` | `Mathathon/P108/SStepAll.lean` |
| 5. The normaliser's growth is the margin formula (odd s ≥ 5, even ν ≤ 10) | `BFullBridge.explicit_normalizer_limit_statement` | `Final.lean` |
| 5. Positivity and a real bound for every natural s ≥ 2 (ν = 6) | `LMergeCompactAnalytic.finite_real_bound` | `CompactAnalyticBound.lean` |
| 5. ζ(s) as Mathlib's `riemannZeta` | `BZetaIdentification.riemannZeta_eq_zetaS` | `ZetaIdentification.lean` |
| 5. The criterion: negative margin and an analytic bound give irrationality | `BSymbolicCriterion.criterion_standard` | `ZetaBridge.lean` |
| (finite step is not an asymptotic step) | `AperyS.AssemblyTarget.WI_sstep_bounds`, `AperyS.AssemblyTarget.Lp_inner_sstep`, `AperyS.AssemblyTarget.selected_Lp_can_increase` | `Zeta5S/FiniteStep.lean` |

**Layer 2. The point (s, ν) = (7, 6): the package's margin is positive.**

| Report claim | Declaration | File |
|---|---|---|
| 3(a). The formula exceeds 9/10 for every real M ≥ 40 and U > −139/100 | `U18.theta_allM_gt`, `U18.arithmetic_allM_strict` | `AllM.lean`, `ShortArithmeticFloor.lean` |
| 3(b). The same for the package's own normaliser, for large n | `BFullBridge.zeta_seven_explicit_margin_positive_statement` | `BFullPositive.lean` |
| 3(c). The energy bound over an explicit class of measures | `U44.optimized_energy_floor_real` and companions | `BoundedFieldSupremum.lean`, `PositiveEnvelope.lean` |

**Layer 3. The instance s = 5, and audit lemmas.**

| Report claim | Declaration | File |
|---|---|---|
| 8. ζ(5) is irrational, along the chain of layer 1 | `CCertificateSplit.irrational_five` | `SplitEntry.lean` |
| 8. Its two numerical certificates | `CSplitField.local_field_certificate`, `SplitClosing.closing_neg` | `SplitField.lean`, `Closing.lean` |
| 7. The rational gain at ν = 8 (arithmetic only) | `Mathathon.P108.gain58_formal` | `Mathathon/P108/OuterValues58.lean` |
| Audits of earlier certificates | `Mathathon.P108.classLoss_witness`, `Mathathon.P108.lai_offset_gap_7_2`, `Mathathon.P108.Skip.lai_skip_witness` | `LeanWitness/ClassLoss.lean`, `Mathathon/P108/OffsetGap.lean`, `Mathathon/P108/LaiSkip.lean` |

## Where things come from

`Apery/` reuses Moritz Firsching's mo271/Zeta5 (Apache-2.0; Comparator metadata
by Paul-Lez), including the unchanged criterion, raw-energy and tail files.
`Zeta5S/` makes the arithmetic parameters s and ν symbolic. Lane B's existing
GeneralDegree proof bounds the actual FS degree by h without an exact leading
coefficient calculation; C8 applies it to the fixed instance. The existing generic
density/envelope/integrability proofs specialize to the exact s=5 weight through
Apery.WeightCore, replacing the duplicate specialized analytic route. Polynomial
identification names and all numerical data/model constants are preserved.

**Andrew Casper** is credited by name for the degree-upper-bound and primitive-value
suggestions in his shared archive. None of his files is copied. The primitive
interpretation clarifies the existing criterion; no extra content theorem is assumed.
The implementation reuses the attributed lane-B proofs and existing Firsching-based
adapters. The prime number theorem input is AlexKontorovich/PrimeNumberTheoremAnd,
pinned in the manifest. `NOTICE` and the licence files retain the prior/event credits.

## Independent statement comparator

```bash
./verify-comparator.sh
```

See [COMPARATOR.md](COMPARATOR.md) and [comparator.json](comparator.json). The trusted
Mathlib-only challenge is [Mathathon/Zeta5Comparator/Challenge.lean](Mathathon/Zeta5Comparator/Challenge.lean);
the separate solution delegates to `CCertificateSplit.irrational_five`. The intentional
challenge hole is not imported by the solution or the default target. Linux uses the
built-in sandbox; macOS local runs require the explicit option documented there.

To print the axioms of the zeta(5) endpoint directly:

```bash
cat > .lake/CheckAxioms.lean <<'LEAN'
import SplitEntry
#print axioms CCertificateSplit.irrational_five
LEAN
lake env lean .lake/CheckAxioms.lean
```

The historical stronger energy-table bounds (report D15/D16) and heavy zeta(5)
variant (D21) are not submitted here. Claim 4's interval table and claim 6's
obstruction conjecture are evidence in the report, not additional Lean theorems.

## Computations that are not Lean

[`computations/`](computations/README.md) holds the interval-arithmetic cover behind the report's statement that the margin of
the estimates at zeta(7) stays positive (at least +0.486) over the whole region of proportions of the construction, with the
code, its result files and a second run. It is a computation relative to a written derivation, not a Lean proof, and `lake build`
does not touch it.
