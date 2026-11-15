# E218 / U23: lane U human statement comparison sheet

Author: Codex driver for [team member], event work Sat Nov 14 2026.

**CONJECTURE — Review status.** These are agent-generated comparison materials.
No human verdict is recorded. For every passed supporting gate below, the
report wording remains: **“Lean gate passes; statement not yet compared.”**
The overall energy/irrationality claims remain CONJECTURE as [team member] requested.

**CITED — Prior numerical and formal sign evidence.** The pre-event Claude Opus5 audit prepared for Dan Romik reports a nu6 zeta(7) balance of about+0.93 (PDFp.3). [team member]'s pre-event [team handle]/zeta7-irrational@be55b3a4 already proves a margin failure for Anand's different nu8 package: `ZetaSeven.primeSumA_add_u_pos`, FinalMargins.lean95, gives `primeSumA+44/25>0` for natural cutoffs M>0; `final_margins_fail`, line101, refutes its final inequalities. Exact references and source comparisons are in [the librarian's R2 audit](../R-margin-and-step/README.md). These are prior work, not event results, and this sheet makes no first-formal-sign claim.

**CONJECTURE — Scope of the present certificate.** E206 supplies the stated explicit fifteen-component scalar witness; E213 gives the quantitative nu6 package bound for every real M>=40. Their exact scope differs from the prior nu8/natural-cutoff audit. The sign itself is known; the librarian leaves exact-statement priority unclear. No human statement comparison is recorded here.

Use this sheet to compare statements and definitions, not to read tactic
proofs. Each Lean theorem block is copied exactly from its gate report; each
definition block is literal `#print` output from the compiled v4.33.1 probe.
All project-model definitions needed by the selected statements are included
in dependency order. Standard Mathlib primitives (`Real.log`, square root,
floor, measure/integral, finite sum, `Integrable`, etc.) retain their library
meanings and are not recursively reprinted. The model-print source files and
raw outputs are in `printed/`; `sheet-source-hashes.json` records the inputs.

Suggested route: E206, E207, E209, E208, then the arithmetic cell. Reuse the
earlier definition blocks when later statements refer to them. Answer each
section's yes/no questions and record any difference; answering yes does not
automatically upgrade any broader claim or a different theorem. The integrator
records the actual human comparison and any resulting label change.

## E206: explicit scalar energy cell

**CONJECTURE — Claim in two sentences.** The exact fifteen-width real
expression `U11.lb6Square15` exceeds `-139/100`. If arbitrary real numbers
`A,U` satisfy `A>=229/100` and `lb6Square15<=U`, their sum exceeds `9/10`.

Project definitions, printed in dependency order (the optional exact
`rootWidth` helper is included alongside `width`):

```lean
def U11.alpha : ℝ :=
3 / 40
def U11.lam : ℝ :=
37 / 40
def U11.mass : Fin 15 → ℝ :=
![1033 / 10000, 1160 / 10000, 1032 / 10000, 917 / 10000, 813 / 10000, 719 / 10000, 633 / 10000, 555 / 10000,
  484 / 10000, 420 / 10000, 361 / 10000, 308 / 10000, 260 / 10000, 216 / 10000, 339 / 10000]
def U11.width : Fin 15 → ℝ :=
fun j => 25 / 36 * (49 / 64) ^ (↑j : ℕ)
def U11.rootWidth : Fin 15 → ℝ :=
fun j => 5 / 6 * (7 / 8) ^ (↑j : ℕ)
def U11.T : ℝ → ℝ → ℝ :=
fun a b => 2 * a * Real.log ((a + √(a ^ 2 + b)) / 2) - 2 * √(a ^ 2 + b) + 2 * √b
def U11.W : ℝ → ℝ :=
fun b => 4 * √b + U11.T 1 b - 6 * U11.T U11.alpha b
def U11.C6 : ℝ :=
-2 * U11.lam + 12 * U11.alpha * U11.lam * (1 - Real.log U11.alpha) + 3 * U11.lam ^ 2 -
  2 * U11.lam ^ 2 * Real.log (2 * U11.lam)
def U11.lb6Square15 : ℝ :=
U11.lam ^ 2 * Real.log (25 / 144) + 233486993 / 100000000 * Real.log (49 / 64) - ∑ j, U11.mass j * U11.W (U11.width j) +
  U11.C6
```

```lean
U11.lb6Square15_gt : -139 / 100 < U11.lb6Square15
```

```lean
U11.margin_gt : ∀ (A U : ℝ), 229 / 100 ≤ A → U11.lb6Square15 ≤ U → 9 / 10 < A + U
```


Known differences from the informal E201 application: this statement defines
a real expression, not an energy infimum or a comparison measure. Its
arithmetic premise is non-strict and its energy premise is explicit. The
fifteen-component witness is event work rather than the upstream comparison
table. The scalar bound uses Mathlib estimates; it does not adapt an upstream
valuation theorem.

Yes/no comparison:

- [ ] Are alpha, lambda, all15 masses and widths, T, W, C6 and both logarithm
  coefficients exactly those intended in E201?
- [ ] Is the conclusion strict `-139/100 < lb6Square15`, without a numeric-bound
  hypothesis or an unidentified symbol standing in for that expression?
- [ ] Does the margin interface say only what its explicit real premises give,
  with the measure/infimum interpretation kept separate?

## E207: explicit closed-form modulus

**CONJECTURE — Claim in two sentences.** The explicit arcosh function below
changes by at most `2*sqrt(e/(b-a))` under a nonnegative shift of its real
argument. The assertion covers every real x and every a<b, including e=0.

```lean
def Mathathon.P108.UTranslation.intervalDistance : ℝ → ℝ → ℝ → ℝ :=
fun a b x => max (a - x) (max 0 (x - b))
def Mathathon.P108.UTranslation.closedPotential : ℝ → ℝ → ℝ → ℝ :=
fun a b x => Real.log ((b - a) / 4) + 2 * Real.arsinh √(Mathathon.P108.UTranslation.intervalDistance a b x / (b - a))
def Mathathon.P108.UTranslation.arcoshPotential : ℝ → ℝ → ℝ → ℝ :=
fun a b x => Real.log ((b - a) / 4) + Real.arcosh (1 + 2 * Mathathon.P108.UTranslation.intervalDistance a b x / (b - a))
```

```lean
@Mathathon.P108.UTranslation.arcoshPotential_translation : ∀ {a b e : ℝ},
  a < b →
    0 ≤ e →
      ∀ (x : ℝ),
        |Mathathon.P108.UTranslation.arcoshPotential a b (x + e) - Mathathon.P108.UTranslation.arcoshPotential a b x| ≤
          2 * √(e / (b - a))
```


Known differences from E200: E207 alone is a real-function theorem; there is
no arcsine measure, logarithmic integral, translated measure, energy invariance
or equal-infimum assertion in this statement. The equivalent arsinh expression
is the definition used by the proof. Later E209 supplies a separate angular
integral identification; E212 defines a pushforward Borel measure separately.
No prior-project proof was copied into the elementary E207 modulus proof.

Yes/no comparison:

- [ ] Are intervalDistance and both explicit expressions literally the intended
  functions on the full real line?
- [ ] Are a<b and e>=0 the only assumptions, with the constant and interval
  length exactly as claimed?
- [ ] Is the application to a measure/integral kept distinct from this theorem?

## E208: finite-curve weak duality

**CONJECTURE — Claim in two sentences.** For the normalized logarithmic kernel
of a finite family of continuous uniformly bounded curves, nonnegative a,
equal total masses and the averaged-field premises imply weak duality.
Pair integrability and almost-everywhere distinctness are explicit hypotheses;
zero-mass energy nonpositivity and symmetry are proved from them.

```lean
@[reducible] def Apery.μcirc : MeasureTheory.Measure ℝ :=
MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
def Apery.pairInt.{u_1} : {ι : Type u_1} → (ι → ℝ → ℂ) → (ℂ → ℂ → ℝ) → ι → ι → ℝ :=
fun {ι} γ f k l => ∫ (θ : ℝ) (φ : ℝ) in 0..2 * Real.pi, f (γ k θ) (γ l φ)
def Apery.energy.{u_1} : {ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ → ℂ) → (ℂ → ℂ → ℝ) → ℝ :=
fun {ι} [Fintype ι] s γ f => ∑ k, ∑ l, s k * s l * Apery.pairInt γ f k l
def Mathathon.P108.FiniteDuality.bilinear.{u_1} : {ι : Type u_1} → [Fintype ι] → (ι → ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ :=
fun {ι} [Fintype ι] K a b => ∑ i, ∑ j, a i * b j * K i j
def Mathathon.P108.FiniteDuality.quadratic.{u_1} : {ι : Type u_1} → [Fintype ι] → (ι → ι → ℝ) → (ι → ℝ) → ℝ :=
fun {ι} [Fintype ι] K a => Mathathon.P108.FiniteDuality.bilinear K a a
def Mathathon.P108.FiniteDuality.curveKernel.{u_1} : {ι : Type u_1} → (ι → ℝ → ℂ) → ι → ι → ℝ :=
fun {ι} gamma i j => Apery.pairInt gamma (fun z w => Real.log ‖z - w‖) i j / (2 * Real.pi) ^ 2
```

```lean
@Mathathon.P108.FiniteDuality.finite_curve_weak_duality : ∀ {ι : Type u_1} [inst : Fintype ι] (gamma : ι → ℝ → ℂ),
  (∀ (i : ι), Continuous (gamma i)) →
    ∀ {R : ℝ},
      (∀ (i : ι) (theta : ℝ), ‖gamma i theta‖ ≤ R) →
        (∀ (i j : ι),
            MeasureTheory.Integrable (fun p => Real.log ‖gamma i p.1 - gamma j p.2‖) (Apery.μcirc.prod Apery.μcirc)) →
          (∀ (i j : ι), ∀ᵐ (p : ℝ × ℝ) ∂Apery.μcirc.prod Apery.μcirc, gamma i p.1 ≠ gamma j p.2) →
            ∀ (a b V : ι → ℝ) (lam M : ℝ),
              (∀ (i : ι), 0 ≤ a i) →
                ∑ i, a i = lam →
                  ∑ i, b i = lam →
                    (∀ (i : ι), 2 * ∑ j, b j * Mathathon.P108.FiniteDuality.curveKernel gamma i j - V i ≤ M) →
                      Mathathon.P108.FiniteDuality.quadratic (Mathathon.P108.FiniteDuality.curveKernel gamma) a -
                          ∑ i, a i * V i ≤
                        lam * M -
                          Mathathon.P108.FiniteDuality.quadratic (Mathathon.P108.FiniteDuality.curveKernel gamma) b
```


Known differences from E201's universal comparison: this is a finite-curve
theorem with an input vector V and row-averaged potential bounds, not a theorem
for all Borel measures or a proof that a pointwise field bound has been
averaged correctly. Diagonal index pairs are included in the a.e.-distinctness
premise. The generic zero-mass proof is prior work by Firsching/Paul-Lez from
mo271/Zeta5@be1c0d82; the normalized finite-algebra interface is event glue.
E210 later discharges these curve hypotheses for finite arcsine families.

Yes/no comparison:

- [ ] Does the `(2*pi)^2` normalization match the intended probability energy?
- [ ] Are every analytic premise, both mass equalities, `a_i>=0` (with signed b
  allowed) and the averaged row bound present literally, including diagonal pairs?
- [ ] Does the statement refrain from identifying arbitrary V/U symbols with
  the original external field or an unrestricted measure class?

## E209: angular integral identification

**CONJECTURE — Claim in two sentences.** The normalized real angular
logarithmic integral equals E207's explicit closed potential for every a<b
and real evaluation point. It consequently satisfies the same shift modulus.

```lean
def Apery.arcCurve : ℝ → ℝ → ℝ → ℂ :=
fun m r θ => ↑(m + r * Real.cos θ)
def Apery.Uω : ℝ → ℝ → ℝ → ℝ :=
fun a b t => if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4) else Real.log ((|t - (a + b) / 2| + √((t - a) * (t - b))) / 2)
def U14.angularMean : ℝ → ℝ → ℝ → ℝ :=
fun a b t => (2 * Real.pi)⁻¹ * ∫ (θ : ℝ) in 0..2 * Real.pi, Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)|
```

```lean
@U14.angular_mean_closed : ∀ {a b : ℝ},
  a < b →
    ∀ (t : ℝ),
      (2 * Real.pi)⁻¹ * ∫ (θ : ℝ) in 0..2 * Real.pi, Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)| =
        Mathathon.P108.UTranslation.closedPotential a b t
```

```lean
@U14.angular_mean_translation : ∀ {a b e : ℝ},
  a < b → 0 ≤ e → ∀ (x : ℝ), |U14.angularMean a b (x + e) - U14.angularMean a b x| ≤ 2 * √(e / (b - a))
```


Known differences: this is an angular integral, not a density-defined Borel
integral. The angular formula is prior Firsching/Paul-Lez work
(`Apery/ArcsinePotential.lean:114-125` at be1c0d82), minimally extracted with
license and exact declaration source maps. The comparison with E207's chosen
closed form, real-axis rewrite and composition are event adaptation.

Yes/no comparison:

- [ ] Is the angular parametrization `(a+b)/2+(b-a)cos(theta)/2` and the
  normalization exactly `1/(2*pi)` over `0..2*pi`?
- [ ] Does the identity include t=a and t=b, rather than omit the singular
  endpoint evaluations through an extra hypothesis?
- [ ] Are prior proof attribution and the angular-versus-density distinction
  explicit in the associated claim?

## U18 / E213: arithmetic package cell

**CONJECTURE — Claim in two sentences.** The literal defined arithmetic
package `thetaPkg 7 6 (3/40) M 0` exceeds `229/100` for every real M>=40.
For those M, every real U>-139/100 and the explicit E206 witness give a
package margin above `9/10`; no energy-infimum identification is implicit.

All root-package model definitions, printed verbatim from the byte-copied
root definitions in dependency order:

```lean
def Mathathon.P108.ell : ℝ → ℝ → ℝ :=
fun x z => ↑⌊x - z⌋ + ↑⌊x + z⌋ + 1
def Mathathon.P108.Hc : ℝ → ℝ → ℝ :=
fun ν α => 1 - α + ν / 2 * α
def Mathathon.P108.Tc : ℝ → ℝ → ℝ → ℝ :=
fun ν α x => ↑⌊2 * Mathathon.P108.Hc ν α * x⌋
def Mathathon.P108.sigmaC : ℝ → ℝ → ℝ → ℝ :=
fun ν α x => Mathathon.P108.Hc ν α * x - Mathathon.P108.Tc ν α x / 2
def Mathathon.P108.nplus : ℝ → ℝ :=
fun x => (2 * x - ↑⌊2 * x⌋) / 2
def Mathathon.P108.gammaIntegrand : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α x z =>
  (Mathathon.P108.Tc ν α x - ν / 2 * Mathathon.P108.ell (α * x) z) *
    (Mathathon.P108.Tc ν α x + ν / 2 * Mathathon.P108.ell (α * x) z - Mathathon.P108.ell x z - s)
def Mathathon.P108.innerGamma : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α x =>
  (∫ (z : ℝ) in 0..1 / 2, Mathathon.P108.gammaIntegrand s ν α x z) +
      Mathathon.P108.sigmaC ν α x * (2 * Mathathon.P108.Tc ν α x - ↑⌊2 * x⌋ - s) +
    max (Mathathon.P108.sigmaC ν α x - Mathathon.P108.nplus x) 0
def Mathathon.P108.Jfun : ℝ → ℝ :=
fun u => ↑⌊2 * u⌋ * u - ↑⌊2 * u⌋ * (↑⌊2 * u⌋ + 1) / 4
def Mathathon.P108.innerN : ℝ → ℝ → ℝ → ℝ :=
fun ν α x => 2 * (1 - α) * x * ↑⌊x⌋ - 2 * ν * (1 - α) * x * ↑⌊α * x⌋ - 2 * Mathathon.P108.Jfun ((1 - α) * x)
def Mathathon.P108.innerR : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α x => -Mathathon.P108.innerGamma s ν α x - Mathathon.P108.innerN ν α x
def Mathathon.P108.cRem : ℝ → ℝ → ℕ → ℝ :=
fun s ν l => ∑ i ∈ Finset.range (l - 2), max 0 (↑l + s - 1 - ν - 2 * ↑i)
def Mathathon.P108.zRem : ℝ → ℝ → ℕ → ℝ :=
fun s ν l => 1 + ∑ i ∈ Finset.range (l - 2), if ↑l + s - 1 - ν - 2 * ↑i ≤ 0 then 1 else 0
def Mathathon.P108.gOuter : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α y =>
  if 1 / 3 < y ∧ y ≤ 1 then
    have k := ⌊1 / y⌋₊;
    have v := 1 - ↑k * y;
    have u := max 0 (α + v - y);
    have mv := min α v;
    have d0 := α - mv;
    have d1 := mv - u;
    have d2 := u;
    have cost :=
      (s + 2) * (1 - y - (d0 * (2 * ↑k - 2) + d1 * (2 * ↑k + 1 - 2) + d2 * (2 * ↑k + 2 - 2))) +
        (d0 * Mathathon.P108.cRem s ν (2 * k) + d1 * Mathathon.P108.cRem s ν (2 * k + 1) +
          d2 * Mathathon.P108.cRem s ν (2 * k + 2));
    have zz :=
      y - 2 * α +
        (d0 * Mathathon.P108.zRem s ν (2 * k) + d1 * Mathathon.P108.zRem s ν (2 * k + 1) +
          d2 * Mathathon.P108.zRem s ν (2 * k + 2));
    have r := min (1 - α) (max 0 (1 + (ν - 2) * α - (s - 1) / 2 * y));
    cost + min r zz
  else 0
def Mathathon.P108.legendreTerm : ℝ → ℝ → ℝ :=
fun α y => -2 * (1 - α) * ↑⌊1 / y⌋₊ + ∑ j ∈ Finset.range 6, max (2 * (1 - α) - (↑j + 1) * y) 0
def Mathathon.P108.Tout : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α y => Mathathon.P108.gOuter s ν α y + Mathathon.P108.legendreTerm α y
def Mathathon.P108.Iout : ℝ → ℝ → ℝ → ℝ :=
fun s ν α => ∫ (y : ℝ) in 1 / 3..2 * (1 - α), Mathathon.P108.Tout s ν α y
def Mathathon.P108.thetaPkg : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
fun s ν α M U =>
  U + Mathathon.P108.Iout s ν α + (s + 1) * (1 - α) / M + ∫ (x : ℝ) in 3..M, Mathathon.P108.innerR s ν α x / x ^ 3
```

```lean
U18.arithmetic200_strong : 2323 / 1000 <
  Mathathon.P108.Iout 7 6 (3 / 40) + 8 * (1 - 3 / 40) / 200 +
    ∫ (x : ℝ) in 3..200, Mathathon.P108.innerR 7 6 (3 / 40) x / x ^ 3
```

```lean
U18.theta200_gt : ∀ (U : ℝ), -139 / 100 < U → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) 200 U
```

```lean
U18.theta200_lb6Square15 : 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) 200 U11.lb6Square15
```

```lean
U18.theta200_of_witness_le : ∀ (U : ℝ), U11.lb6Square15 ≤ U → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) 200 U
```

```lean
U18.theta200_le_of_40_le_le200 : ∀ (M U : ℝ),
  40 ≤ M → M ≤ 200 → Mathathon.P108.thetaPkg 7 6 (3 / 40) 200 U ≤ Mathathon.P108.thetaPkg 7 6 (3 / 40) M U
```

```lean
U18.arithmetic_allM_strict : ∀ (M : ℝ), 40 ≤ M → 229 / 100 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M 0
```

```lean
U18.theta_allM_gt : ∀ (M U : ℝ), 40 ≤ M → -139 / 100 < U → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M U
```

```lean
U18.theta_allM_lb6Square15 : ∀ (M : ℝ), 40 ≤ M → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M U11.lb6Square15
```

```lean
U18.theta_allM_of_witness_le : ∀ (M U : ℝ),
  40 ≤ M → U11.lb6Square15 ≤ U → 9 / 10 < Mathathon.P108.thetaPkg 7 6 (3 / 40) M U
```


The first four types concern M=200; the fifth is the finite-prefix comparison
for every real 40<=M<=200. The final four are the complete all-real-M>=40
statements in the passed combined gate. Their cutoff premise is discharged
internally using `arithmetic200_strong` and the separately checked E217 tail.

Known differences from E13/upstream: this is a statement about the defined
real package, with U an explicit real parameter. It is not a derivation of the
package from Fauzan's valuations, a proof of the finite general-s functional's
analytic interpretation, or an assertion about a measure-theoretic infimum.
The root definitions are copied unchanged; the inner integral is checked from
affine/floor cells, rather than assuming a stored rational A200 value. The
root package's outer function includes its written correction literally; this
does not identify it with lane L's raw-rank-only finite normalization theorem.

Yes/no comparison:

- [ ] Do innerR, Iout and thetaPkg above exactly match the root definitions,
  including all floor conventions, constants, finite sums and corrections?
- [ ] Do the types use exactly s=7,nu=6,alpha=3/40, with every real U above
  the stated floor and every real M>=40 in the final result?
- [ ] Is the witness substitution a real-package statement, with universal
  measure comparison and the arithmetic valuation derivation still separate?
- [ ] Is every claimed M-range covered by its passed printed theorem, with no
  numerical cutoff or desired-bound premise left in the all-M statement?

## Comparison receipt

Human reader/date: __________. Compared sections: __________.
Exact declaration(s) accepted as matching: __________.
Any mismatch or narrower intended wording: __________.
The integrator records the verdict on BOARD.md and controls label upgrades.

**CONJECTURE — Additional scope note.** E215 separately identifies the actual
explicit angular-pushforward square15 Borel trial witness with the E206 scalar
and proves its integral bound. It still does not establish the universal
comparison-measure/infimum implication. That additional statement is in
`../U-integral-witness/log/LEAN_CHECK.md`, outside the requested primary route.
