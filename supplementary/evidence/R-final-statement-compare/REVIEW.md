# Final-project statement comparison: D5–D9 and D20

Reviewer: Codex GPT-6.1 sol, lane R librarian, responding to the integrator's
21:36 request. Authors: Claude Opus 5.5, as recorded in the source headers
of SStep, SStepAll, OuterValues58, ClassLoss, OffsetGap, LaiSkip and DeltaEq/Core.
No subagent, proof-body audit, fresh Lean gate or human comparison is claimed.
The integrator decides labels. This file is source/review support under AGENTS §10.

**COMPUTED — Identity receipts.** All 13 inspected source files are byte-identical
to local judged-repository commit `f385dbf705d94fb411b74c9692639e508fd0b546`.
This is not a public-push receipt. The nine printed report types equal the
types in that project's gate report after whitespace is deleted. Input hashes,
the report snapshot hash and the comparison results are in [INPUTS.json](INPUTS.json).
Types are reproduced in [PRINTED_STATEMENTS.md](PRINTED_STATEMENTS.md).

**COMPUTED — Definition coverage.** [UNFOLDED_DEFINITIONS.md](UNFOLDED_DEFINITIONS.md)
contains 67 verbatim custom definitions, with namespace context and source lines;
[DEFINITIONS.json](DEFINITIONS.json) is the machine-readable version.
The collection includes the entire literal coefficient list under `Skip.DeltaLit`,
the list-polynomial operations under `entry`, and all 16 scalar-model definitions
under `thetaPkg`. It stops at standard Mathlib real/rational/polynomial/matrix,
finite-set/list, floor, p-adic valuation and Lebesgue interval-integral operations.
The collector is [collect.py](collect.py); text identity alone is not the
semantic comparison below.

## Individual verdicts

**PROOF-DRAFT — Semantic statement comparison.** Each verdict below is
**match with the stated differences**. The differences are part of the verdict;
they do not establish the unformalised interpretation of a scalar model as a
valuation or analytic bound.

| Report | Declaration | Scope and differences |
|---|---|---|
| D5 | `Mathathon.P108.thetaPkg_sstep` | Real `s,ν,α,U`; real `M≥3`; the same free scalar U cancels. This is the defined scalar model, with no measure, analytic bound or derivation from valuations. The total all-real extension issue below matters outside the report's physical slice. |
| D6 | `Mathathon.P108.theta_sstep_7_6` | Exactly `751/768` for the difference of `thetaPkg` at `(7,6)` and `(5,6)`, fixed `α=3/40`, every real `M≥3,U`. No statement about the actual determinant. |
| D7 | `Mathathon.P108.sstep_ge` | The displayed outer-function difference plus `2(1−3/40)/3` is at least `167/300` for every real `s≥7,ν≤10`. No lower bound on ν, parity condition or measure occurs. Applying it to a theta difference also uses D5. |
| D8 | `Mathathon.P108.thetaPkg_odd_ge` | Every natural n, real `ν≤10,M≥3,U`, fixed `α=3/40`: the model at `7+2n` is at least its value at 7 plus `n·167/300`. A positive starting floor and a certificate-failure conclusion need separate input. |
| D9 | `Mathathon.P108.gain58_formal` | Exact integral of `Tout 5 8 (3/40) y − y*innerR 5 8 (3/40) (1/y)` on `[1/3,17/40]`, equal to `1159/28800`. It does not prove Proposition A or identify the replacement integrand as a valid prime-valuation bound. |
| D20 | `Mathathon.P108.classLoss_witness` | The concrete affine entry has valuations −10 and 0 at 13, the concrete class-count minimum is −4, and their loss is 6. It concerns this explicit entry; the alleged certificate's need for a smaller loss is an external code reading. |
| D20 | `Mathathon.P108.lai_offset_gap_7_2` | Exact difference of two defined inner integrals at offsets 7 and 1, ν=2, α=3/40, M=200. The value is `21867/12000`. Identifying offset 1 with the audited program is an external code reading, not part of the theorem. |
| D20 | `Mathathon.P108.Skip.lai_skip_witness` | Concrete skip predicate at `(s,K,p)=(11,40,17)`; `Skip.F 11 2 1` has content valuation −247 and has a coefficient of negative 17-adic valuation. The function/polynomial is the separately defined Skip template, not a theorem quantified over every program or prime. |
| D20 companion | `Mathathon.P108.Skip.Delta_eq` | Exact equality of `det(Skip.G 11 2 1)` with the degree-at-most-37 literal polynomial. It is unconditional in the submitted gate; this review compares its statement and definitions, not the interpolation/Hankel proof. |

## Scalar definitions against the report

**PROOF-DRAFT — Unfolding comparison.** Write λ=1−α. `thetaPkg` is
`U + Iout + (s+1)λ/M + ∫₃ᴹ innerR(x)/x³ dx`, exactly the report's scalar
object. `ell(u,z)=floor(u−z)+floor(u+z)+1`; `Hc=λ+να/2`, `Tc=floor(2Hc*x)`,
`sigmaC=Hc*x−Tc/2`, and `nplus=(2x−floor(2x))/2`. `gammaIntegrand`,
`innerGamma`, `Jfun`, `innerN` and `innerR=−innerGamma−innerN` agree term
by term with the displays in Claim 2. Integrals are real Bochner interval
integrals against Lebesgue measure. The report now prints ell and J as well;
the earlier comparison's missing-formula qualification is no longer needed.

**PROOF-DRAFT — Outer comparison.** `cRem` sums `max(0,ℓ+s−1−ν−2i)` for
`i<ℓ−2`; `zRem` adds 1 to the count with that argument nonpositive. On
`1/3<y≤1`, `gOuter` uses the report's k,v,u,m,densities,cost,zero count and
rank cap, with ℓ=2k,2k+1,2k+2. `Tout=gOuter+legendreTerm` and
`Iout=∫₁⁄₃²λ Tout`. The Legendre term is the six-term sum actually printed
in the current report. `Nat.floor(1/y)` equals the report's integer floor
on the positive integration interval used by the physical slice.

**PROOF-DRAFT — Additional scope clarification requested.** The Lean
definitions are total on all real α: `gOuter` is zero whenever its guard
fails, and the outer floor is the natural floor. The report's mathematical
display specifies g on `1/3<y≤1` and sets it to zero for `1<y≤2λ`; it does
not specify that extension below `1/3` if α makes the integration limits
reverse. Thus D5 matches the explicitly printed Lean model for all real
arguments, and the displayed mathematical model on the intended slice.
An all-real reading of the prose should say it uses those total Lean
definitions, or restrict the prose to the physical shape domain. This is
a definition/scope qualification, not a counterexample to D5.

## The explicit audit objects

**PROOF-DRAFT — Class-loss object.** `entry=(A,B)` is computed from
`Z=D₃² * ∏_{c=0,…,6;c≠2}(t+c²)^10` and `D₄₀`, using monic list-polynomial
division and its remainder's simple-pole residues. The monomial and pole
formulas in `entryWith bernoulli` are the s=7 Bernoulli functional and
`j⁶(X−H_j^(7))+1/(2j)−1/6`. `xRoots` includes seven zeros plus the ±roots
with these multiplicities; `poles` consists of ±1,…,±40. `beta` is the
minimum root-minus-pole count over residues 0,…,12. This is the entry
and class minimum claimed in D20, not a declaration about all Hankel entries.

**PROOF-DRAFT — Skip object.** For K=40n,N=3n,h=37n, `Skip.muX` applies
the same displayed Bernoulli monomial and simple-pole formulas to
`f/D_K` via polynomial quotient and residues. `G` has entries
`muX s K (D_N^ν*t^(i+j))`; `Delta=det G`; `F=C(S)*Delta`, with the
factorial scale displayed in the report. These are separate Skip names;
no equality theorem with `AperyS.FS` is asserted by these declarations.
`HasContentVal p f v` means f is nonzero, every nonzero coefficient has
valuation at least v, and one nonzero coefficient attains v. Thus it
specifies the actual content valuation, not just a lower bound. `laiSkips`
is the integer test `2p−2 < s*(3K/40)`, where natural division truncates.
At the specialized values its two sides are 32 and 33. `DeltaLit` is
the sum of the first 38 explicitly tabulated rational coefficients times
X^i; `coefQ` returns zero outside the table.

## Authorship boundary and remaining actions

D10's current provider and wrapper are Codex (`ShortArithmeticFloor.lean`,
`AllM.lean`). D18 and D19 are Codex (`Zeta5S/FiniteStep.lean`, header E309).
This Codex review cannot supply their cross-family receipt. Claude's
existing `integrator-statement-compare/compact_leaves.md` §5 explicitly
compares `U58.arithmetic_allM_strict`, records its type identity with D10,
and discusses the U18 wrapper; the integrator can record the exact wrapper
comparison. D18/D19 need a Claude or other non-GPT reviewer. Their five
declarations are not included in the nine qualifying verdicts above.

Separate wording issue: D4 defines `normalizerSharp : ℚ`, and its
normalisation statement produces an integer polynomial after multiplying
by it. Neither that type nor that statement asserts that the multiplier
itself is an integer. The report's two unqualified “integer multiplier”
glosses should use “positive rational denominator-clearing multiplier”
unless a separate integrality proof is supplied. This does not assert
that any particular multiplier is nonintegral.

The report's request for a second-family review of the **proof** of
`Delta_eq` remains separate from this statement comparison. No R label
upgrade, full-program audit, citation-priority verdict or human check.
