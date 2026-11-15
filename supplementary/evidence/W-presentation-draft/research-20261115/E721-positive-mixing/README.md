# E721: positive mixing separates finite savings from an asymptotic repair

Codex for [team member], 15 November 2026. This follow-up tests the
joint denominator-and-decay question. It changes no report, slides,
speaker notes, Lean source, or existing claim status. OMOS was not run:
the local driver reported no available platform credential.

## Result

**PROOF-DRAFT.** For the E719 repeated multiplicity profile, with
K_n=36n+4, moving one negative factor from t+1 to t+c, 1<=c<=4, gives
an elementary uniform raw-error bound

    0<r_n(c)-zeta(7)<exp(-60n),  for every n>=1.

The proof uses a factor-by-factor comparison and 21 exact rational
inequalities. This is a changed thin degree-one construction, not
the original h=37n determinant. See [PROOF.md](PROOF.md), sections 1-2.

**COMPUTED.** An adaptive continued-fraction choice of a rational
between the two endpoint approximants gives:

| n | K_n | Primitive denominator digits | Primitive residual decade |
|---:|---:|---:|---:|
|1|40|22|-21|
|2|76|41|-39|
|3|112|59|-58|
|4|148|78|-76|
|5|184|96|-94|
|6|220|115|-113|

Decade d means a strict enclosure between 10^d and 10^(d+1).
Every candidate retains positivity and comes from an exact positive
combination of the endpoint forms. Its primitive denominator is used,
not a coarse common multiplier. All six q_n<exp(55n) checks pass by
exact rational comparison. A separate direct-product residue checker
reproduces all mixed forms.

## Why this has not closed the proof

The adaptive choice is standard rational reconstruction in disguise:
varying c rationally can produce ANY rational inside the endpoint
interval. Its root stays in (1,4), but its rational height reaches
554 digits at n=6. The missing theorem is an ALL-n denominator bound
q_n<=exp((60-epsilon)n) for some epsilon>0. There is no such proof here.

**COMPUTED rational control.** Applying the same reconstruction rule
near the rational target 126/125 gives primitive residual exactly
1/125 at five precisions through 320 decimal places, despite raw
errors tending to zero. This prevents interpreting the zeta finite
table as evidence sufficient for irrationality.

**COMPUTED bounded comparison.** At each of the six scales, all
15,065 reduced parameters 1<c<4 with denominator<=128 were checked.
Every strict mixture tested is worse than the unmodified c=1 source.
Thus the large finite gain comes from the adaptive arithmetic choice;
it is not reproduced by this bounded parameter class.

The actionable remaining question is a structural denominator estimate
for an explicit parameter rule, coupled to the actual positive error.
Finite primitive smallness alone does not supply that estimate.

## Reproduce

From the repository root, run the following in this folder in order:

```sh
python3 check.py
python3 bounded.py
python3 replay.py
python3 analytic_certificate.py
```

The scripts need only the Python standard library. check.py credits
and imports E719/parent_verify.py and the inherited witness/zeta_rig.py
Euler--Maclaurin enclosure. bounded.py reads the freshly produced exact
endpoints. replay.py uses a different direct-product residue formula.
analytic_certificate.py checks exact finite inequalities; the all-size
integral argument remains written PROOF-DRAFT. No human, cross-family,
Lean, novelty, or irrationality upgrade is asserted.
