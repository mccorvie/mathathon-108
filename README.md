# Compact ζ(5) re-derivation

A re-derivation of Fauzan's theorem reusing Moritz Firsching's formalisation
(mo271/Zeta5@be1c0d82, Apache-2.0; Comparator metadata by Paul-Lez).
The event general-s arithmetic chain is specialized at (5,6); lane U supplies
the coarse169-cell field certificate and actual closing inequality.
No new or independent irrationality theorem is claimed.

LEAN-CHECKED: CCompactZeta5.irrational_five, with literal conclusion
`∃ x, Irrational x ∧ riemannZeta 5 = x` and no caller hypotheses.
Its parent receiving project passes the final4.35gate, standard three axioms.
This standalone export also passes --final3/3; receipt: log/LEAN_CHECK.md.

Build with Lean/Mathlib4.35.0:

```sh
lake exe cache get
lake build
```

All local source dependencies are here. Mathlib and PNT are pinned in the
manifest; there is no path dependency. Ignored warm-cache links are only a
local convenience. A clean checkout fetches the pinned dependencies normally.
LICENSE/NOTICE and source attribution headers must be preserved.

COMPUTED:282local Lean files /69,392lines, including16,960lines of new field
certificate and27,040lines of event scalar cells. No old fine energy chunks
or unreachable heavy fallback are included. Upstream's main-theorem closure
is209files /138,236lines:49.8%fewer source lines, with more files. The initial
forecast of far more than half reduction was not achieved. Full comparison,
scope, transcripts and build history live in the parent evidence folder.
Only the integrator upgrades labels after the submitted-project gate,
verbatim report statement and recorded cross-family comparison.
