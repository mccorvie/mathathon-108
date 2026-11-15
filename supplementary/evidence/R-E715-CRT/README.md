# E715 scope: explicit CRT counterexample to universal H

Reviewer/author: **Codex GPT-6.1 sol**, lane R. This is an additional
scoped finding after [partial E714 check11](../R-E714-partial/REVIEW.md),
not a blanket E714 review. No subagent or OMOS launch was used.

**Later strengthening:** [POSITIVE_ROOT_PROOF.md](POSITIVE_ROOT_PROOF.md)
and [POSITIVE_ROOT_EXAMPLES.json](POSITIVE_ROOT_EXAMPLES.json) now give a
separate construction INSIDE E713's positive-integer-square-root subclass,
still with unrestricted height. It forces tau>=4 on all covered p=1mod4,
has no complete prefix root block, and yields excess>=5K/6+o(K) by prior
PNT-for-AP. The original packet below concerns general B; its earlier
scope limitation is superseded by this added construction, not by inference.

**PROOF-DRAFT.** E715's unrestricted whole class permits a family
at s=7, v=N=0, A=P_K^2 with deg P_K=K/2-2, retaining every pole,
for which tau_p>=4 at all primes K/2+3<=p<=K. Coefficientwise CRT
forces this divisibility; a constant lift prevents cancelled poles.
Ordinary PNT then gives weighted excess >=1.5K+o(K), contradicting
H if conjectured for the whole advertised class.

**COMPUTED.** [Own standard-library code](check_crt.py) constructs
K=40,80,160 examples and evaluates all large-prime tails exactly.
[EXACT_EXAMPLES.json](EXACT_EXAMPLES.json) includes the full P coefficients,
degree/congruence/nonzero-pole checks and actual valuations. Weighted
logarithmic totals are floating diagnostics, explicitly distinguished.

Read [PROOF.md](PROOF.md) for the construction, prior PNT source,
asymptotic argument and scope. This does not produce q*e->0 or refute
an implication restricted to families expressly assumed to satisfy H.
The E713 positive-integer-square-root subclass is narrower than E715's
advertised B>=0 class; this ORIGINAL example does not cover it, while the
separate positive-root construction above now does.
No sufficient height restriction, novelty or proof-status upgrade is claimed.

```sh
python3 problems/108-zeta-odd-autopsy/evidence/R-E715-CRT/check_crt.py
```
