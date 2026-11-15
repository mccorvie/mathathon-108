# Global upper certificate for the original ratio

Codex, Sat Nov 14 2026 PT. Scoped lane A follow-up to the E710 second-party
review. This packet repairs the missing global potential bound for two
existing comparison measures. It does not alter the report, selected
problem, source producer packet or active worker assignments.

**COMPUTED:** with alpha=1/12, beta=11/12, s=5 and the explicit measures
in witnesses.json translated right by 10^(-12), certify.py verifies:

| nu | Global potential target tau | Accepted cells | Limiting margin, safe upper | M=1000 margin, safe upper |
|---|---|---|---|---|
| 4 | -801/125 | 434 | -0.0334 | -0.0287 |
| 6 | -667/100 | 377 | -0.0392 | -0.0327 |

Each number in the two right columns is rounded UP, so it remains an
upper bound. Exact rational interval endpoints, every cell, and the
infinite-tail checks are in results.json. Maximum bisection depth: 21.
An entire rerun matches every non-runtime output exactly.

**PROOF-DRAFT:** PROOF.md justifies the endpoint envelope by the flat
minimum of each arcsine potential, controls the whole tail by a decreasing
elementary function, and gives an explicit finite-cutoff upper error.
The source's compact-support-in-(0,infinity) hypothesis prompted the small
translation: the actual translated potentials are certified again, rather
than assuming the old bound survives translation.

**CONJECTURE (integrated research claim):** the stated inherited package
closes at s=5, nu4/6, original ratio and M=1000. This depends on the
existing arithmetic derivation and analytic theorem, not established anew
by these computations. No human, Lean or novelty upgrade; no zeta(7)
irrationality conclusion. The previous E710 warning about its *sampled*
top5 values remains correct. This packet supplies separate upper evidence.

## Reproduce

From this directory, in a checkout containing the preceding E710 packet:

```sh
python3 certify.py
python3 reviewer/check.py
```

The second command checks the saved cell certificate with a separate
160-bit implementation (see reviewer/REVIEW.md for exact scope). Both
agents are Codex: this is same-family review, not cross-family or human
verification. The parent reruns the reviewer's executable before upload.

Dependencies are Python, mpmath, numpy and scipy; INPUTS.json records
versions and hashes. Five existing executed modules are imported read-only
from the frozen E710 replay, with all dependency hashes checked before
import. Interval primitives and arithmetic integration are credited to
Claude Opus 5.5; the witness search is the source W-ratio-1-12 work.
This is not an independently implemented arithmetic integration engine.

Remaining obstacle: integrate this bounded result only after checking its
inherited package and source hypotheses to the project's required standard.
It is supporting numerical evidence about s=5, not a stronger s=7 result.
Exact source references and what was actually opened are in SOURCES.md.
WORK_RECORD.md is a condensed AI-use record, not a full native transcript.
