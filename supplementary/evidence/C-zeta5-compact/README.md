# Compact ζ(5) proof along the general-s chain

Codex GPT-6.1 sol, lane C for [team member]. A re-derivation of Fauzan's theorem
reusing Moritz Firsching's formalisation (mo271/Zeta5@be1c0d82, Apache-2.0);
Comparator metadata by Paul-Lez. No novelty or independence claim.

**LEAN-CHECKED:** the unconditional compact endpoint passes the repository
`--final` gate on Lean/Mathlib4.35.0, with no caller hypotheses and only
`propext`, `Classical.choice`, `Quot.sound`:

```lean
CCompactZeta5.irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```

**Primary artifact:** [project/](project/README.md), a standalone source-only
project containing exactly the282-file /69,392-line compact import closure.
Its own final3-target gate passes. [COMPACT_STATEMENT.md](COMPACT_STATEMENT.md)
has the exact scope, attribution, comparison and integration instructions;
[project/log/LEAN_CHECK.md](project/log/LEAN_CHECK.md) is the actual gate receipt.
[RESULT.json](RESULT.json) records both compact and heavy variants. Only the
integrator upgrades labels under the submitted-project/report/cross-family rule.

Build the primary project with Elan on PATH:

```sh
cd project
lake exe cache get
lake build
```

The default target is CompactEntry. All local proof sources are included;
Mathlib4.35.0 and PNT AlexKontorovich@127b50e3 are pinned, with no path dependency.
Ignored warm caches are local conveniences. Preserve LICENSE, NOTICE and the
source attribution headers. The parent development project also defaults to
CompactEntry and retains the gated heavy fallback as HeavyEntry.

**COMPUTED source sizes** (same import-closure method, external libraries
excluded for all rows):

| Endpoint | Files | Lean lines | Old Apery/Table lines | New field lines | Event scalar-cell lines |
|---|---:|---:|---:|---:|---:|
| Upstream Apery.Main | 209 | 138,236 | 117,029 | 0 | 0 |
| HeavyEntry fallback | 307 | 169,446 | 117,029 | 0 | 27,040 |
| CompactEntry / project | 282 | 69,392 | 97 | 16,960 | 27,040 |

The compact project has68,844fewer lines:49.8%reduction, with more files. The
initial forecast of far more than half reduction was not achieved. The97old
Table lines are the cheap analytic Tail proof; no old fine energy chunk is
reachable. All16scalar chunks count, including four unused cells in the last
chunk. `SIZE_STANDALONE.json` and `size_audit.py` list every source/import/hash.
The original251-file /218,572-line directory includes unreachable Table2;
that is a different metric, not the fair main-theorem baseline.

C0's accepted route is [ROUTE.md](ROUTE.md). C3's exact arithmetic/growth
instances, E604's finite-to-leading links and lane U's E244/E246/E247/E248
proofs compose without changing their canonical models or proof bodies.
The compact composition compiled first try. No ζ(7) irrationality claim is made.
The initial conditional snapshots are preserved as history, not proof sizes.

`SOURCE_MANIFEST.json`, `PROOF_MANIFEST.json`, the integration receipts and
`TRANSCRIPTS.json` preserve provenance. Timing receipts are incremental/cache
invocations, not a full cold-build benchmark. Do not rerun `prepare.py` over
this assembled development project: it records C0's initial construction.
