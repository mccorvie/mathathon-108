# U43 / E238: actual-field coercivity

Author: Codex (GPT-6), lane U. Logical source/config frozen at 2026-11-14 17:58:48 PT.
Overall report status: CONJECTURE. No human statement-comparison or novelty verdict is claimed.

**PROOF-DRAFT:** `U43.V6_coercive` proves, for every real `t` with `0 ≤ t`,
`5 * Real.sqrt t - 3 ≤ U16.V6 t`. The model is the imported, unchanged definition
`U16.V6 t = 2 * Real.pi * Real.sqrt t + U16.J 1 t - 6 * U16.J (3 / 40) t`,
where `U16.J a t = ∫ u in (0 : ℝ)..a, Real.log (t + u ^ 2)`.
The exact model source paths, lines, hashes, and inherited attribution maps are in `source-map.json`.
No field-growth assumption or desired-bound premise occurs in this theorem.

**PROOF-DRAFT:** `J_intervalIntegrable` handles every real endpoint `a` and every `t ≥ 0`.
At `t = 0`, Mathlib's identity `Real.log (u ^ 2) = 2 * Real.log u` and genuine
interval integrability of `Real.log` include the logarithmic endpoint. For `t > 0`,
the integrand is continuous. `J_one_zero` evaluates the actual integral as `-2`.
`J_one_lower` compares the actual integrals on the open interval `(0,1)`, avoiding
an invalid pointwise monotonicity assertion at `u = 0` under total `Real.log`.

**PROOF-DRAFT:** `J_alpha_upper` proves
`U16.J (3 / 40) t ≤ (3 / 20) * Real.sqrt (t + 1)` for `t ≥ 0` by integrating the
pointwise bound `log x ≤ 2 * sqrt x` and using `0 ≤ u ≤ 3/40 ≤ 1`.
The final proof combines these bounds with `sqrt(t+1) ≤ sqrt(t)+1` and Mathlib's
strict bound `3 < Real.pi`. It unfolds the actual field definition directly.

**COMPUTED:** `python3 build.py` completed with exit code 0 at
2026-11-14 17:58:39 PT in 3.89 seconds. `compiler.log` contains all seven
`#print axioms` outputs; each contains only `propext`, `Classical.choice`, and
`Quot.sound`. This is direct compiler evidence, not a claim that the parent gate
or human statement comparison has already occurred. The parent owns those checks.

Reproduce from this folder:

```sh
python3 build.py
```

The script raises only its own soft file-descriptor limit to 16384, invokes the pinned
Lean via `/Users/[user]/.elan/bin/lake env lean`, writes a live ignored `.lake/`
log, and archives `compiler.log` and `build-result.json` after completion. It uses
cached read-only imports through the frozen sibling `UBorelAEField` dependency.
The local umbrella `FieldAverage.olean` was absent; `FieldAverage.Field` is imported
directly instead. No sibling source or configuration was changed.

Requested parent gate: library `FieldCoercivity`, declarations
`U43.J_intervalIntegrable`, `U43.J_one_lower`, `U43.J_alpha_upper`, and `U43.V6_coercive`.

Scope: this packet contains no measure bound, extended-potential identification,
field-supremum finiteness theorem, optimized objective, admissibility theorem,
infimum theorem, or irrationality claim. Those are separate parent-owned results.
The proof follows the parent-supplied elementary comparison route and uses the
listed Mathlib lemmas; no claim of novelty is made. Licenses and inherited source
attribution are preserved. No upstream proof body was copied into this probe.
