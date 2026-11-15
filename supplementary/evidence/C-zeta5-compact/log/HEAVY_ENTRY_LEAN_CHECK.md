# Lean check
Run 2026-11-14T20:07-08:00 on `HeavyEntry` in `/Users/mathathon/code/mathathon/problems/108-zeta-odd-autopsy/evidence/C-zeta5-compact`.
**Overall: PASS**


## Versions
- PASS: Lean v4.35.0, Mathlib v4.35.0

## Build
- PASS

## Declarations

| Declaration | Verdict | Axioms | Problem |
|---|---|---|---|
| `CHeavyZeta5.irrational_five` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `HeavyInstance.heavy_finite_real_bound` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCompactWithClosing.closing` | **PASS** | propext, Classical.choice, Quot.sound |  |

## Statements (a human must compare each with the claim in the report)

### `CHeavyZeta5.irrational_five`
```lean
CHeavyZeta5.irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```
### `HeavyInstance.heavy_finite_real_bound`
```lean
HeavyInstance.heavy_finite_real_bound : CCompact.FiniteRealBoundStatement
```
### `CCompactWithClosing.closing`
```lean
CCompactWithClosing.closing : CCompact.ClosingStatement
```

## Source scan (warnings)
No forbidden tokens.
