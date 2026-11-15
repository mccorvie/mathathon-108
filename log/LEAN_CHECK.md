# Lean check
Run 2026-11-14T20:25-08:00 on `CompactEntry` in `/Users/mathathon/code/mathathon/problems/108-zeta-odd-autopsy/evidence/C-zeta5-compact/project`.
**Overall: PASS**


## Versions
- PASS: Lean v4.35.0, Mathlib v4.35.0

## Build
- PASS

## Declarations

| Declaration | Verdict | Axioms | Problem |
|---|---|---|---|
| `CCompactZeta5.irrational_five` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `CCompactZeta5.finite_real_bound` | **PASS** | propext, Classical.choice, Quot.sound |  |
| `U49.local_field_certificate` | **PASS** | propext, Classical.choice, Quot.sound |  |

## Statements (a human must compare each with the claim in the report)

### `CCompactZeta5.irrational_five`
```lean
CCompactZeta5.irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = ↑x
```
### `CCompactZeta5.finite_real_bound`
```lean
CCompactZeta5.finite_real_bound : CCompact.FiniteRealBoundStatement
```
### `U49.local_field_certificate`
```lean
U49.local_field_certificate : ∀ (t : ℝ), 0 < t → t ≤ 2 → 2 * Apery.Uρ t - Apery.Vfield t ≤ -1323 / 200
```

## Source scan (warnings)
No forbidden tokens.
