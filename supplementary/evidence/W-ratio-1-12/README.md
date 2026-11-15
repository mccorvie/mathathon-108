# The bound package at the paper's own proportions, N/K = 1/12 (lane W)

Claude Opus 5.5 (Claude Code, [team machine]), for [team member], Sat 14 Nov 22:11 PT. EVENT WORK. No human has checked this.

**Why.** Calegari's blog (galoisrepresentations.org, 24 Sep 2026) reports that the paper behind the zeta(5) proof uses K = 12n, N = n, r = 6, h = 11n, i.e. (alpha, beta) = (1/12, 11/12). Fauzan's Lean template is (3/40, 37/40). The team's scan over (alpha, beta) (../scope_alpha_beta/) did not contain alpha = 1/12 exactly.

**Method.** The free-(alpha, beta) bound package of ../scope_alpha_beta/ (derivation_beta.md: PROOF-DRAFT; code imported read-only and unchanged): scan.py's cell() for float values, and certify_min.py's astar_cert / lb_cert (interval arithmetic, 113 bits, N = 1000) for the floors. Nothing in ../scope_alpha_beta/ was written.

## Result

| nu | zeta(7) floor A*(7)+LB (certified lower bound) | zeta(5): certified lower bound / float upper bound | zeta(5) |
|---|---|---|---|
| 2 | >= +1.073145 | +0.044210 / +0.146561 | fails |
| 4 | >= +0.946180 | -0.060764 / -0.043116 | closes (float upper bound) |
| 6 | >= **+0.890740** (smallest) | -0.076274 / -0.048417 | closes (float upper bound) |
| 8 | >= +0.915293 | +0.047238 / +0.148827 | fails |
| 10 | >= +1.069395 | +0.300008 / +0.353590 | fails |

- **COMPUTED (interval-certified):** at the paper's proportions, zeta(7) fails for every comparison measure and every even nu <= 10, with floor >= +0.8907. zeta(5) is excluded at nu = 2, 8, 10.
- **COMPUTED (float, not certified):** zeta(5) closes at nu = 4 and 6, the same window as at Fauzan's proportions. At nu = 6 the margin lies between -0.0763 and -0.0484 per K^2; per n^2 (K = 12n) that is 6.97 to 10.98. The blog reports gamma_5 = 3/2 per n^2 for the paper's own estimates (CITED, blog). This package's margin is larger.
- **Control:** at Fauzan's (3/40, 37/40) the same code gives a nu = 6 floor of +0.904378, matching the scan's certified +0.904376, and a zeta(5) bracket containing the certified [-0.07206, -0.07185].
- So the statement "within this package, no proportion closes zeta(7)" now also covers the paper's own proportion.

| claim | command (from this folder) | expected | time |
|---|---|---|---|
| float values, both proportions | `python3 -B run_cells.py` | out/run.log, out/cells.json (8 cells) | 2 s |
| certified floors at (1/12, 11/12) | `python3 -B certify_cells.py` | out/certify.log: 5 lines, all `CERTIFIED > 0: True` | 1.5 min |
