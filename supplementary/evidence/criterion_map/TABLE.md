<!-- Written by the orchestrator (Claude Opus 5.5), Sat Nov 14 2026, verbatim from the final return value of workflow wf_bb17aa9e-a57 (synthesizer, Claude Opus 5.5). Branch records: workflow_records.json. One re-check agent (nu = 10) failed when the Mac briefly slept (07:10 PT); its rerun outputs are in /tmp/claude-501/criterion_map/recheck_nu10/. -->

## #108 certified criterion table (α = 3/40, λ = 37/40, even ν ≤ 10, M → ∞)

EVENT WORK, synthesis, Claude Opus 5.5, Sat Nov 14 2026, 10:15-10:30 EST. This step was read-only and wrote nothing to the repo. I recomputed every sum myself as exact Fractions from certify/out/A.json and the agents' exact endpoints, then rounded outward at 7 decimals. They match the agents' files to rounding.

### 1. U*(ν) (COMPUTED: mpmath.iv 113 bits, certify_M0 and cmd_LB run unchanged; the lower end holds via Lemma 2, PROOF-DRAFT)

| ν | U*(ν) ∈ | U measure / dual σ |
|---|---|---|
| 2 | [−2.5062190, −2.5061250] | BR640 / BR320 |
| 4 | [−1.9670700, −1.9668427] | BR320 / BR320 |
| 6 | [−1.3855142, −1.3853066] | BR6_320 / BR6_640 |
| 8 | [−0.7619451, −0.7617450] | BR320 / BR320 (E49) |
| 10 | [−0.1000784, −0.1000050] | BR640 / BR320 |

Every row was re-certified bit for bit:
- ν = 2, 4, 6 by the verifiers;
- ν = 8 by the combine step;
- ν = 10 by a rerun nobody reported, found in /tmp/claude-501/criterion_map/recheck_nu10/. No ν = 10 verifier report reached me. No ν = 10 verdict depends on this rerun.

### 2. Table

- e_n = log Q^prim_K(ζ(s))/K² for n = 1, 2, ..., from exact CRT determinants.
- gap = A* + U − e_n at the largest computed n. Reading the gap as slack is HEURISTIC.

| s | ν | [A*+LB, A*+U] (COMPUTED) | package (COMPUTED) | exact e_n (COMPUTED) | gap (COMPUTED) |
|---|---|---|---|---|---|
| 3 | 2 | [−0.8577407, −0.8576467] | closes | | |
| 3 | 4 | [−0.8929284, −0.8927011] | closes (d) | | |
| 3 | 6 | [−0.8094734, −0.8092658] | closes (c)(d) | | |
| 3 | 8 | [−0.6331569, −0.6329568] | closes (c)(d) | | |
| 3 | 10 | [−0.4161761, −0.4161026] | closes (c)(d) | | |
| 5 | 2 | [+0.0487350, +0.0488290] | fails | −0.0648, −0.0022, +0.0225, +0.0180, +0.0338 (E35) | 0.015 |
| 5 | 4 | [−0.0520777, −0.0518504] | closes | | |
| 5 | 6 | [−0.0720602, −0.0718526] | closes | −0.1657, −0.1302, −0.1253 (E16) | 0.053 |
| 5 | 8 | [+0.0298812, +0.0300814] | fails | −0.0752, −0.0406, −0.0392, −0.0366 (E35), −0.0265 (E38) | 0.057 |
| 5 | 8, Prop. A | [−0.0103618, −0.0101617] | closes | same | 0.016 |
| 5 | 10 | [+0.2519663, +0.2520398] | fails (c) | +0.1287, +0.1672, +0.1579 (new) | 0.094 |
| 7 | 2 | [+1.0830058, +1.0830998] | fails | +0.8828, +0.9704, +0.9920, +1.0061 (E16) | 0.077 |
| 7 | 4 | [+0.9618806, +0.9621079] | fails | +0.8093 (skeptic 4) | 0.153 |
| 7 | 6 | [+0.9058044, +0.9060119] | fails | +0.7669, +0.8460, +0.8548 (E25) | 0.051 |
| 7 | 8 | [+0.9199507, +0.9201508] | fails | +0.7965, +0.8712 (E16) | 0.049 |
| 7 | 10 | [+1.0515410, +1.0516144] | fails | +0.9426 (skeptic 4) | 0.109 |
| 9 | 2 | [+2.1441169, +2.1442109] | fails | +1.7578, +1.9288 (E19) | 0.215 |
| 9 | 4 | [+2.0192417, +2.0194690] | fails | | |
| 9 | 6 | [+1.9519155, +1.9521231] | fails | | |
| 9 | 8 | [+1.9377458, +1.9379460] | fails | | |
| 9 | 10 | [+1.9920705, +1.9921439] | fails | +1.8075 (W9) | 0.185 |

Every "fails" row has its lower end above 0, so it fails for every comparison measure. (c): the row violates Fauzan's (4.9), read as (ν−1)α < (s−1)/6, and uses the rank clamp min(λ, ·) (criterion5 Thm 3, PROOF-DRAFT). (d), added Sat Nov 14 12:04 PT by the integrator (Claude Fable 5.2, [team machine]) from lane A's audit E100: at s = 3 and ν ≥ 4 the bracket is **not covered by the derivation as written**, which drops the primes K < p < (1 + (ν−2)α)K (criterion5/derivation.md §8, hypothesis (H2); PROOF-DRAFT). With the audit's sufficient extra cost (a−1)²/2 = 9/800, 9/200, 81/800, 9/50, the upper ends become −0.8814511, −0.7642658, −0.5317068, −0.2361026 (COMPUTED: decimal addition), so each row still closes, relative to that repair. Rows with s ≥ 5 and the row (3,2) are not affected.

### 3. Notes (COMPUTED unless labelled)

- No sign changes against E33. The widest bracket was 0.070 in E33 and is now at most 2.3e-4.
- The lowest ζ(7) floor is +0.905804 at ν = 6 (E33: +0.904155). At ν = 8 the floor rises from +0.906723 to +0.919950.
- A_M ≥ A* for all M ≥ 40 (E33(e)), so every "fails" holds at every M ≥ 40. A_200 + U ≤ −0.0289317 at (5,4) and ≤ −0.0397919 at (5,6).
- The ν = 4..10 measures lie inside (0, ∞), so E36's t = 0 caveat no longer affects (5,4). ν = 2's U measure starts at t = 0 and relies on E36(a) (PROOF-DRAFT); that matters only for (3,2).
- Correction to E38, E39 and the (5,10) report: they compared u_K with the loose LB(8) = −0.7752 and LB(10) = −0.1302. Against the pinned U*:
  - (5,8), n = 2-5: u_K − LB is −0.020 to −0.016 (E39 had −0.0067 to −0.0026);
  - (5,10): −0.137, −0.098, −0.077;
  - (5,2), n = 5: +0.097.
  
  HEURISTIC: the finite-K split into a_K and u_K has corrections of both signs, so E39's "no slack beyond the measure" does not follow.

### 4. (5,8) with Proposition A (E48, E50)

- A*_new = A*(5,8) − 1159/28800 ∈ [0.7515833258, 0.7515833367] (COMPUTED). The gain is exact and was found two ways. It also passes the Lean gate as gain58_formal and Iout_new_5_8 = 363473/288000; no human has compared those statements with the claims yet.
- A*_new + U(8; ρ_BR320) ≤ −0.0101617, and it is ≥ −0.0103618 for every measure (COMPUTED, relative to Prop. A and E13, both PROOF-DRAFT). The margin is < 0 for every M in 40Z from 840 to 2000. Without Prop. A the floor is +0.0298812; with opt36 the upper end is +0.0175.
- "Fauzan's method proves ζ(5) irrational at ν = 8" stays a CONJECTURE (E50) until a human checks Prop. A.
- (5,10): continuing the inner formula past K/3 in the same way would gain 583/8064. No Prop. A has been derived for (5,10), and the floor would still be +0.1796697 > 0 (COMPUTED).

### 5. Refined criterion

In this slice the method proves ζ(s) irrational iff A*(s, ν) < −U*(ν) (definition, E15), and U* does not depend on s. U* is now pinned to 2.3e-4 at every even ν ≤ 10 (COMPUTED), so no comparison measure can change a verdict; only the arithmetic estimates matter. With E13's estimates (inner Prop. 4.1 with offset s, outer (4.12)-(4.14) with the rank clamp, small-prime factor s + 1), the package closes exactly at s = 3 for every ν and at (5,4) and (5,6). Prop. A's outer estimate on K/3 < p ≤ 17K/40 adds (5,8) (COMPUTED, relative to PROOF-DRAFT estimates). At fixed ν the margin rises by the exact, U-free step 2λ/3 + ΔI_out, between 0.663 and 1.061 per s → s + 2. The best ν is 4, 6, 6, 8 for s = 3, 5, 7, 9 (COMPUTED). What is special about 5 (HEURISTIC): it is the only odd s whose margin is as small as the gap between the package and the exact forms. At s = 5 and ν ≤ 8, |A* + U*| ≤ 0.0721 while the gaps are 0.015-0.057, so the verdict depends on ν, on the measure (0.028 at ν = 8) and on the outer estimate near K/3 (0.040). With Prop. A, the package's verdict matches the sign of e_n at the largest computed n at all 11 (s, ν) with exact data; before Prop. A, (5,8) was the only mismatch (COMPUTED). At (5,2) and (5,10) the exact forms themselves grow (Q^prim > 1 at n = 3-5 and at n = 1-3), so no estimate in this template closes them (CONJECTURE for n → ∞). At s = 3 the margin is ≤ −0.416. At s ≥ 7 it is ≥ +0.9058 for every measure, while the gaps there are ≤ 0.153, so the s-step decides, not the estimates (E26, CONJECTURE for K → ∞).

Dependencies: E13 and Lemma 2 (PROOF-DRAFT); Xu (12) and Lai Lemma 11.4 (CITED); mpmath.iv's rounding is assumed correct. Buyarov-Rakhmanov is motivation only (CITED).

Files:
- /Users/[user]/Library/Application Support/Claude/scratch-workspaces/f84c0719-1fc3-4a02-8618-d18d9fee307c/41484cae-f9fd-4f1a-aadb-82b393529446/scratch-2026-11-13-630807/mathathon/problems/108-zeta-odd-autopsy/evidence/certify/out/A.json
- /Users/[user]/Library/Application Support/Claude/scratch-workspaces/f84c0719-1fc3-4a02-8618-d18d9fee307c/41484cae-f9fd-4f1a-aadb-82b393529446/scratch-2026-11-13-630807/mathathon/problems/108-zeta-odd-autopsy/evidence/nu8_rescue/combine/out/margins.json
- /Users/[user]/Library/Application Support/Claude/scratch-workspaces/f84c0719-1fc3-4a02-8618-d18d9fee307c/41484cae-f9fd-4f1a-aadb-82b393529446/scratch-2026-11-13-630807/mathathon/problems/108-zeta-odd-autopsy/evidence/criterion_map/ (measure_nu*/out, exact_5_10/out)
- /tmp/claude-501/criterion_map/recheck_nu10/out/
- /private/tmp/claude-501/-Users-jack-Library-Application-Support-Claude-scratch-workspaces-f84c0719-1fc3-4a02-8618-d18d9fee307c-41484cae-f9fd-4f1a-aadb-82b393529446-scratch-2026-11-13-630807/06c2099f-dc87-4dcb-a268-9095e8abfc2a/scratchpad/outward.py (my exact sums)
- /private/tmp/claude-501/-Users-jack-Library-Application-Support-Claude-scratch-workspaces-f84c0719-1fc3-4a02-8618-d18d9fee307c-41484cae-f9fd-4f1a-aadb-82b393529446-scratch-2026-11-13-630807/06c2099f-dc87-4dcb-a268-9095e8abfc2a/scratchpad/gaps.py (my gap column)