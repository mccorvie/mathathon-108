# E716 receiving review (lane N driver, Claude Opus 5.5, Sun Nov 15 2026)

**What ran.** Open Math OS chat `chat-25eacaa352`, project 108, launched once at 01:05 PT by lane N for lane W's G3 (the producer of `scope_alpha_beta/derivation_beta.md` is lane W's advocate, so AGENTS.md section 9 rule 6 allows the launch). **All 25 model calls were served by `moonshotai/kimi-k3.1-pro`** (`served_by` in the records; transcript `log/transcripts/omos/p-a217855738464a2684aabaf655cafe60-chat-25eacaa352-seq0.jsonl.gz`). 2.58 M tokens in, 37.7 k out, 506 s. Effort high, no swarm.

**What was fetched.** The reviewer's own 12 files are in `worker/`, unedited. **Not fetched, deliberately:** `fauzan_22826419.pdf` and `.txt`, which the worker downloaded itself (the VM has web access), and its `replay_evidence/` copies of our inputs. The team has no recorded licence for Fauzan's preprint, and AGENTS.md section 6 says to link papers, not commit them. The citation is Zenodo record 22826419.

**Replay (COMPUTED).** Both worker scripts, re-run unmodified in an isolated copy (they import only `fractions, itertools, json, math, mpmath, sympy`), reproduce the worker's outputs exactly. `review_free_beta.py` gives an identical `independent_results.txt` and an identical JSON. `verify_counterexample_sympy.py` gives an identical `counterexample_symbolic.txt`. **Independent check of the counterexample by lane N's own code** (exact residues): at (K, N, s, ν) = (7, 1, 5, 2) the X coefficient of μ_X(D_N^ν/D_K) is exactly 0 and the constant is 363851/19595520000000, as reported. At (10, 1, 5, 6) it is again 0.

## Verdicts and how they are taken

| Check | Reviewer | Reading |
|---|---|---|
| 1 Lemma 3′ (outer range, H ≠ r) | pass | accepted |
| 2 deg_X Δ_H = H for H < r | **fail** | **accepted.** The claim is false in general (11 of 120 small cases have lower degree). It is also not needed: clearing a rational denominator uses b^H with deg Δ_H ≤ H automatically. derivation_beta.md §0 should drop it or restrict it. |
| 3 Prop. 1′, s-step 2β/3 | pass | accepted; independent I_out(5) = 101999/96000 and I_out(7) = 5791/4000 at (3/40, 17/20, 6) give the step 18277/19200 |
| 4 Prop. 4.1 with h → H | pass | accepted |
| 5 C*(ν, α, β), Lemma 2′ | pass | accepted |
| 6 validity region, the +0.757 minimum | partial | **accepted.** The cell (11/80, 9/16, 8) satisfies all four conditions exactly (La_min = 0, min z_β = 19/240, 2β + να − 1 = 49/40 < 3, α < 1/6). But +0.757 is a minimum over the computed grid, not over the continuous derived region, and README §1(g)'s "the infimum is attained on the La edge" is not shown. The interval certificate was not re-run (its `certify/` helpers were not uploaded). |
| 7 numerics, code against formulas | pass | accepted; both uploaded logs replay byte for byte |
| 8 reading | partial | accepted: 22 E29 rows, not 21; "Deterministic" is too strong for bitwise JSON floats; `zmin()` is a sampled screen, not an exact minimum; the denominator-clearing degree b^H belongs in the §1 table |

**Lane N's addition.** The degree failure has a simple cause. An entry μ_X(t^m D_N^ν/D_K) contains X only if νN + m ≥ K − (s+1)/2, the residue-at-infinity condition. So deg_X Δ_H < H whenever H is small against K − (s+1)/2 − νN. Even at the template (K, N, s, ν) = (40, 3, 7, 6), the 1 × 1 determinant has no X. Since the X coefficients vanish on the antidiagonals i + j < K − (s+1)/2 − νN, deg_X Δ_H ≤ max(0, 2H − K + (s+1)/2 + νN). So the degree is below H for β < 1 − να + o(1): at α = 3/40 and ν = 6, that is every β < 0.55, part of the scanned range β ≥ 0.35. The reported minimum is not affected: there να = 1.1 > 1, so every entry carries X.

**Label consequences.** derivation_beta.md now has one second-family review (Kimi, proof-text and computation): its bounds pass, and one side claim fails and is unneeded. Its labels stay PROOF-DRAFT and COMPUTED. The derivation belongs to lane W, so lane N does not edit it. The corrections are lane W's to make (board NEED).
