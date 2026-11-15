# E731 receiving review (lane N driver, Claude Opus 5.5, Sun Nov 15 2026)

The reviews of E730 (`../E730-box-certify/`, the interval box certificate of the ζ(7) floor) are collected here: two
same-family reviews (Claude reviewing Claude, sections 1 and 2) and one second-family review (Kimi K3.1 Pro, section 5). All
three pass, and lane N replayed every script of each.

## 1. Local review (`local-review/`)

**What ran.** At [team member]'s instruction (Sun 02:55: "From now on just do everything locally"), a fresh-context Claude
Opus 5.5 subagent ran E731's brief in this checkout. It worked from the brief and the files only, without the author's
reasoning, from 02:58 to 03:18 PT. It wrote only in `local-review/`. It ran the team's code from verbatim copies in
`local-review/work/evidence/` and never ran git, sync or omos.

**Replay (COMPUTED).** Lane N re-ran all seven of its scripts in place, after backing up their outputs:
`check1_sample.py`, `check46_cover.py`, `check3_reductions.py`, `check5_tout.py`, `check_replay.py`, `check2_fgrid.py`
and `check3b_tail.py`, 03:18 to 03:31.
- All exited without error.
- Every JSON output is identical to the subagent's, apart from timing fields (`sec`), and every stdout file is unchanged.
- The five copied team modules (`pkg_ab.py`, `scan.py`, `ivlib.py`, `run.py`, `theta.py`) are byte-identical to the originals (`cmp`).

| Check | Reviewer | Reading |
|---|---|---|
| 1 Falsification by sampling | pass: 322 points, 312 with a package value (258 admissible), 488 point-box pairs, no violation, smallest slack +0.0832 (ν = 2, (11/80, 39/40)) | accepted (replayed) |
| 2 Soundness of the centred form | pass: an independent f stays above floor_lo by ≥ +0.038 on 200 boxes; the gradients lie in the stored hulls; floor_lo is reproduced exactly on 40 boxes | accepted (replayed) |
| 3 Reductions | pass: both closed forms; Q ≥ −1/4; R = xF + Q exact at 2500 points with β up to 2; the cancellation; the arcsine potential; Lemma 2′ admissibility | accepted (replayed) |
| 4 Invalid verdicts | pass | accepted (replayed) |
| 5 Code against the package | pass: 3000 integrand samples with no enclosure or gradient failure; ∫V dσ inside [W_lo, W_hi] in 10/10 boxes | accepted (replayed) |
| 6 Coverage | pass: the boxes tile the rectangle exactly; 58,088 random region points all lie in certified boxes. Note: `scan.cell` cannot evaluate α = 0 (ZeroDivisionError in `La_check`) | accepted; the claim is now 0 < α < 1/6 |
| 7 Lean lemmas | pass: compiled, standard axioms. Caveats: `tail_ge` holds for any q, integrable or not; `hasDerivAt_J` needs t > 0; `min_max_zero` is trivial; Lean does not show that this Q is the Q of R = xF + Q | accepted; the caveats are now in the README's table |
| 8 The reading | partial: labels "Lean" and "classical" are not allowed labels; α ≤ 1/6 should be α < 1/6; β ∈ (1.125, 2] is new ground for the package itself; derivation_beta §3 line 106 writes the y > 1 normaliser as (2β − y)₊ alone | accepted, all fixed in E730's README (below) |

## 2. Lane W's spot-check (`../../../W-E730-spotcheck/`, commit c0b4e8b9)

Also Claude Opus 5.5, a separate session, so also same-family. Lane N replayed both of its scripts:
- `check_formulas.py` reproduces its numbers: both closed forms against exact series sums; the cancellation at 1000 random
  points, max difference 3.7·10⁻⁴⁰.
- `check_boxes.py` reproduces its 30 random admissible points in certified boxes (β up to 1.74): no violation, smallest slack
  +0.0868, 2 min 27 s.

## 3. What changed in E730

The README now:
- says 0 < α < 1/6, and "no (α, β, ν) in the derived region rescues ζ(7) within this package";
- labels the 14 lemmas LEAN-CHECKED, with the Lean caveats in the table;
- labels the arcsine potential PROOF-DRAFT plus COMPUTED;
- says that β ∈ (1.125, 2] is the package's first computation there, and that Lemma 3′ / Theorem 3′ have not been checked
  numerically at β > 1;
- records the line-106 slip.

No number changed.

**The line-106 slip** is in the integrator's file, `scope_alpha_beta/derivation_beta.md`, so lane N does not edit it.
- Line 106 gives the y > 1 normaliser as (2β − y)₊ alone.
- The general formula is Σ_{j≥1}(2β − jy)₊. It appears in the file's own table row (line 51) and its T_out formula (line 103),
  and it is what `pkg_ab.Tout` computes. It comes from v_p(∏_{i<H}(2i)!²) = Σ_j (2H − jp)₊ for p > K (PROOF-DRAFT).
- The two agree when β ≤ 1. Lane W agrees, and its break-even split uses β = 37/40 < 1, so it is unaffected.

## 4. Label consequences

- E730 stays COMPUTED, given the PROOF-DRAFT reductions in its README's table.
- Two same-family reviews, E731's local review and lane W's spot-check, have found nothing against it, and neither has the
  author's own cross-check or spot check.
- The 14 Lean lemmas stay **LEAN-CHECKED**. AGENTS.md's label table upgrades a gated declaration to LEAN-VERIFIED only after
  a recorded statement comparison, by a human or by a model family other than the author's. The local review's comparison
  (check 7) is same-family, so it does not count.
- Kimi's check 7 (section 5) is a second-family statement reading, and it finds a match. It still is not the full
  LEAN-VERIFIED procedure (section 5).

## 5. Second-family review (Kimi K3.1 Pro, `chat-d888090ac8`): pass with one qualification

**What ran.** Launched once at 02:48 (LAUNCH.json), before the switch to local work, and collected at 04:05 with no follow-up
message. **All 100 model calls were served by `moonshotai/kimi-k3.1-pro`** (13.16M tokens in, 56.8k out, 4305 s; transcript
`log/transcripts/omos/p-a217855738464a2684aabaf655cafe60-chat-d888090ac8-seq0.jsonl.gz`). Its 29 files are in `worker/`,
unedited. Not fetched: its `worker/evidence/` copy of our 31 inputs, and `__pycache__`.

**Replay (COMPUTED).** Lane N rebuilt the `N-E731-review/{inputs,worker}/evidence/` layout in an isolated scratch copy from the
same 31 input files, and re-ran every script. The fetched originals were kept for comparison.
- `falsify_sample.py` (632 points, 1733 s on 4 cores): all 633 records match to 10⁻⁶.
- `analyze_sample.py`, `auxiliary_f_check.py`: their summaries match to 10⁻⁹.
- `invalid_saturation_audit.py`: identical.
- `reduction_structure_audit.py`: identical except W_quadrature, where Wlo, W and Whi all shift together by about 2·10⁻⁸. That is
  the platform variation of `lb_opt`'s numerically optimised trial measure, which the reviewer also reported, and W stays inside
  [Wlo, Whi] on both machines.
- The ν = 8 cover replay (`cover.py 8`, 182 s): bounds identical to E730's on this machine (difference 0.0); on the VM they
  differed by at most 1.7·10⁻⁸.
- `validate_results.py`: PASS.
- The Lean audit file is our `E730Lemmas.lean` verbatim plus `#print axioms`, so the gate's run covers it.

| Check | Reviewer | Reading |
|---|---|---|
| 1 Falsification by sampling | partial, only because `scan.cell` cannot evaluate α = 0: 632 points, 265 derived-admissible, 332 point-box pairs, no violation, no orphan, smallest slack +0.0822 (ν = 2, (7/48, 77/80)); large β (71 points up to 461/240) ≥ +0.110 | accepted (replayed). α = 0 is handled in E730's extension through the certified α ∈ [0, 1/48] boxes |
| 2 Centred form | pass, with a written argument for (a) to (f) | accepted |
| 3 Reductions | pass: closed forms from harmonic sums; Q ≥ −1/4; the cancellation; the arcsine potential by differentiating in z (60-digit quadrature agrees to 3·10⁻⁶¹); Lemma 2′ admissibility | accepted (replayed) |
| 4 Invalid verdicts | pass | accepted (replayed) |
| 5 Code against the package | pass: 2000 + 2000 exact comparisons, no failure; independent 8192-node W inside [Wlo, Whi] | accepted (replayed) |
| 6 Coverage | pass, with a continuity argument at α = 0 | accepted |
| 7 Lean | pass: compiled, standard axioms; the Lean Q faithfully transcribes `pkg_ab.PkgAB.Q`; the statements match what `box2.py` uses | accepted. This is a second-family statement reading, but it does not by itself make the lemmas LEAN-VERIFIED (section 4) |
| 8 The reading | pass: no material overstatement | accepted. The local review's check 8 points were fixed anyway |

**Label consequences.** E730 now has one passing second-family review (Kimi) and two same-family ones, and lane N has
replayed all of them. Its result stays COMPUTED given the PROOF-DRAFT reductions. Kimi checked the PROOF-DRAFT
reductions in writing (checks 2 and 3). Whether any of them can be reported as WRITTEN PROOF is the integrator's call: AGENTS.md
requires each complete proof to be written out in a file, and E730's README gives only short arguments. The Lean lemmas
stay LEAN-CHECKED: LEAN-VERIFIED also needs the gate in the submitted project, the statements printed in the report, and a
`DONE statement-compare` board line with a file that unfolds every definition. That is the integrator's step.

The review predates E730's extension to ν = 12 to 22 and α = 0 (04:20 to 04:50), so it does not cover that extension.
