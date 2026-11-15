# E733 receiving review (lane N driver, Claude Opus 5.5, Sun Nov 15 2026)

**What ran.** One local fresh-context Claude Opus 5.5 subagent, at [team member]'s request (`local-review/REVIEW.md`,
06:25 to 07:00 PT). **This is a same-family check**: Claude reviewing Claude. It wrote only in `local-review/`.

**Replay (COMPUTED).** Lane N re-ran its eight scripts in place, after backing up their outputs, and then restored the
reviewer's JSON files.
- `selftest`, `coverage`, `hunt_holes`, `band3`, `check3` and `falsify2`: identical to the originals apart from timings.
  `falsify2.out` also has a shell `time` line, which the script does not print.
- `falsify_membership` takes a draw count as its argument. With 1500, the value the reviewer used, it reproduces exactly:
  35925 draws, 4954 window-valid points outside the derived region, 0 holes. With the default 1000 it gives 23953 draws and
  also 0 holes.
- `check3b`: its first line reproduces. Its second line (the near-breakpoint maximum, 0.1249995 ≤ 1/8) is not printed by the
  saved script, so it was not replayed. It is consistent with the proved bound and with E732's `window.py`.

| Check | Reviewer | Reading |
|---|---|---|
| 1 The x = 3 test is necessary; hunt for holes | pass: 1352 window(x=3) boxes and 13,520 points, 0 window-feasible on (3, 3.5]; 5180 saturation-box points, all z₇ < 0; exactly sharp at x = 3 + 10⁻⁹ (0/1156, 0/1155); finite p = 106649, 10/10; re-derived exactly at a finite prime (h − L₀ ≥ (m − N)k), with the corrections going the safe way | accepted (replayed); its finite-K remarks are now in the README |
| 2 Coverage | pass: the 1398 La boxes are exactly re-tiled; even ν ≤ 10 never used the La verdict; ν = 1..24 each tile area 1/3 with no overlaps and nothing unresolved; overall min +0.48273 | accepted (replayed) |
| 3 The bound outside the derived region | pass: even ν at La_check < 0, window R = `pkg_ab.R` exactly (120 points × 64 x); odd ν, \|ΔR\| ≤ 1/8 | accepted (replayed, except `check3b`'s second line) |
| 4 Falsification | pass: 4954 window-valid points outside the derived region, none in a non-certified box; 54 floors, no bound above the floor, smallest slack +0.108 | accepted (replayed) |
| 5 ν ≥ 25 | **partial**: "k = ⌈ν/2⌉ − 1 ≥ (ν − 1)/2" is false at even ν, and "empty" holds only for α > 0 | **accepted and fixed**: new Lean corollary `E730.window3_empty_even` (the lemma applied at ν − 1); the README says α > 0 and points to E730's α = 0 column |
| 6 Replays of E733's own scripts | pass | accepted |
| 7 The reading | partial: the even-ν / α > 0 wording; the x = 3 section gave only the limit; "3000 points" meant 2029 kept; the pointers said "certified" without E733's label; "as far as his validity proof allows" should name his row basis and weights | **accepted, all fixed** in E733's README and the E730/E732 pointers |

**Label consequences.** E733 stays COMPUTED given PROOF-DRAFT steps, now with one passing same-family review. The two cut-off
lemmas are LEAN-CHECKED: the gate re-run of 07:05 passes all 19 declarations with `--final`. No number changed. A second-family review is still
missing for E732 and E733.
