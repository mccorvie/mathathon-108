# Local review of E733 (the ζ(7) floor on the whole window region)

reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)

**This is a same-family check.** The reviewer is the same model family as E733's author, so shared blind spots are possible.
It is not a second-family review. EVENT WORK, Sun Nov 15 2026, about 09:20 to 10:05 PT.

Read in full: E733 `README.md`, `extend.py`, `check_window3.py`, `check_gap_points.py`, `extend.log`; E730 `README.md`,
`box2.py`, `cover.py`; E732 `README.md`, `window.py`, `cover_odd.py`, and its `local-review/REVIEW.md` (check 5), `my_window.py`,
`check5.py`, `gap.py`; `scope_alpha_beta/derivation_beta.md`, `pkg_ab.py` (`R`, `Q`, `zmin`, `La_check`), `scan.py`; the Lean
lemma `E730.window3_empty` and the gate output `lean/log/LEAN_CHECK.md`; Fauzan, *ζ(5) is irrational* (Zenodo 22826419),
§4.1 with (4.1)–(4.8) and the proof of Prop. 4.1 (local text, not copied).
I wrote every script in this folder myself. My window code `rv_window.py` decides feasibility by a formulation different from
E732's and E733's (no forced window base and no greedy step; see check 1). Team modules are imported read-only. Nothing
outside `local-review/` was written. The two replays ran on copies in `work/` (team folders symlinked read-only, `python3 -B`).

## Verdicts

| # | Check | Verdict | Label |
|---|---|---|---|
| 1 | The x = 3 test is a necessary condition; hunt for a wrongly invalid box | **pass**, no hole found | PROOF-DRAFT (argument) + COMPUTED (hunt) |
| 2 | Coverage of [0, 1/6] × [0, 2] for ν = 1..24 from the JSON files | **pass** | COMPUTED |
| 3 | E730's bound applies on the window region outside the derived region | **pass** | COMPUTED + PROOF-DRAFT |
| 4 | Falsification by sampling window-valid points | **pass**, no counterexample | COMPUTED (sampled) |
| 5 | ν ≥ 25 empty, `E730.window3_empty` | **partial**: true, but the README's justification is false at even ν, and "empty" holds only for α > 0 | PROOF-DRAFT + LEAN-CHECKED |
| 6 | Replays of `check_window3.py`, `check_gap_points.py` | **pass**, outputs identical | COMPUTED |
| 7 | The reading | **partial**: four wording fixes, none changes the number | — |

No counterexample to A*(7) + LB ≥ +0.483 on the window region was found.

## 1. The x = 3 test (pass)

**The argument, step by step (PROOF-DRAFT; I re-derived it at finite p, not only in the limit).** Fix ν, 0 < α < 1/6, and an
inner prime p with x = K/p slightly above 3. Classes are a = 1..m, m = (p − 1)/2.
- *ℓ_N.* N = αK = αxp < p/2 (since αx < 1/2), so ℓ_N(a) = 1 iff a ≤ N, else 0. Correct; in the limit this is measure 3α of
  (0, 1/2).
- *ℓ_K.* ℓ_K(a) = 6 + [a ≤ K − 3p]. So ℓ_K = 7 on the small classes a ≤ K − 3p (measure x − 3 in the limit), not "every
  class has ℓ_K = 6". This does not matter: for x < 3/(1 − α) we have K − 3p < N, so every ℓ_N = 0 class has ℓ_K = 6, and
  some ℓ_N = 1 classes have ℓ_K = 6 too. Those two facts are all the argument uses.
- *L_a ≥ 0 ⇔ Z_a ≥ b_a.* Yes: Z_a = L_a + b_a by definition. On the ℓ_N = 1 classes, Z ≥ ν/2.
- *Window.* Prop. 4.1's foreign-source inequality, between an ℓ_N = 1 class and an ℓ_N = 0 class with the same ℓ_K = 6, is
  Z_0 ≥ Z_1 − 1. So Z_0 ≥ ν/2 − 1. Since b = 0 there, Z_0 = L_0 is an integer, so Z_0 ≥ ⌈ν/2⌉ − 1 =: k. Correct.
- *The mean.* Exactly: Σ_a Z_a = (h − L₀) + (ν/2)(N − m_N), with m_N = 0. The bounds give Σ_a Z_a ≥ (ν/2)N + (m − N)k, and
  the (ν/2)N terms cancel. So a window allocation needs **h − L₀ ≥ (m − N)k**. Divided by p/2 this is
  2βx − 2L₀/p ≥ (1 − 1/p − 2αx)k. The finite-K corrections go the safe way: L₀ = 4M + 10 > 0 only makes the condition
  harder. In the README's words, the mean of Z is at most 2H_L x, and it tends to 6β + 3να as x → 3+ and K → ∞.
- *Attained.* For any ε > 0 and K large, there is a prime p ∈ (K/(3 + ε), K/3]. It is inner (p ≤ K/3, p > K/M), and x = K/p ∈
  (3, 3 + ε]. So if 6β < (1 − 6α)k strictly, then for every large K some inner prime violates the condition: the point is
  outside the window region. The README does not state this step, but it is standard.
- *Box test.* k ≥ 0, and (1 − 6α)k is non-increasing in α. So 6β₁ < (1 − 6α₁)k at the corner gives the strict inequality at
  every point of the closed box with α > 0. A box touching α = 1/6 is never flagged. The test never applies at k = 0
  (ν = 1, 2), nor at α = 0.

**Hunt for a hole (COMPUTED, `hunt_holes.py` → `hunt_holes.out`, `hunt_holes.json`; `band3.py` → `band3.out`).**
`rv_window.valid_all` is exact in x. On each x-interval with a fixed class structure, the piece measures and the target are
affine in x. I add the zeros of every feasibility condition as breakpoints, then evaluate at every breakpoint and every
sub-interval midpoint. The row total is not shortened (shift 0), which is the most generous choice. Feasibility at a single x
means: some window [w, w + 1] with w ∈ ½Z, each class having an admissible Y ≥ c in c + Z inside it, and the target between
the two attainable extremes.
- (a) **All 1352 `window(x=3)` boxes of extend.json**, at 13 520 points: the upper corner, 3 points within 10⁻⁴ of it, and 6
  random interior points. **0 are window-feasible on (3, 3.5].** Each fails on the first constant-feasibility sub-interval
  after 3. At x = 3 + 10⁻⁹, all 1352 upper corners are infeasible.
- (b) **Every saturation box of the final tiling**, ν = 1..24, at 5180 points: z₇ < 0 at all of them, the largest being
  −0.050. So no saturation verdict hides a valid point.
- (c) **The band around the line** 6β = (1 − 6α)k, ν = 3..30, at distances up to 2·10⁻³, at x = 3 + 10⁻⁹. Below the line,
  1156 points are all infeasible. Above it, 1155 points are all feasible. So on this sample the test is exactly feasibility at
  3+, as the README says.
- (d) **Finite p, no continuum.** Exact discrete window feasibility over all (p − 1)/2 classes, with Fauzan's row total
  Σ L_a = h − L₀ (M = 40, K = 320000, p = 106649, x = 3.0005). I used points 1/200 below and above the line at ν = 9, 12, 17,
  23 and 24 (α = 1/96). Below the line all 5 are infeasible; above it all 5 are feasible.
- (e) Among the 4954 window-valid points that check 4 found outside the derived region, 0 lie strictly below the line.

**Verdict: pass.** The x = 3 test is a necessary condition, and I found no box that is marked invalid wrongly.

## 2. Coverage (pass; COMPUTED, `coverage.py` → `coverage.out`, `coverage.json`)

For each ν = 1..24, the final tiling is the earlier cover (E730 even ν ≤ 22, E732 odd ν ≤ 21), with each
`La(x=3), alpha > 0` box replaced by the extend.json boxes inside it. For ν = 23 and 24 it is extend.json alone.
- **Every La box was re-examined.** Each of the 1398 La boxes (819 odd, 579 even) is re-tiled exactly by extend.json. No
  extend.json box at ν ≤ 22 lies outside a La box. In extend.json every replacement is the same box at depth 0.
- **The even ν ≤ 10 covers never use the shortcut.** cover-nu{2,4,6,8,10}.json contain no La verdict, only certified, iii
  and saturation.
- **Tiling.** For every ν, the 320 final boxes are pairwise interior-disjoint, lie in the rectangle and have total area
  exactly 1/3.
- **Statuses.** Every final box is certified (floor_lo > 0) or invalid by iii, saturation or window(x=3). There is no La,
  open, error or unresolved box.
- **Verdicts re-derived.** Every iii box fails (iii) at its lower corner. Every window box fails my own reading of the test at
  its upper corner. Saturation was checked by sampling (check 1(b)).
- **The minimum.** The smallest floor_lo over all ν = 1..24 is **+0.48273** (ν = 9, box [7/48, 1/6] × [1/4, 3/10]), which is
  the E732 derived-region box. Per-ν minima match the README tables.
- **α = 0.** The window test does not apply on the line α = 0. There E733 relies on E730's ν-free argument. I confirmed that
  in cover-nu2.json every box of the column [0, 1/48] with β₁ > 2/3 is certified (`check3.py` (c)). The validity of f at
  α = 0 itself (E730, reviewed in E731) was not re-reviewed here.

## 3. The bound outside the derived region (pass)

E730's f lower-bounds the floor wherever (ii) holds and R = xF + Q with Q ≥ −5/8. Neither step uses L_a ≥ 0. What has to be
checked is that the R of the window allocation is the R that the formulas assume.
- **Even ν, at La_check < 0 points (COMPUTED, `check3.py` → `check3.out`).** My window cost has no L ≥ 0 constraint and
  assigns its up-measure in piece order, not greedily. It equals `pkg_ab.PkgAB.R` exactly at every x tested, at 120 points
  with La_check < 0 (11 of them window-valid), 7680 x values, 0 mismatches. Also `selftest.out`: 612 random even-ν (point, x)
  pairs, 0 mismatches.
- **Why (PROOF-DRAFT).** At even ν, Fauzan's allocation (extras by decreasing ℓ_K, ties free) puts every Y in one window of
  length 1 with integer L. Given the window, the row total and L ∈ Z, the Y-distribution is unique, because the windows for
  consecutive bases tile the range of the target. So Fauzan's allocation is a window allocation. Conversely, every window
  allocation is Fauzan's with some tie order, namely extras to the ℓ_N = 1 classes first among equal ℓ_K. That is within his
  "ties may be ordered arbitrarily". The cost depends only on the Y-distribution. So E733's "at even ν the window allocation is
  Fauzan's own" is right, at La-failing points too.
- **Odd ν, at La_check < 2 points (COMPUTED, `check3.out`, `check3b.out`).** At 120 points and 7680 values of x, R_window − R_relaxed
  stays inside ±1/8, and min Q_true = +0.00000 (rounded) > −3/8. The exact maximum of |R_window − R_relaxed| near breakpoints is 0.1249995 (ν = 15,
  x = 120.000001), so the 1/8 bound is nearly attained but never exceeded (0 of about 21 000 exact values above 1/8). E732's
  argument holds without L ≥ 0: both allocations have the same mean and each has spread ≤ 1. So |∫Y_t² − ∫Y_r²| ≤ 1/8, and the
  true floor is ≥ the relaxed floor − 1/144.

## 4. Falsification (pass; COMPUTED, sampled; `falsify_membership.py` → `falsify_membership.out`, `.json`; `falsify2.py` → `falsify2.out`, `falsify2.json`)

- **The sample.** Points with (iii), z₇ ≥ 0 and window L_a ≥ 0 at every x ≥ 3 (exact in x, shift 0), drawn inside E733's
  newly certified boxes, near the x = 3 line, or uniformly. The uniform and line draws were kept only outside the derived
  region (La_check < 0 at even ν, < 2 at odd ν).
- **Membership.** Every kept point must lie only in certified boxes of the final tiling.
- **Values.** For a subset, the floor (scan.cell's floor7, minus 1/144 at odd ν) must be ≥ each containing box's floor_lo.

- **Membership at scale** (`falsify_membership.py 1500`). 35 925 draws, a third of them aimed at the band around the x = 3
  line. **4954 window-valid points outside the derived region**, at every ν from 5 to 24 (23 at ν = 5, up to 512 at ν = 11;
  none at ν ≤ 4 or ν = 6 in this run). **0 lie in a non-certified box**, and 0 lie below the x = 3 line. The lowest containing-box bound
  among them is +0.5596.
- **Values** (`falsify2.py`, on the grid α = k/240, β = m/120). 16 145 grid draws gave 1127 window-valid points outside the
  derived region, again with 0 holes. For each ν I took the 2 points in the lowest-bound boxes, plus 1 point in a box that E733
  newly certified: 54 points at ν = 3, 5, 7 to 24. **0 box bounds lie above the floor.** The smallest slack is **+0.108**, at
  ν = 5, (19/120, 2/3): box bound +0.718, floor ≥ +0.826. The smallest floor sampled is +0.738 (ν = 8, (13/80, 8/15)).
- The E733 replay (check 6) adds 36 points from E732's review: min slack +0.262.
- *Note.* `falsify.py` is the module that holds the sampler and the tiling. I stopped its own stage 2: random fine rationals
  give scan.cell periods around 10⁵, so each cell takes many minutes. Its stage 1 (244 points, 0 holes) is superseded by the
  two runs above.
- *Limits.* The membership test is exact in x but sampled in (α, β). Saturation uses pkg_ab's kink sampling (`zmin`). The
  floors are scan.cell floats. α = 0 itself is not sampled (check 2).

## 5. ν ≥ 25 (partial)

- **The Lean lemma (LEAN-CHECKED, gate PASS).** Its statement is: 25 ≤ ν, (ν − 1)/2 ≤ k, 0 < α ≤ 1/6, 2β + να − 1 < 3
  ⟹ 6β < (1 − 6α)k. It matches the README's inequality chain. The algebra is right: 12 − 3να ≤ (1 − 6α)(ν − 1)/2 ⇔
  ν ≥ 25 − 6α.
- **The README's hypothesis is false at even ν.** It says "k = ⌈ν/2⌉ − 1 ≥ (ν − 1)/2". At even ν, k = ν/2 − 1 < (ν − 1)/2
  (ν = 26: k = 12 < 12.5). So the lemma does not apply directly at even ν ≥ 26.
- **The conclusion still holds there.** Apply the lemma with ν′ = ν − 1 ≥ 25 (odd) and the same k = ν/2 − 1 = (ν′ − 1)/2.
  (iii) at ν′ follows from (iii) at ν because α > 0. The conclusion does not involve ν. Directly: one needs ν ≥ 26 − 12α. So
  "empty for ν ≥ 25" is true, but the sentence should be fixed (PROOF-DRAFT).
- **"Empty" holds only for α > 0.** At α = 0 the window region is non-empty for every ν, for example β ∈ [2/3, 2). It is
  ν-free and covered by E730's α = 0 column (check 2). The Result line handles this ("α = 0 is covered as in E730"), but the
  sentence "The window region is empty for ν ≥ 25", and the E730/E732 pointers, should say "with α > 0".
- **Numerically.** At ν = 24 the line is not excluded (k = 11 needs α ≥ 1/6), which is consistent with the 52 certified boxes
  at ν = 24.

## 6. Replays (pass; COMPUTED)

- **`check_window3.py`** (on the copy in `work/`; `replay_check_window3.out`): identical to the README. 793 flagged points,
  0 unsound; 1236 unflagged points, 0 not sharp; the 5 review points agree.
- **`check_gap_points.py`** (on the copy; `replay_check_gap_points.out`; its new `check-gap-points.json` sits in
  `work/.../E733-window-region/`): **byte-for-byte the same JSON content** as the team's (compared as parsed objects). 36
  points, 0 orphans, 0 bounds above the floor, min slack +0.26158689734098006. 165 s on 6 processes.

## 7. The reading (partial)

1. "The window region is empty for ν ≥ 25. With k = ⌈ν/2⌉ − 1 ≥ (ν − 1)/2 …" — false at even ν, and "empty" should be
   "empty for α > 0" (check 5). The same "empty for ν ≥ 25" appears in the E730 pointer ("What this does not show") and the E732
   pointer ("What is still open").
2. **The x = 3 section gives the limit only.** "every class has ℓ_K = 6" and "the mean of Z is 6β + 3να" are limit
   statements. The write-up should say:
   - at finite K the mean is h − L₀ over m, which is below 2H_L x, so the necessary condition only gets stronger;
   - the ℓ_K = 7 classes are all ℓ_N = 1 classes and play no role;
   - primes with x ∈ (3, 3 + ε] exist for large K.

   None of this changes the test (check 1).
3. **"3000 random (ν ≤ 30, α, β) satisfying (iii)".** The script draws 3000 and keeps the 2029 that satisfy (iii) (793 + 1236).
4. **The pointers say "certified".** E730's pointer says E733 "has since certified the whole window region", and E732's says it
   "is now certified". Both should keep E733's own label, COMPUTED given PROOF-DRAFT steps, and say "not yet reviewed" or point
   here, so the result does not read as more than that.
5. **"with its allocation taken as far as his own validity proof allows"** (Result, in words). This is fair within Fauzan's
   weight scheme. E732's review found the window condition necessary there. But the weight scheme itself (rows (4.5), weights
   (4.6), L₀ = 4M + 10) is a choice. Suggested: "as far as his proof of Prop. 4.1 allows with his row basis and weights".

Accurate as written:
- the per-ν table (it matches extend.log and my coverage audit);
- "All 2038 boxes resolved at the first level" (1398 La boxes + 640);
- "Every newly certified box is at least +0.68" (min +0.6847, ν = 11);
- "The minimum is still … ν = 9, +0.4827";
- the even/odd applicability sentence (check 3).

## Files (all in this folder)

`REVIEW.md` (this file); `rv_window.py` (my window feasibility, cost and exact all-x validity); `selftest.py` → `selftest.out`;
`coverage.py` → `coverage.out`, `coverage.json`; `hunt_holes.py` → `hunt_holes.out`, `hunt_holes.json`; `band3.py` →
`band3.out`; `check3.py` → `check3.out`, `check3.json`; `check3b.py` → `check3b.out`; `falsify.py` (sampler module; its stage 2 was stopped, no output kept); `falsify2.py` → `falsify2.out`, `falsify2.json`; `falsify_membership.py` →
`falsify_membership.out`, `falsify_membership.json`; `replay_check_window3.out`, `replay_check_gap_points.out`; `work/` (the
replay copies: `work/evidence/W-presentation-draft/research-20261115/E733-window-region/` with copies of `check_window3.py`,
`check_gap_points.py`, `extend.py`, `extend.json`, the original `check-gap-points.ORIG.json` and the replayed
`check-gap-points.json`; the other team folders are symlinks, read-only).
Reproduce from this folder with `python3 -B <script>` (each at most 6 processes).
