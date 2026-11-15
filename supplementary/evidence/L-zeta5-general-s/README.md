# L-zeta5-general-s: can the Lean arithmetic core of zeta(5) be made symbolic in s? (task [108/L7 scout])

formalizer (L7 scout): Claude Fable 5.2 subagent (Claude Code, launched by the integrator on `[team machine]` for [team member]). **started 12:24** PT, Sat Nov 14 2026. EVENT WORK. The literal map `MAP.md` was written by a fork of this agent (12:29-12:39). Wrapped up early at the coordinator's request (hand-over to another session); end time on the last line.

**Current status: the 120 declarations listed in `Zeta5S/Axioms.lean` are LEAN-CHECKED.** Local Codex lane L driver: gate120/120PASS at13:55 PT, 24.688 seconds including rebuilds (`log/LEAN_CHECK.md`), standard axioms only. This covers the full general raw arithmetic chain, the approved finite local-valuation and normalization propositions, positive normalizer, and concrete original-allocation anchors. Source comparison:67 copied definitions/statements and232 verbatim blocks match the pinned source,0 mismatches. **No human has compared any statement with a claim.** Evidence: E300 `../L-stage1-driver/`, E302 `../L-outer-stage3/`, E303 `../L-assembly-statement/`, E304 `../L-assembly-anchors/`, E305 `../L-normalization/`. The original scout author is Claude Fable5.2; the four outer modules, assembly, normalization and anchors are Codex driver work. Nothing here is called new. Original source: mo271/Zeta5@be1c0d82 (Moritz Firsching; PR#1 by Paul-Lez), Apache-2.0, prior work; see NOTICE and LICENSE.

**Stage4 completed, Sat13:55 PT:** `AssemblyTarget.local_valuation_statement` and `normalization_statement` prove exactly the approved finite propositions (definitions unchanged; saved comparison). The result uses upstream's **raw rank loss**, arbitrary supplied allocations with validity flags/fallback, explicit finite shape conditions, and prime support max(7,s,2h). It does **not** prove E13's sharper min(rank,zero-count) exponent, a limiting prime sum, a real bound, or analytic identification/irrationality of zeta(s). The normalizer is positive. R2 kernel anchors: at s5,nu6,K40,N3 the exponents p2/13/17 equal upstream(-1665,-67,-103); s7 inner13/outer17 give-138/-128, below stored exact valuations-116/-126. Independent bounds recalculated exactly; determinant values read back, not recomputed. A cross-lane review is requested.

**Earlier driver continuation, Sat13:20–13:27 PT:** all27 Arith modules have counterparts and build. E302 formalized the raw outer bound and moment/rank/boundary bridge, before stage4 was approved. The remaining numbered sections preserve the scout's earlier13:09 hand-over and then-current estimates; all its “not done” outer/finite-normalization lists are superseded by the current status above. Its analytic and sharper-exponent limitations remain.

## 0. Result in five lines

- **23 of the 27 files of `Apery/Arith/` are in the probe and build**: 286 of its 352 declarations (211 copied verbatim, 67 rewritten for symbolic parameters, 8 moved to `Monomial.lean`/`Pullback.lean` in general form), 4009 of 5077 upstream lines. Wall time for this: 12:28 to 13:05 (37 minutes), one agent, 23 build runs, 7 of them with errors.
- General statements now LEAN-CHECKED include the key step `tauXs_direct` (loss `s - 1`, primes `p ≥ s`), the paper's distribution identity `tauS_distribution`, the pullback identity for every odd `s ≥ 3`, and **two of the three exports of `Arith/`** with symbolic `(s, ν, K, N, h)`: `inner_bound_capS` and `small_prime_boundS`; plus the outer framework `outer_frameS`.
- **Not done**: the last four outer files (`OuterEntry`, `OuterBasis`, `OuterEntries`, `OuterEntryMain`: 1068 lines, 66 declarations, among them the third export `outer_bound`), and the assembly `GV_F_Lp` in `Apery/Norm.lean` (outside `Arith/`). No file holds a `sorry`; nothing is half-done in the build.
- 45 upstream definitions and statements at `s = 5` are re-proved from the general ones in `Zeta5S/AtFive.lean`; a script checks that their text equals upstream's (`tools/check_faithful.py`: 45 SAME, 0 DIFFER; 211 verbatim blocks, 0 mismatches).
- Zeta5 does **not** use the distribution identity: its header says the direct bound "replaces the p-adic distribution formula of the paper (Lemmas 3.1-3.2)". What it uses is `tau_bound` ((3.9), binomial basis). Both are in the probe for general `s`.

## 1. Step 1: measurements (all from `log/`)

| Item | Value |
|---|---|
| Reference clone | `~/mathathon-cache/108/zeta5`, commit `be1c0d82070da93c343f93bffd495b8ebc323645` (Wed Sep 23 2026, "Update reference format for preprint citation"); read-only, only `.lake/` was created in it |
| Toolchain | `leanprover/lean4:v4.33.1` |
| `require`s | `mathlib` (scope leanprover-community) `rev = "v4.33.1"`, manifest rev `0df444a360ea...`: **the same Mathlib commit as our repo's manifest**. `PrimeNumberTheoremAnd` from the fork `github.com/mo271/PrimeNumberTheoremAnd` at `04d81b2a68ea...` (yes, a PNT fork; it pulls `PrimeCert`, `leancert`, `checkdecls`, `LeanArchitect`). **`Apery/Arith` does not need it** (next rows) |
| Repository size | 251 `.lean` files (the brief said 253), 32 MB |
| `Apery/Arith/` | 27 files, 5077 lines, 234 498 bytes; 352 declarations (295 lemmas/theorems, 57 defs; count by the fork's `parse.py`, in `MAP.md`) |
| Import closure of `Arith/` | Mathlib plus 6 files outside `Arith/`, 25 290 bytes: `Construction` (73 lines), `Degree` (180), `PartialFractions` (118), `Legendre` (63), `Normalization` (113), `Constants` (42). The last three come only through `import Apery.Legendre` in `SmallPrimeF.lean`, which is unused: the probe's copy of `SmallPrimeF` builds without it. So the real closure is `Construction`, `Degree`, `PartialFractions` (371 lines). Top modules: `InnerAlloc`, `OuterEntryMain`, `SmallPrimeF` (the three that `Apery/Norm.lean` imports) |
| `lake exe cache get` in the clone | 72.6 s wall (`log/01`): clones all 14 packages, PNT fork included; the Mathlib cache was already on this machine ("No files to download"), so this is clone plus decompression only |
| Build of the `Arith` closure, upstream lakefile | `lake build Apery.Arith.OuterEntryMain Apery.Arith.InnerAlloc Apery.Arith.SmallPrimeF` in the clone: **82.2 s wall**, 33 modules (`log/03`) |
| Same 33 files in a Mathlib-only project | `~/mathathon-cache/108/arith-build` (copies of the 33 files, upstream `leanOptions`, no PNT): **99.0 s wall**, 107 s user (`log/02`; it ran while the cache above was decompressing). First attempt failed on my own lakefile mistake (`roots` without globs, `log/02a`) |
| Machine | Apple silicon, 18 cores, 64 GB; other agents were running |

## 2. Step 2: the literal map

`MAP.md` (507 lines, by the fork; readings of the source are CITED lines, the general-(s, ν) interpretations are HEURISTIC). Its counts: **97 of 352 declarations need a changed statement** (60 with an explicit s or ν literal, 37 that only name an s-specific definition), **0 need only a changed proof**, 255 unchanged; 49 statements hard-code the shape (40n, 3n, 37n), 23 of them otherwise unchanged. Where the objects are defined: `μmono`, `μpoly`, `H5`, `poleValue`, `μX`, `G`, `Δ`, `S`, `F` in `Apery/Construction.lean`, none with an s or ν parameter; `G n` fixes `Fin (37 * n)`, `μX (40 * n)`, `D (3 * n) ^ 6`. The assembled statement is `GV_F_Lp` in `Apery/Norm.lean:146` (outside `Arith/`).

What the probe's builds confirm or correct in the map (measured):
- "0 proof-only" holds for the 23 files done: every changed proof belongs to a changed statement.
- For the 23 files done the map lists 75 declarations whose statement must change (97 minus 22 in `OuterEntries` and `OuterEntryMain`). The generator replaced 67 in place and moved 8 (7 of `Pullback`, 1 of `PoleVal`) to general versions elsewhere: 75, and the per-file numbers agree file by file (`log/09_gen_copies.log` against the map's table). I found no wrong reading in the files I generalised.
- `6` is `s + 1` in `crude_tauX` and `small_prime_bound` and `ν` elsewhere; `24` is `(s-1)!`; `5 ≤ p` is `s ≤ p` (used only for `p ∤ (s-1)!`): all three confirmed by the general proofs.
- The map's warning that `omega` would fail once `ν N` is symbolic did not come true in the files done: `omega` treats `ν * N` as an atom, and it sufficed everywhere once `Nat.add_sub_cancel` was added to one `simp only`.
- The map's warning about number-specific proofs did come true once: `VG_μmono_int` (case split `j = 1, 2, 3`) needed a new argument for general s.

## 3. Step 3: what is in the probe

### Organisation

- `lakefile.toml`, `lean-toolchain` (`leanprover/lean4:v4.33.1`), `lake-manifest.json` (our repo's manifest with the package name changed): **the probe depends only on Mathlib v4.33.1.** It contains adapted copies, so it builds without the 30 MB repository.
- `tools/gen_copies.py <clone>`: **generates** 24 files of `Zeta5S/` from the clone. For each upstream file it copies every declaration verbatim (namespace `Apery` renamed `AperyS`, imports renamed), writes before each one `-- adapted from mo271/Zeta5@be1c0d82 <file>:<lines> (Firsching; Paul-Lez), Apache-2.0 [verbatim | GENERALIZED ...]`, and replaces the declarations listed in its `OVERRIDES` table (hand-written general versions) or rewritten by its `TRANSFORMS` (text substitutions: `_weights` for `InnerWeights`/`InnerAlloc`, `_crude` for `crude_tauX`, `_outer` for `OuterFrame`). **Edit the script, not the generated files.** `Zeta5S/Base.lean` holds the 9 declarations needed from `Construction`, `Degree`, `PartialFractions`.
- Hand-written: `Zeta5S/Monomial.lean` (linearity of `τ_s`, the monomial formula), `Zeta5S/Distribution.lean` (the distribution identity; no upstream counterpart), `Zeta5S/AtFive.lean` (namespace `AperyS.Upstream`: faithful copies of the upstream `s = 5` definitions and the upstream statements re-proved from the general ones), `Zeta5S/Axioms.lean` (82 `#print axioms`), `Zeta5S.lean` (root).
- `tools/check_faithful.py <clone>`: compares the text of the 45 copies in `AtFive.lean` with upstream (definitions whole; theorems from the keyword to `:= by`, whitespace collapsed), and every `[verbatim]` block of the generated files with its source lines.
- `STATEMENTS.lean.txt`: the general definitions and main theorems, extracted from the files for reading.
- `v435/`: see section 5. `log/`: raw logs.

### Rebuild

```
export PATH="$HOME/.elan/bin:$PATH"
cd problems/108-zeta-odd-autopsy/evidence/L-zeta5-general-s
# packages: on [team machine] `.lake/packages` is a symlink to the repo root's `.lake/packages` (same manifest).
# On a fresh checkout instead:  lake exe cache get
python3 tools/gen_copies.py ~/mathathon-cache/108/zeta5      # regenerates Zeta5S/*.lean (optional)
lake build                                                   # 59 s wall after a clean (log/08), 8734 jobs
lake env lean Zeta5S/Axioms.lean                             # 82 lines, log/05_axioms.log
python3 tools/check_faithful.py ~/mathathon-cache/108/zeta5  # log/06_check_faithful.log
```
Last clean build: Sat 13:05:14-13:06:13 PT, `Build completed successfully (8734 jobs)`, 0 `sorry` warnings; source scan for `sorry`, `native_decide`, `bv_decide`, `axiom`: no hit.

### The general declarations (all in namespace `AperyS`; exact text in `STATEMENTS.lean.txt`)

Axioms of each: `[propext, Classical.choice, Quot.sound]` (`log/05_axioms.log`; one line, `Upstream.xroots_eq_xrootsS`, shows the subset `[propext, Quot.sound]`).

| General declaration | Says | Upstream original (s = 5) | Differences to know |
|---|---|---|---|
| `tauS s P := Lb (derivative^[s-2] P) / (s-1)!` | `τ_s(P) = L(P^(s-2))/(s-1)!`, `L(x^k) = B_k` (Mathlib `bernoulli`, `B_1 = -1/2`) | `tau` (`TauBound.lean:18`) | natural subtraction: meaningful for `s ≥ 2`, which every theorem assumes |
| `tauS_bound (hs : 2 ≤ s)` | `v_p(τ_s(P)) ≥ β - (s-1) log_p(d+1) - v_p((s-1)!)` if `deg P ≤ d` and `v_p(P(m)) ≥ β` for `m ≤ d` | `tau_bound` (3.9) | the loss is `(s-2)` derivatives plus 1 for `L`; new helper `BinRep.iterate_derivative` |
| `VG_Hs`, `Hs s j` | `v_p(H_m^(s)) ≥ -s` for `m < p²` | `VG_H5`, `H5` | none |
| **`tauXs_direct (hs : 2 ≤ s) (hps : s ≤ p)`** | **`GV p (tauXs s (numOf κ Z) Pl) (β - (s - 1))`**: the direct bound with loss `s - 1` | **`tauX_direct (hp5 : 5 ≤ p)`**, `β - 4` | `5 ≤ p` becomes `s ≤ p`; holds for every `s ≥ 2`, parity not used here |
| `tauS_X_pow`, `tauS_X_pow_odd (hs : 2 ≤ s)`, `tauS_pull_poly` | `τ_s((-1)^e x^(2e+s)) = μmonoS s e = (-1)^e B_(2e+2) (2e+s)! / ((2e+2)! (s-1)!)`; `τ_s(x^s Q(-x²)) = μpolyS s Q` | `tau_X_pow`, `tau_X_pow_odd`, `tau_pull_poly`, `μmono` | `μmonoS` is written with factorials (the brief's monomial formula); upstream writes `(2e+3)(2e+4)(2e+5)/24`; equality at `s = 5` is `Upstream.μmono_eq_μmonoS` |
| **`Lb_distribution`, `tauS_distribution (hs : 2 ≤ s)`** | `∑_(a<n) L(P(a + n x)) = n L(P)`; **`∑_(a<n) τ_s(P(a + n x)) = n^(s-1) τ_s(P)`** for every `n : ℕ` | **none: not in Zeta5** | this is the identity of the brief (derivation.md §1 as quoted there; I did not open derivation.md). Wider than the brief: any natural `n`, any `s ≥ 2`. Proof by telescoping from upstream's `Lb_shift`, `newton`, `bin_comp_add_one`; it follows no source |
| `poleValueS s j`, `μXS s K P`, **`μXS_eq_tauXs (hodd : Odd s) (hs : 3 ≤ s)`** | pullback identity `μ_X(P/D_K) = τ_X((-1)^K x^s P(-x²)/∏(x - r))` | `poleValue`, `μX`, `μX_eq_tauX` | **`poleValueS s j = j^(s-1)(X - H_j^(s)) - 1/(s-1) + 1/(2j)` is my reading of what the constant `-1/4` becomes; it is the choice that makes the identity true. That this is the functional attached to ζ(s) is an analytic statement not touched here.** First place where odd `s` is needed. New: `qS`, `X_pow_odd_eq`, `tauS_qS` (upstream's cubic `-X³ - aX` becomes a sum of `(s-1)/2` monomials) |
| `μXS_tpol_bound (hodd) (hs3) (hps)` | entry bound, loss `s - 1` | `μX_tpol_bound` | none beyond the hypotheses |
| `VG_μmonoS`, `VG_μmonoS_int (he : 2 * e + 2 < (s - 1) * (p - 1))` | `v_p(μ_s(t^e)) ≥ -1`; integral below the threshold | `VG_μmono`, `VG_μmono_int (he : e + 3 < 2 * p)` | **proof re-thought, not parametrised**: `p` divides the factor `2e+2+j = jp` of the falling factorial |
| `GS`, `ΔS s ν K N h`, `det_basis_changeS`, **`class_frameS`** | Hankel matrix and determinant with symbolic `(s, ν, K, N, h)`; `v_p^G(Δ) ≥ 2 ∑ w` | `G n`, `Δ n`, `det_basis_change`, `class_frame` | `18 * n` is `ν * N`; `+ 4` is `s - 1`; entry indices renamed `x y` |
| `BseS`, `classCount_eqS`, `winner_ACIS`, `wcap_ACIS`, `inner_boundS`, **`inner_bound_capS`**, `sum_wcap_allocKS` | the inner range; **first export of `Arith/`** | `Bse`, ..., `inner_bound_cap`, `sum_wcap_allocK` | in the weight lemmas the loss is a rational parameter `ℓ`, instantiated at `s - 1` |
| `GV_poleValueS_lt/_sq/_mul`, `VG_pairS`, `VG_Hs_pm1`, **`GV_poleValueS_congr (hodd)`** | pole values: `≥ 0`, `≥ -s`, `≥ -1`; congruence `poleValue(p-c) ≡ poleValue(c)` | `PoleVal.lean` | the first three need `¬ p ∣ s - 1` (what `3 ≤ p` gave for `1/4`); the congruence needs odd `s` (`Odd.neg_pow`, `Even.neg_pow` replace `ring` in `ZMod p`) |
| `VG_Hs_log`, `crude_tauXs`, `SS`, `FS`, **`small_prime_boundS`** | `v_p^G(F) ≥ -((s+1) h log_p(d+1) + h v_p((s-1)!))`, `d = s + 2νN + 4(h-1)`; **second export** | `VG_H5_log`, `crude_tauX`, `S`, `F`, `small_prime_bound` | needs the shape hypothesis `2K ≤ s + 2νN + 4(h-1)` (upstream proves it by `omega` for 40n, 3n, 37n); upstream rounds `d + 1 = 184n + 2` up to `200 * n`, the general statement keeps `d + 1` |
| `μGeS σ T`, **`outer_frameS`** | the outer framework with an abstract moment threshold `T`: `v_p^G(Δ) ≥ 2 ∑ w - (h - ((T + K - νN) - (h - 1)))` | `μGe`, `outer_frame` (`T = 2p - 3`, rank term `2p + 22n - 3`) | zeta index is called `σ` in this file (upstream uses `s t` for rows). **Needs `1 ≤ T`: `omega` produced a counterexample at `T = 0` on the first build** |

General statements that have **no** `s = 5` comparison theorem yet (they build; nobody proved they specialise to the upstream text): `VG_μmonoS` aside, these are `winner_ACIS`, `wcap_ACIS`, `inner_boundS`, `sum_wcap_allocKS`, `tmin_allocK_geS/_leS`, `classCount_eqS`, `count_DNS`, `GV_poleValueS_lt/_sq/_mul`, `VG_pairS`, `VG_Hs_pm1`, `Hs_split`, `VG_Hs_log`, `SS_eq_qlead`, the `μGeS_*` lemmas and `μXS_add/_C_mul/_sum`.

### The `s = 5` comparison (`Zeta5S/AtFive.lean`, namespace `AperyS.Upstream`)

Faithful copies of 21 upstream definitions (`μmono`, `μpoly`, `H5`, `tau`, `tauX`, `poleValue`, `μX`, `pull`, `xroots`, `G`, `Δ`, `entryRoots`, `classCount`, `Bse`, `topw`, `tmin`, `wraw`, `wcap`, `S`, `F`, `μGe`), 19 of them proved equal to the general one at `(s, ν, K, N, h) = (5, 6, 40n, 3n, 37n)` (not `topw` and `wraw`, which enter only through `tmin` and `wcap`), and 24 upstream theorems with their statements copied, proved from the general theorems: `tau_bound`, `VG_H5`, `tauX_direct`, `tau_X_pow`, `tau_X_pow_odd`, `tau_pull_poly`, `tau_cubic`, `polyPart_pull`, `resP_pull`, `H5_succ_eq`, `μX_eq_tauX`, `pull_tpol`, `cnt_xroots`, `μX_tpol_bound`, `VG_inv24`, `VG_μmono`, `VG_μmono_int`, `det_basis_change`, `class_frame`, `inner_bound_cap`, `GV_poleValue_congr`, `crude_tauX`, `small_prime_bound`, `outer_frame`. Limits of this check: it is a text comparison of copies, in another namespace, inside the probe; the probe was not compiled against upstream's own files; docstrings and comment lines are not compared.

### What is left with `sorry`

Nothing. No declaration in the probe uses `sorry`. What is missing is absent, not stubbed (section 0).

## 4. Step 4: estimate, and what it rests on

Measured: 12:28-13:05, 37 minutes, one agent, for 23 files (4009 upstream lines, 67 rewritten declarations, 24 comparison theorems and 19 definition equalities). Per stage (clock readings taken in the session): key chain behind `tauX_direct` 6 min (3 builds); distribution identity 2 min; pullback 6 min (4 builds); `TEntry` 1 min; `MomentVal` 2 min; `BasisChange`+`ClassFrame` 3 min; `ClassCount`+`InnerWeights`+`InnerAlloc` 3 min; `PoleVal` 3 min; small primes 4 min; `OuterFrame` 2 min. Most upstream proofs survived the substitution unchanged; repairs were of four kinds: a missing hypothesis (`1 ≤ T`, `¬ p ∣ s - 1`, `2K ≤ d`), `linarith` steps that became products (`mul_le_mul_of_nonneg_left` added), numeral goals that `rw` used to close by `rfl`, and one proof that had to be re-thought. **This rate is from the easier three quarters; do not extrapolate it linearly.**

| Stage | State | Estimate (agent-hours) | Rests on |
|---|---|---|---|
| **(A) inner part** (`PoleVal`, `DirectBound`, `InnerWeights`, `InnerAlloc`, `ClassCount`, `SmallPrime*`) with symbolic (s, ν) | **done in the probe** (LEAN-CHECKED) | 0.3 to add the missing `s = 5` comparison theorems; plus the human statement comparison, which is not agent time | measured |
| **(B) outer part** (`OuterEntry`, `OuterBasis`, `OuterEntries`, `OuterEntryMain`; `OuterFrame`, `LowRank`, `MomentVal` are done) | not started; I only printed the statements | 1 to 3 | extrapolation, not measurement. 1068 lines, 66 declarations, 26 with the shape in the statement. These are the least mechanical files: the weights `wO`, `ellC`, `delC` must be re-defined for (s, ν); `sum_LoC` needs `h = K - N`; `nbC_zero_le` and `pole_case_zero` use `interval_cases` under `40n < 3p`, `3n < p`, `7 ≤ p`. **Where the paper's hypotheses `α < 1/6` and `1 + (ν-2)α ≤ (s-1)/2` would enter I did not determine**: in Zeta5 the outer statements carry prime-range hypotheses (`K < 3p`, `N < p`, `2K < p²`), not α; the α conditions would show up either as extra hypotheses the kernel forces (as with `1 ≤ T`) or only later, in the sums of `Apery/Growth/` |
| **(C) assembled valuation statement** (`GV_F_Lp`, `Apery/Norm.lean`, 293 lines, 29 declarations, plus `Legendre`/`Normalization` for `v_p(S)`) | not started, not read (only the fork's map of it) | 2 to 5, low confidence | `Norm.lean` hard-codes the water-filling window (`kloI = -2(K/p) - 6`, `ktopI = 8(K/p) + 20`, `L0I = 3(K/p) + 6`), `Mcut = 400`, `Lsmall`, `betaI`. A general (s, ν, K, N) version needs a general closed form for these, which is the content of E13 itself, not a parametrisation |
| **v4.35.0** | 10 modules built unchanged (section 5) | unknown for the rest; untested | one partial run |

- **Independent enough for separate agents**: (B) the three outer files, one agent (they are a chain); (C-prep) reading `Norm.lean` and stating the general `Lp`, one agent, can start now from the three general exports; the missing comparison theorems, one agent; the human statement comparison in parallel with all of them.
- **Main risk**: the kernel certifies that each general statement is true, not that it is the right generalisation. Three choices here were mine and are unreviewed: `poleValueS` (the constant `-1/(s-1)`), the abstract threshold `T` in `outer_frameS`, and the shape hypothesis in `small_prime_boundS`. The second risk is (C): if the general exponent of E13 is wrong, no amount of repair makes `GV_F_Lp` build, and the failure will appear late.
- **Cloud worker with Lean v4.33.1 at `/opt/lean/bin`, Mathlib v4.33.1 at `/opt/mathlib`, no elan**: the probe needs nothing else (Mathlib only, same commit `0df444a3`). **Not tested.** Two ways that should work: change the `[[require]]` of `lakefile.toml` to `path = "/opt/mathlib"` and run `/opt/lean/bin/lake build`; or compile the 28 files in import order with `lean` and `LEAN_PATH` pointing at Mathlib's and its dependencies' `.lake/build/lib/lean`. Compile cost is small: 59 s wall, 78 s user here.

## 5. v4.35.0 (addendum from the coordinator, later cancelled)

`v435/` has `lean-toolchain` v4.35.0, the Mathlib v4.35.0 lakefile and manifest of `../L-v435-trial/`, and `Zeta5S`, `Zeta5S.lean` as relative symlinks to the probe's sources. One run, Sat 12:37:52-12:40:14 (`log/07_v435_build.log`): `lake exe cache get` 59.8 s, `lake build` 82.5 s, exit 0. **At that time the probe had 10 modules** (`Val`, `IntPoly`, `BinomBasis`, `TauBound`, `PoleFun`, `Monomial`, `DirectBound`, `Distribution`, `DirectPoly`, the first `AtFive`): **they built on v4.35.0 with no source change.** The 18 modules added afterwards were not built on v4.35.0 (the coordinator cancelled the addendum before I re-ran it), so nothing is known about them; no Mathlib rename was hit in the part that ran. `v435/.lake` is 7.3 GB (gitignored).

## 6. Next three steps for whoever continues

1. **Outer files.** In `tools/gen_copies.py` add `OuterEntry` (expected verbatim), then `OuterBasis`, `OuterEntries`, `OuterEntryMain` to `FILES`, with a transform like `_outer` (section variables `(hm) (n)` become `(hm) (N K)` with `hNK : N ≤ K`; `37 * n` becomes `K - N`; `6` becomes `ν`; `poleValue`, `μX`, `μGe p` become `poleValueS σ`, `μXS σ K`, `μGeS σ T`). Start from the definitions `wO`, `ellC`, `delC` (`OuterEntryMain.lean`), which I did not read. Target: `outer_boundS`, then its `s = 5` comparison with `outer_bound`.
2. **Human statement comparison** of the three unreviewed choices (`poleValueS`, `T`, the shape hypothesis) and of `tauXs_direct`, `tauS_distribution`, `inner_bound_capS`, `small_prime_boundS` against E13 (`evidence/criterion5/derivation.md`), using `STATEMENTS.lean.txt`. Then, and only then, run the gate (`scripts/lean_check.py --root <this folder> --decl AperyS.<name>`), which I did not run.
3. **Decide (C) before coding it**: write the general `Lp` (the exponent of `GV_F_Lp`) on paper from `Apery/Norm.lean:27-82` and `evidence/criterion5/derivation.md`, and check it numerically at (5, 6) against upstream's `Lp` and at one other (s, ν), before any Lean. If the team's target is v4.35.0, first run `cd v435 && lake build` to see whether the 18 newer modules port unchanged.

## Files

`README.md`, `MAP.md` (fork), `STATEMENTS.lean.txt`, `NOTICE`, `LICENSE.Zeta5-Apache-2.0`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `Zeta5S.lean`, `Zeta5S/` (28 files), `tools/gen_copies.py`, `tools/check_faithful.py`, `v435/` (lakefile, toolchain, manifest, two symlinks), `log/` (01 cache get, 02/02a/03 Arith builds, 04 the 23 probe build runs, 05 axioms, 06 faithfulness, 07 v4.35.0, 08 clean build, 09 generator counts). Outside the repo: `~/mathathon-cache/108/zeta5` (clone, with `.lake`, 7.5 GB) and `~/mathathon-cache/108/arith-build` (Mathlib-only build of the 33 upstream files). No shared log, board, lane file or other evidence folder was edited; no git command was run on our repo. The `log/AI_USE.md`, `log/SOURCES.md` rows and the board `DONE` line are for the driver to write.

**ended 13:09** PT, Sat Nov 14 2026 (45 minutes of the 90-minute cap; stopped at the coordinator's request).
