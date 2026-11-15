# Statement comparison: the finite step in s (E309; report D18, D19)

Statement comparison by Claude Fable 5.2 (subagent of the integrator); author of the Lean: Codex (GPT family); Sat Nov 14, 21:58 PT. Statements only: no proof was read, nothing was built, not checked by a human.

Labels (AGENTS §2). The verdicts below are a PROOF-DRAFT semantic comparison. The hand recomputations in §0.3 are COMPUTED (by hand, in this file; no script). The printed types are quoted from the gate report `evidence/L-merge/project/log/LEAN_CHECK.md` (run 2026-11-14 21:12, Lean and Mathlib v4.35.0, overall PASS, 37 declarations; the five below are its rows 22 to 26, each with axioms `propext, Classical.choice, Quot.sound`). Source: `evidence/L-merge/project/Zeta5S/FiniteStep.lean` (header l. 5: "L10/E309 finite-prime s-step, Codex lane L"). Paths below are relative to `evidence/L-merge/project/`. Report lines refer to `report/report.tex` as it stood at 21:55 (2179 lines).

## 0. Definitions, unfolded to Mathlib

### 0.1 Text of the definitions

| Name | File, line | Body |
|---|---|---|
| `Allocations` | `Zeta5S/AssemblyData.lean` 24 | `abbrev Allocations := (p : ℕ) → Fin (p / 2 + 1) → ℕ` |
| `degreeBound` | same, 26 | `s + 2 * (ν * N) + 4 * ((K - N) - 1)` (ℕ, truncated subtraction) |
| `Lsmall` | same, 28-30 | `-(((s + 1 : ℕ) : ℤ) * (K - N : ℕ) * Nat.log p (degreeBound s ν K N + 1) + (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℤ))` |
| `vSK` | same, 32 | `padicValRat p (SS ν K N (K - N))` (ℤ) |
| `InnerOK` | same, 34-40 | `∃ hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2, s ≤ p ∧ Sep p (PlK K) ∧ K < p ^ 2 ∧ s + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2 ∧ ∑ c, L p c = K - N ∧ tminS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) ≤ 2 * (L p 0 : ℚ) + (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2` |
| `WI` | same, 42-46 | `if hm1 : 1 ≤ p / 2 then ∑ x, wcapS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) x else 0` (ℚ; `x` ranges over `Σ a : Fin (p/2+1), Fin (L p a)`) |
| `OuterOK` | same, 48-49 | `2 * (p / 2) + 1 = p ∧ s ≤ p ∧ 7 ≤ p ∧ K < 3 * p ∧ 2 * K < p ^ 2 ∧ N < p` |
| `Lp` | same, 61-68 | `if p * M ≤ K then Lsmall s ν K N p else if 3 * p ≤ K then (if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋ else Lsmall s ν K N p) else if OuterOK s K N p then vSK ν K N p + ⌊WO s ν K N p⌋ else Lsmall s ν K N p` (ℤ; classical `if`) |
| `LpSharp` | `Zeta5S/SharpAssembly.lean` 15-22 | the same four branches with `WOsharp` for `WO` in the outer branch only. **Not mentioned by any of the five statements.** |
| `SS` | `Zeta5S/SmallPrimeF.lean` 212-214 | `(K.factorial : ℚ) ^ (2 * h) * 4 ^ (h - 1) / ((N.factorial : ℚ) ^ (2 * ν * h) * ∏ i ∈ Icc 1 (h - 1), ((2 * i).factorial : ℚ) ^ 2)` |
| `SX` | `Zeta5S/ClassCount.lean` 99-101 | `((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = c).card + ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = -c).card` |
| `BseS` | same, 115-117 | `(if a = 0 then (s : ℚ) else 0) + (ν : ℚ) * (SX p N ((a : ℤ) : ZMod p) : ℚ) - SX p K ((a : ℤ) : ZMod p)` |
| `topwS` | `Zeta5S/InnerWeights.lean` 25-26 | `L a + (b a - ℓ) / 2` |
| `tminS` | same, 30-31 | `(Finset.univ.erase (0 : Fin (m + 1))).inf' _ (topwS ℓ L b)`: the minimum of `topwS` over the classes `a ≠ 0` |
| `wrawS` | same, 133-134 | `if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - ℓ) / 2 else (s.2 : ℚ) + (b s.1 - ℓ) / 2` |
| `wcapS` | same, 138-140 | `min (wrawS ℓ L b s) (tminS ℓ hm L b)` |
| `Sep` | `Zeta5S/DirectBound.lean` 152-153 | `∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬ (p : ℤ) ^ 2 ∣ r - s` |
| `PlK` | `Zeta5S/Pullback.lean` 86-87 | `(Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))` |
| `switchAllocation` | `Zeta5S/FiniteStep.lean` 170 | `fun _ c => ([2, 5, 4, 4, 7, 7, 8] : List ℕ).getD c.val 0` |
| `upstreamAlloc` (not in the five statements; used in §2 d) | `Zeta5S/AssemblyAnchors.lean` 14 | `fun p => Upstream.allocI 1 p (p / 2)` |

Everything else is Mathlib: `Finset.sum`, `Finset.inf'`, `min`, `Int.floor`, `Nat.log`, `padicValNat`, `padicValRat`, `ZMod`, `List.getD`, casts ℕ → ℤ → ℚ. Not unfolded: `WO`, `WOsharp`, `LoC`, `wO` (the outer branch, never selected in the five statements: see §2 and §3).

### 0.2 In mathematical notation

For a natural `p ≥ 2` put `m = ⌊p/2⌋`; classes are `a = 0, …, m`. `S_X(a) = #{1≤j≤X : j≡a} + #{1≤j≤X : j≡−a (mod p)}`; for `a = 0` every multiple of `p` is counted twice (and, for even `p`, so is the class `a = p/2`). `b_s(a) = s·[a=0] + ν S_N(a) − S_K(a)`, `ℓ = s − 1` computed in ℚ (no truncation at `s = 0`).

- raw weight of row `i` of class `a ≠ 0`: `i + (ν S_N(a) − S_K(a) − (s−1))/2`: this is the report's (eq:ordinary) with `ℓ_A(a) = S_A(a)`;
- raw weight of row `i` of class `0`: `2i + (b_s(0) − (s−1))/2 = 2i + ν⌊N/p⌋ − ⌊K/p⌋ + 1/2`, which does not depend on `s`;
- cap: `t_s = min_{a≠0} ( L_a + (b_s(a) − (s−1))/2 )`; capped weight `= min(raw, t_s)`;
- `W_I(s) = Σ_{a} Σ_{i<L_a} capped weight` (0 if `p < 2`);
- zero-class test of `InnerOK`: `t_s ≤ 2 L_0 + (b_s(0) − (s−1))/2 = 2L_0 + 1/2`;
- `Lp` on the inner branch (`K < pM`, `3p ≤ K`, `InnerOK`): `v_p(S_K) + ⌊2 W_I(s)⌋`; if `InnerOK` fails there: the crude value `Lsmall = −((s+1) h ⌊log_p(D+1)⌋ + h·v_p((s−1)!))`, `h = K − N`, `D = s + 2νN + 4(h−1)`.

### 0.3 Hand recomputation of the example (COMPUTED, by hand)

`p = 13`, `K = 40`, `N = 3`, `ν = 6`, `L = (2,5,4,4,7,7,8)` (sum 37 = K − N). `S_40(a) = 6,7,6,6,6,6,6` and `S_3(a) = 0,1,1,1,0,0,0` for `a = 0..6`; so `b_s = (s−6, −1, 0, 0, −6, −6, −6)`.
- `s = 5`: tops of the ordinary classes `5/2, 2, 2, 2, 2, 3`, so `t_5 = 2`; right side `4 + (−1−4)/2 = 3/2`. Test `2 ≤ 3/2` fails. The other conjuncts of `InnerOK` hold (13 odd, `5 ≤ 13`, `40 < 169`, degree `5 + 184 − 80 + 1 = 110 < 169`, sum 37). `Lsmall = −(6·37·⌊log_13 186⌋ + 37·v_13(4!)) = −(444 + 0) = −444`.
- `s = 7`: `t_7 = 1`; right side `4 + (1−6)/2 = 3/2`. Test `1 ≤ 3/2` holds. Capped sums by class: `−3, −15/2, −6, −6, −21, −21, −20`; `W_I(7) = −169/2`; `⌊2W_I⌋ = −169`; with `v_13(S_40) = 50` (source lemma `VS13`, `AssemblyAnchors.lean` 31): `Lp = −119`.
These agree with the report's table (l. 605-606) and with D19.

## 1. `AperyS.AssemblyTarget.WI_sstep_bounds` (D18, first statement)

**a. Statement.** Gate report l. 188-195; source `Zeta5S/FiniteStep.lean` l. 131-134.
```lean
AperyS.AssemblyTarget.WI_sstep_bounds : ∀ (s ν K N p : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  1 ≤ p / 2 →
    ∑ c, L p c = K - N →
      AperyS.AssemblyTarget.WI s ν K N p L - ↑(K - N) ≤ AperyS.AssemblyTarget.WI (s + 2) ν K N p L ∧
        AperyS.AssemblyTarget.WI (s + 2) ν K N p L ≤ AperyS.AssemblyTarget.WI s ν K N p L
```
The printed type in the report (l. 1169-1173) is character-identical.

**b. Definitions.** `WI`, `Allocations`, and under them `wcapS`, `wrawS`, `tminS`, `topwS`, `BseS`, `SX`: §0.

**c. Plain language.** For all naturals `s, ν, K, N`, every natural `p ≥ 2` and every allocation whose rows at `p` number `K − N`: the capped inner weight sum at `s + 2` is at most the one at `s` and at least the one at `s` minus `K − N`. Inequalities in ℚ.

**d. Weakness hunt.**
- Hypotheses are jointly satisfiable for every `p ≥ 2`, `K`, `N` (choose `L`). Not vacuous. Concrete instance: the tuple of §0.3.
- `K - N` is truncated natural subtraction, in the hypothesis and (cast to ℚ) in the conclusion. For `N < K` it is `h`. For `K ≤ N` it is 0, the allocation is empty, both sums are 0 and the statement is trivial.
- `p` is any natural `≥ 2`: not required to be prime or odd. `s`, `ν` arbitrary naturals (no parity, no `s ≤ p`). Wider than the report's setting; nothing weaker.
- No floor, no `toReal`, no junk value: under `1 ≤ p/2` the `dif` in `WI` selects the sum.
- The statement compares two sums. It does not say that each row moves by a number in `[−1,0]` (that is the source lemma `wcapS_shift_bounds`, l. 67, not gated by name), and it says nothing about which rows move.

**e. Against the report.** Report (eq:finite), l. 589-592; row S2, l. 809; D18 entry, l. 1184-1185.
1. `W_I(s) − h ≤ W_I(s+2) ≤ W_I(s)`: agrees, with `h = K − N` rows at `p`.
2. The report says "for a fixed allocation". The Lean also needs the row count at `p` to be `K − N` (stated in the body at l. 583, not in the D18 entry or in row S2) and `p ≥ 2`.
3. The body says "For an odd prime p" (l. 578). The Lean statement is for every natural `p ≥ 2`. Wider.
4. The body's sentences "Increasing s by two lowers each ordinary raw weight and that cap by one; the zero-class raw weight stays unchanged" and "every capped row changes by a number in [−1,0]" are source lemmas of the same file (`wrawS_shift` l. 52, `tminS_shift` l. 32, `wcapS_shift_bounds` l. 67). They are not among the 37 gated declarations and are not printed in the report. I checked them against the definitions by hand (§0.2): they hold.

**f. Verdict: match with the stated differences.**

## 2. `AperyS.AssemblyTarget.Lp_inner_sstep` (D18, second statement)

**a. Statement.** Gate report l. 196-205; source `Zeta5S/FiniteStep.lean` l. 150-154.
```lean
AperyS.AssemblyTarget.Lp_inner_sstep : ∀ (s ν K N M p : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  K < p * M →
    3 * p ≤ K →
      AperyS.AssemblyTarget.InnerOK s ν K N p L →
        AperyS.AssemblyTarget.InnerOK (s + 2) ν K N p L →
          AperyS.AssemblyTarget.Lp s ν K N M p L - 2 * ↑(K - N) ≤ AperyS.AssemblyTarget.Lp (s + 2) ν K N M p L ∧
            AperyS.AssemblyTarget.Lp (s + 2) ν K N M p L ≤ AperyS.AssemblyTarget.Lp s ν K N M p L
```
The printed type in the report (l. 1175-1181) is character-identical.

**b. Definitions.** `Lp`, `InnerOK`, and under them `vSK`, `WI`, `Lsmall`, `Sep`, `PlK`: §0.

**c. Plain language.** If `p` is in the inner range (`K < pM` and `3p ≤ K`) and the allocation passes the whole inner check at `s` and at `s + 2`, then the selected raw exponent at `s + 2` is at most the one at `s` and at least the one at `s` minus `2(K − N)`. Under the hypotheses both exponents are `v_p(S_K) + ⌊2W_I⌋`, and `v_p(S_K)` does not depend on `s`, so this is `⌊2W_I(s)⌋ − 2h ≤ ⌊2W_I(s+2)⌋ ≤ ⌊2W_I(s)⌋`. Inequalities in ℤ.

**d. Weakness hunt.**
- **Can the four hypotheses hold together?** Yes. `(s,ν,K,N,M,p) = (5,6,40,3,400,13)` with `upstreamAlloc`: `40 < 5200`, `39 ≤ 40`, and the source has `inner13_flag5 : InnerOK 5 6 40 3 13 upstreamAlloc` and `inner13_flag7 : InnerOK 7 6 40 3 13 upstreamAlloc` (`Zeta5S/AssemblyAnchors.lean` l. 39, 44; not among the 37 gated declarations; I did not build them). There the same file gives `Lp = −67` at `s = 5` and `−138` at `s = 7` (`exponent5_inner13`, `exponent7_inner13`, l. 65-70): a drop of 71, inside `[0, 74]`. So the statement is not vacuous, on the evidence of those source lemmas.
- `InnerOK` at `s + 2` includes `s + 2 ≤ p`; `InnerOK` forces `p` odd and `≥ 3` and `K < p²`. It does not require `p` prime: the statement is about the defined function `Lp` at any natural `p`.
- The floor: `2(K − N)` is an integer, so subtracting it commutes with the floor; nothing is lost.
- `↑(K − N)`: truncated subtraction cast to ℤ; `InnerOK` gives row count `K − N`.
- `Lp` here is the **raw** selected exponent (`AssemblyData.lean` l. 61), the one of D2. The bridge and Claim 3(b) use `LpSharp` (D4). On the inner branch (`3p ≤ K`) the two definitions have the same text (they differ only in the outer branch), but no gated statement here says so; the source has only `Lp_le_LpSharp` (`SharpAssembly.lean` l. 37).
- It is a comparison of two selected lower bounds. It says nothing about the valuation of the determinant, and nothing when either inner check fails (§3 shows what can happen then).
- The degree conjunct of `InnerOK` uses truncated subtraction; it is a hypothesis, so truncation can only widen the statement.

**e. Against the report.** Body l. 593-594; row S2 l. 809; D18 entry l. 1184-1185.
1. "When both the old and the new inner tests hold, and K<pM, 3p≤K, … L_p(s)−2h ≤ L_p(s+2) ≤ L_p(s)": agrees.
2. "inner tests" / "inner check" is the whole predicate `InnerOK` (eight conjuncts: `p` odd, `p ≥ 3`, `s ≤ p`, separation, `K < p²`, the degree condition, row count `K − N`, the zero-class inequality), not only the zero-class inequality shown in the table of l. 603-606. The D18 entry names `InnerOK`; row S2 says "the inner check". Adequate, once the entry says what the check contains.
3. Row S2 omits the prime range `K < pM`, `3p ≤ K`. The D18 entry has it.
4. The D18 entry says "`Lp` is the raw selected exponent of D2": correct, and it matters, because the section's display (l. 560) is about `L_p^sharp`.
5. The D18 entry's "Where" names the probe `evidence/L-zeta5-general-s` and a v4.33.1 gate report. In the submitted project the file is `Zeta5S/FiniteStep.lean` and the gate is that of 21:12 on v4.35.0.

**f. Verdict: match with the stated differences.**

## 3. `AperyS.AssemblyTarget.switch_Lp5` (D19, first statement)

**a. Statement.** Gate report l. 206-210; source `Zeta5S/FiniteStep.lean` l. 187.
```lean
AperyS.AssemblyTarget.switch_Lp5 : AperyS.AssemblyTarget.Lp 5 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation =
  -444
```
Report l. 1191-1192: character-identical.

**b. Definitions.** `Lp`, `switchAllocation`: §0. Argument order of `Lp` is `s ν K N M p L`: `s=5, ν=6, K=40, N=3, M=400, p=13`.

**c. Plain language.** The raw selected exponent at `s=5, ν=6, K=40, N=3`, cutoff 400, prime 13, with the allocation `(2,5,4,4,7,7,8)`, is the integer −444.

**d. Weakness hunt.**
- A closed statement with no hypothesis; not vacuous.
- **The statement gives a value, not a branch.** That −444 is the fallback (`Lsmall`) and that the inner check fails is not in the type. It is the source lemma `switch_old_flag_false : ¬ InnerOK 5 6 40 3 13 switchAllocation` (l. 172), on which the proof depends and which is not among the 37 gated declarations. My hand computation (§0.3) agrees: the check fails at its zero-class inequality only (`2 ≤ 3/2`), and `Lsmall = −444`. If the check held, the value would be `50 + ⌊2W_I(5)⌋`, which is not −444, so the value does determine the branch, but only after a computation the statement does not contain.
- **The witness is not an allocation the report uses elsewhere.** `switchAllocation` is the constant list `(2,5,4,4,7,7,8)` at every `p` (padded with 0, cut at `p/2+1` entries). At `p = 13` it has 7 entries and sum 37 = K − N, so it is a genuine allocation there. It is neither the explicit water-filling allocation of the bridge (`explicitAllocation`, D12) nor upstream's (`upstreamAlloc`, which at 13 is `(15,3,2,2,5,5,5)` and passes the check at `s = 5` and `7`). It was chosen so that the zero-class test fails at `s = 5` and holds at `s = 7`.
- `Lp` is the raw exponent. At `p = 13`, `K = 40` the inner branch is selected (`39 ≤ 40`), where `Lp` and `LpSharp` have the same text; no statement about `LpSharp` is made.
- −444 is a selected lower bound for `v_13^G(F_40)` (by D3's raw analogue), not that valuation. It is the crude bound, valid and weak.

**e. Against the report.** Body l. 595-610; D19 entry l. 1200-1201; row S2.
1. Value −444, parameters and allocation: agree.
2. The table's columns "Inner zero-class test: 2 ≤ 3/2 fails" and "Selected branch: fallback" are not asserted by D19; see d. The body's closing sentence gives "These statements, values and flags" one label. The flags are source lemmas, not gated declarations with a printed statement.
3. The report does not say that the allocation of the example is chosen for the example. A reader may take it for the allocation of the bridge.

**f. Verdict: match with the stated differences.**

## 4. `AperyS.AssemblyTarget.switch_Lp7` (D19, second statement)

**a. Statement.** Gate report l. 211-215; source `Zeta5S/FiniteStep.lean` l. 191.
```lean
AperyS.AssemblyTarget.switch_Lp7 : AperyS.AssemblyTarget.Lp 7 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation =
  -119
```
Report l. 1193-1194: character-identical.

**b, c.** As §3 with `s = 7`: the raw selected exponent is −119.

**d. Weakness hunt.** As §3. The branch (inner) is the source lemma `switch_new_flag_true : InnerOK 7 6 40 3 13 switchAllocation` (l. 179), with `switch_WI7 : WI 7 6 40 3 13 switchAllocation = -169/2` (l. 185) and `VS13 : vSK 6 40 3 13 = 50`; none is among the 37 gated declarations. By hand (§0.3): the check holds, `W_I = −169/2`, `50 + ⌊−169⌋ = −119`. Here `2W_I` is an integer, so the floor loses nothing.

**e. Against the report.** Value −119, "1 ≤ 3/2 holds", "inner": agree with §0.3; the last two are not asserted by the statement.

**f. Verdict: match with the stated differences.**

## 5. `AperyS.AssemblyTarget.selected_Lp_can_increase` (D19, third statement)

**a. Statement.** Gate report l. 216-221; source `Zeta5S/FiniteStep.lean` l. 195-196.
```lean
AperyS.AssemblyTarget.selected_Lp_can_increase : AperyS.AssemblyTarget.Lp 5 6 40 3 400 13
    AperyS.AssemblyTarget.switchAllocation <
  AperyS.AssemblyTarget.Lp 7 6 40 3 400 13 AperyS.AssemblyTarget.switchAllocation
```
Report l. 1195-1197: character-identical.

**c. Plain language.** At that one tuple, the raw selected exponent at `s = 5` is strictly smaller than at `s = 7`.

**d. Weakness hunt.**
- **"Can increase" is one inequality at one tuple.** The name suggests a general possibility; the type is the single comparison `−444 < −119`, which follows from §3 and §4 and adds nothing to them. It contains no quantifier: not "for some allocation at every prime", not "for infinitely many K", nothing asymptotic.
- The increase is produced by a change of branch: at `s = 5` this allocation fails the inner check and `Lp` falls back to the crude bound. It is an increase of the *selected bound for this allocation*, not of a valuation, and not of the best bound available at `s = 5`: with `upstreamAlloc` the bound at `s = 5` is −67 (source lemma `exponent5_inner13`), which is larger than −119. So the example does not show that the arithmetic gets cheaper from 5 to 7.
- What it does establish: the conclusion `Lp(s+2) ≤ Lp(s)` of §2 is false without the hypothesis `InnerOK s` (all other hypotheses of §2 hold at this tuple: `40 < 5200`, `39 ≤ 40`, `InnerOK 7`). That is exactly the use the report makes of it.
- It says nothing about `LpSharp`, although on this branch the two definitions coincide textually.

**e. Against the report.**
1. "There is no unconditional monotonicity for the selected exponent" (l. 595) and row S2's "the selected exponent is not monotone in s in general": supported, as a counterexample to monotonicity of `s ↦ Lp(s, …, L)` for a fixed arbitrary allocation. Correct as stated, provided "selected exponent" is read as the raw `Lp` with a supplied allocation.
2. "The selected exponent increases by 325" (l. 610): `−119 − (−444) = 325`, correct; the number 325 is not a Lean statement.
3. "although the capped inner rows are nonincreasing": this is §1 (D18).
4. The paragraph title "A finite local step is not automatically an asymptotic step" and its first sentence ("prevented a false generalisation") are an interpretation. No declaration here is asymptotic, and none states what the false generalisation would have been.

**f. Verdict: match with the stated differences.**

## 6. Corrected sentences for the report

1. D18 entry, add to the differences: "The first statement needs `p ≥ 2` and the row count `Σ_c L_p(c) = K − N` at `p`; `p` is any natural number (not necessarily prime) and `s`, `ν` are arbitrary naturals. `InnerOK` is the whole inner check (`p` odd, `p ≥ 3`, `s ≤ p`, separation of the poles, `K < p²`, a degree condition, row count `K − N`, and the zero-class inequality), not only the zero-class inequality of the table. No statement is made for the sharp exponent `LpSharp` of D4; on the inner branch its definition has the same text. That each capped row moves by a number in `[−1,0]` is a lemma of the same source file, not a gated declaration."
2. D19 entry, add: "The three statements give two values and their comparison at one tuple. Which branch is selected, and the two test values `2 ≤ 3/2` and `1 ≤ 3/2`, are not in these types: they are the lemmas `switch_old_flag_false`, `switch_new_flag_true` and `switch_WI7` of the same file, on which the proofs depend and which are not gated by name. The allocation is chosen for the example: it is neither the explicit allocation of the bridge nor upstream's (which at `p = 13` passes the check at `s = 5` and `7`, and there the selected exponent decreases). `selected_Lp_can_increase` is the single inequality `−444 < −119`, with no quantifier. `Lp` is the raw exponent of D2."
3. Body, l. 610, replace the last sentence: "The two values and their comparison are LEAN-VERIFIED (D19), as are the two inequalities for a fixed allocation (D18). The two branch flags and the test values are lemmas of the same Lean file on which those proofs depend; they are not gated by name. The allocation of this example was chosen to make the test fail at s = 5; it is not the allocation of the bridge."
4. Row S2: "…when the inner check holds at s and at s+2 and p is in the inner range (K<pM, 3p≤K), …; for a supplied allocation the selected exponent is not monotone in s in general: with one allocation chosen for the purpose, at K=40, … it goes from −444 … to −119 …".

## 7. Summary of verdicts

| Report | Declaration | Verdict |
|---|---|---|
| D18 | `AperyS.AssemblyTarget.WI_sstep_bounds` | match with the stated differences |
| D18 | `AperyS.AssemblyTarget.Lp_inner_sstep` | match with the stated differences |
| D19 | `AperyS.AssemblyTarget.switch_Lp5` | match with the stated differences |
| D19 | `AperyS.AssemblyTarget.switch_Lp7` | match with the stated differences |
| D19 | `AperyS.AssemblyTarget.selected_Lp_can_increase` | match with the stated differences |

No mismatch and no vacuous statement. Limits of this comparison: statements and definitions only; the non-vacuity of §2 and the branch facts of §3 and §4 rest on source lemmas I read but did not build, and on the hand computation of §0.3; `WO`, `WOsharp` and `Upstream.allocI` were not unfolded (not reached by the five statements). Not checked by a human.
