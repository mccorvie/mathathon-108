# The U-free s-step is positive for every s ≥ 7 (α = 3/40, even ν ≤ 10)

EVENT WORK, Sat Nov 14 2026, 08:47-09:12 PT (times from `TZ=America/Los_Angeles date`). Author: advocate:Claude Opus 5.5, thread sstep-all-s (queue row 31). No human has checked this file. Labels follow AGENTS.md §2.

**Summary (10 lines)**
1. D(s, ν) := 2λ/3 + I_out(s+2, ν) − I_out(s, ν) (λ = 37/40, α = 3/40) is **≥ 167/300 > 0 for every real s ≥ 7 and every real ν ≤ 10** (Theorem 1, PROOF-DRAFT).
2. Lean counterpart `Mathathon.P108.sstep_ge` (and `sstep_pos`, `Tout_sstep`, `Tout_intervalIntegrable`) in the probe `lean_criterion`: **LEAN-CHECKED**, gate passes, statement not yet compared by a human.
3. The proof is pointwise in y, not piece by piece in s: T_out(s+2, y) − T_out(s, y) ≥ −max(0, 8/5 − 3y), and ∫_(1/3)^(37/20) max(0, 8/5 − 3y) dy = 3/50 (Lemma 2, PROOF-DRAFT; Lean `Tout_sstep`).
4. Exact table, odd s = 3..49, ν ∈ {2, 4, 6, 8, 10}, 120 values (COMPUTED, `sstep_all.out`): the minimum over s ≥ 7 is 108349/115200 ≈ 0.9405 at (7, 10); every step from s = 11 on is 191/180.
5. The table agrees exactly with `criterion5/sstep_exact.out` (all 15 steps and their 20 I_out endpoints), with `general_sq.py` I_out_gen at all 125 (s, ν), and with the 20 Lean values `Iout_s_nu` (COMPUTED).
6. Eventually constant: D(s, ν) = 191/180 = 2λ/3 + 4/9 for every real s ≥ s*(ν) = max(ν + 1, 7 + 6(ν−2)α), and there I_out(s, ν) = 2(s+2)/9 − 117ν/1600 + 1851/16000 (Proposition 2, PROOF-DRAFT; COMPUTED check).
7. Hence Θ(7 + 2n, ν; M, U) ≥ Θ(7, ν; M, U) + n·167/300 for every n, M ≥ 3 and U (Corollary 3, PROOF-DRAFT; Lean `thetaPkg_odd_ge`, LEAN-CHECKED).
8. With E59's floor Θ(7, ν) ≥ +0.9058044 (every M ≥ 40, every admissible ρ): **in the slice the package proves irrationality of ζ(s) for no odd s ≥ 7**; with E59's s = 3, 5 rows it closes exactly at s ∈ {3, 5} (Corollary 4, PROOF-DRAFT relative to E13 and E59).
9. E13's admissibility conditions all hold for odd s ≥ 7. The s-dependent ones only get easier as s grows, and Fauzan's (4.9) holds unclamped for every s ≥ 7 (§5, PROOF-DRAFT).
10. Not shown: anything off α = 3/40, ν > 10 or odd ν, and anything outside Fauzan's bound package (§6).

---

## 0. Objects (the authority is `Mathathon/P108/OuterDefs.lean`)

α = 3/40, λ = 1 − α = 37/40. For y ∈ (1/3, 1], k = ⌊1/y⌋ ∈ {1, 2}, v = 1 − ky, u = (α + v − y)₊, m_v = min(α, v), with densities d₀ = α − m_v, d₁ = m_v − u, d₂ = u at ℓ = 2k, 2k+1, 2k+2, and

- B(y) = (1 − y) − Σ_ℓ d_ℓ(ℓ − 2) (the unremoved poles above p),
- C_s(y) = Σ_ℓ d_ℓ c¹_s(ℓ), with c¹_s(ℓ) = Σ_(i=0)^(ℓ−3) max(0, ℓ + s − 1 − ν − 2i),
- ẑ_s(y) = (y − 2α) + Σ_ℓ d_ℓ z¹_s(ℓ), with z¹_s(ℓ) = 1 + #{i ≤ ℓ−3 : ℓ + s − 1 − ν − 2i ≤ 0},
- r̂_s(y) = min(λ, (1 + (ν−2)α − ((s−1)/2) y)₊),

g_s(y) = (s+2)B(y) + C_s(y) + min(r̂_s, ẑ_s) on (1/3, 1], and g_s = 0 elsewhere. T_out(s, y) = g_s(y) + Leg(y), where Leg(y) = −2λ⌊1/y⌋ + Σ_(j=1)^6 (2λ − jy)₊ does not depend on s. I_out(s, ν) = ∫_(1/3)^(2λ) T_out dy. These are criterion5 `derivation.md` §3 (E13), transcribed in `OuterDefs.lean` (`gOuter`, `legendreTerm`, `Tout`, `Iout`), and implemented in `general_sq.py` (`g_general`, `PkgGen.Tout`). `SStepAll.lean` restates g_s as `(s+2)·brK + clK + min rhat zhK` (lemma `gOuter_eq`, proved by unfolding).

## 1. Theorem 1: D(s, ν) ≥ 167/300 for all real s ≥ 7, ν ≤ 10 (PROOF-DRAFT)

**Lemma 1 (PROOF-DRAFT; COMPUTED exact minima in `sstep_all.out` (3a); Lean `dens_nonneg`, `brK_nonneg`).** For y ∈ (1/3, 1]: d₀, d₁, d₂ ≥ 0 and B(y) ≥ 0.
*Proof.* d₀ ≥ 0 since m_v ≤ α, and d₂ = u ≥ 0. Since k = ⌊1/y⌋, we have ky ≤ 1 < (k+1)y, so 0 ≤ v < y. Also y > 1/3 > α. Hence u = max(0, α + v − y) ≤ min(α, v) = m_v (0 ≤ α, 0 ≤ v, α + v − y ≤ α, α + v − y ≤ v), so d₁ ≥ 0. For the bracket, Σ_ℓ d_ℓ(ℓ−2) = (2k−2)α + m_v + u.
- k = 2 (y ≤ 1/2): B = 1 − y − 2α − m_v − u ≥ 1 − y − 4α ≥ 1/2 − 3/10 > 0.
- k = 1 (y > 1/2): B = 1 − y − m_v − u. If α + v − y ≤ 0, then u = 0 and m_v ≤ v = 1 − y. Otherwise u = α + 1 − 2y and m_v ≤ α, so m_v + u ≤ 2α + 1 − 2y ≤ 1 − y, because y > 1/2 > 2α. ∎

**Lemma 2 (pointwise s-step; PROOF-DRAFT; Lean `gOuter_sstep`, `Tout_sstep`).** For real s ≥ 7, real ν ≤ 10 and every y: T_out(s+2, y) − T_out(s, y) ≥ −max(0, 8/5 − 3y).
*Proof.* Outside (1/3, 1] both g's vanish and Leg cancels, so the difference is 0 ≥ −max(0, ·). On (1/3, 1]:

  T_out(s+2) − T_out(s) = 2B + Σ_ℓ d_ℓ [c¹_(s+2)(ℓ) − c¹_s(ℓ)] + min(r̂_(s+2), ẑ_(s+2)) − min(r̂_s, ẑ_s).

(a) 2B ≥ 0 (Lemma 1). (b) Every term of c¹ satisfies max(0, A + 2) ≥ max(0, A), so c¹_(s+2)(ℓ) ≥ c¹_s(ℓ), and d_ℓ ≥ 0 (Lemma 1). (c) r̂ ≥ 0 (λ > 0), and ẑ_(s+2) ≥ y − 2α > 0 because z¹ ≥ 1 and d_ℓ ≥ 0, so min(r̂_(s+2), ẑ_(s+2)) ≥ 0. (d) min(r̂_s, ẑ_s) ≤ r̂_s ≤ (1 + (ν−2)α − ((s−1)/2)y)₊ ≤ (8/5 − 3y)₊. The last step uses (ν − 2)α ≤ 8·3/40 = 3/5 and ((s−1)/2)y ≥ 3y (s ≥ 7, y > 0). Adding (a)-(d) gives the claim. ∎

**Theorem 1 (PROOF-DRAFT).** For all real s ≥ 7 and ν ≤ 10, at α = 3/40:
  D(s, ν) = 2λ/3 + I_out(s+2, ν) − I_out(s, ν) ≥ 37/60 − 3/50 = **167/300 ≈ 0.5567**.
*Proof.* T_out(s, ·) is interval integrable on [1/3, 2λ] for every real s, ν: it agrees with a continuous function on each of (1/3, 1/2], (1/2, 1] and (1, 2λ], where ⌊1/y⌋ = 2, 1, 0 (Lean `Tout_intervalIntegrable`). Integrate Lemma 2 over [1/3, 2λ]. The function max(0, 8/5 − 3y) is the triangle with height 3/5 at y = 1/3 that vanishes from y = 8/15 on, so its integral is (1/2)(3/5)(1/5) = 3/50. ∎

*Sharper form (PROOF-DRAFT; ∫B COMPUTED exactly).* Keeping the term 2B in Lemma 2 gives D ≥ 2λ/3 + 2∫_(1/3)^1 B − 3/50 = 37/60 + 2147/7200 − 3/50 = **1231/1440 ≈ 0.8549**, with ∫_(1/3)^1 B = 2147/14400. The Lean statement uses the weaker 167/300.

**Formal counterpart (LEAN-CHECKED: `scripts/lean_check.py` passes, statement not yet compared by a human).** `lean:Mathathon.P108.sstep_ge@problems/108-zeta-odd-autopsy/evidence/lean_criterion`, printed statement

  `∀ (s ν : ℝ), 7 ≤ s → ν ≤ 10 → 167 / 300 ≤ 2 * (1 - 3 / 40) / 3 + (Iout (s + 2) ν (3 / 40) - Iout s ν (3 / 40))`,

axioms propext, Classical.choice, Quot.sound (`LEAN_CHECK_sstep_all.md`). Also `sstep_pos` (the same with 0 <), `Tout_sstep` (Lemma 2 for T_out) and `Tout_intervalIntegrable`, all PASS. Differences from the claim: `Iout`/`Tout` are the OuterDefs.lean transcriptions of E13's formulas, not a formal derivation of them from Fauzan's valuation bounds. The Lean statement is for real s and ν, which is stronger than "odd s, even ν".

## 2. Proposition 2: the step is eventually constant (PROOF-DRAFT; COMPUTED check)

For real s ≥ s*(ν) := max(ν + 1, 7 + 6(ν−2)α), **D(s, ν) = 191/180 = 2λ/3 + 4/9 ≈ 1.0611**, and I_out(s, ν, 3/40) = 2(s+2)/9 − νW + L, where W = ∫_(1/3)^1 Σ_ℓ d_ℓ(ℓ−2) dy = 117/1600 and L = ∫_(1/3)^(2λ) Leg dy = 1851/16000.
*Proof.* (i) If s ≥ 7 + 6(ν−2)α, then 1 + (ν−2)α − ((s−1)/2)y < 1 + (ν−2)α − (s−1)/6 ≤ 0 for y > 1/3. So r̂_s = r̂_(s+2) = 0 on (1/3, 1], and min(r̂, ẑ) = 0 because ẑ > 0. (ii) If s ≥ ν + 1, then every argument of c¹_s(ℓ), ℓ ≤ 6, satisfies ℓ + s − 1 − ν − 2i ≥ s + 5 − ν − ℓ ≥ 0, so c¹_s(ℓ) = (ℓ−2)(s+2−ν). Hence g_s = (s+2)(1−y) − νΣ_ℓ d_ℓ(ℓ−2) on (1/3, 1], and T_out(s+2) − T_out(s) = 2(1 − y) there and 0 beyond. Since ∫_(1/3)^1 2(1−y) dy = 4/9, we get D = 37/60 + 4/9 = 191/180. ∎
s*(ν) = 7, 7.9, 8.8, 9.7, 11 for ν = 2, 4, 6, 8, 10. COMPUTED (`sstep_all.out` (3d)): D = 191/180 at every odd s ≥ s* up to 49 and at 62 rational s ≥ s* per ν. The closed form for I_out holds at the odd s ≥ s* up to 51 and at 3 rational s per ν. The only odd s ≥ 7 with D ≠ 191/180 are (7, ν ≥ 4) and (9, ν ≥ 8). This explains the scout's "all 15 exact steps exceed 2λ/3": the excess I_out(s+2) − I_out(s) is 4/9 = ∫_(1/3)^1 2(1 − y) dy from s* on. Every pole j ∈ (p, K] then costs two more powers of p per step, whether or not its class has a removed pole: through the per-pole cost s + 2 of derivation §3 for unremoved classes, and through the rows of c¹, all active from s ≥ ν + 1, for removed ones.

*Breakpoints in s (PROOF-DRAFT remark; not needed for Theorem 1).* On 7 ≤ s < s*(ν), I_out(·, ν) is piecewise rational in s, not polynomial. The kink y₀(s) = (1 + (ν−2)α)/((s−1)/2) of r̂ and the crossing r̂ = ẑ move with s, so the integrals contain 1/(s−1)-type terms. The cap r̂ = λ is inactive on (1/3, 1] for s ≥ 1 + 6(ν−1)α (≤ 5.05). c¹ and z¹ change at the integers s = ν + 1 + 2i − ℓ, which in [7, ν+1] are {7, ..., 11} (ν = 10), {7, 8, 9} (ν = 8), {7} (ν = 6), and none for ν ≤ 4. Theorem 1 does not need these pieces: Lemma 2 is uniform in s, so it covers every piece at once. As a consistency check only, exact D on the grid s = 7, 7 + 1/8, ..., 21 (113 values per ν; COMPUTED, (4)) has its minimum at s = 7 for each ν, and that minimum is ≥ 0.9405.

## 3. The exact step table (COMPUTED)

`sstep_all.py` transcribes OuterDefs.lean independently. Its exact integrator enumerates every kink in closed form: the fixed kinks 1/3, 1/2, 1, 2λ, (1±α)/2, (1+α)/3, 1−α and 2λ/j; the two kinks of r̂; and the crossing r̂ = ẑ, solved on each sub-interval. It checks every piece affine at 5 interior points (an assertion, so a missing kink would stop the run). D(s, ν), odd s = 3..49, α = 3/40:

| s | ν = 2 | ν = 4 | ν = 6 | ν = 8 | ν = 10 |
|---|---|---|---|---|---|
| 3 | 52213/57600 (0.906476) | 48433/57600 (0.840851) | 1699/2304 (0.737413) | 38191/57600 (0.663038) | 7697/11520 (0.668142) |
| 5 | 9929/9600 (1.034271) | 4867/4800 (1.013958) | 751/768 (0.977865) | 12817/14400 (0.890069) | 92111/115200 (0.799575) |
| 7 | 191/180 (1.061111) | 7613/7200 (1.057361) | 1883/1800 (1.046111) | 2345/2304 (1.017795) | 108349/115200 (0.940530) |
| 9 | 191/180 (1.061111) | 191/180 (1.061111) | 191/180 (1.061111) | 30511/28800 (1.059410) | 11983/11520 (1.040191) |
| 11, 13, ..., 49 (20 rows) | 191/180 | 191/180 | 191/180 | 191/180 | 191/180 |

The full 24-row table is printed in `sstep_all.out`. Checks (COMPUTED, all PASS):
- the s = 3, 5, 7 rows equal `criterion5/sstep_exact.out` exactly: the 15 steps, their 20 I_out endpoints and their ΔI_out;
- all 125 values I_out(s, ν), s = 3..51 odd, equal `general_sq.py` `I_out_gen(PkgGen(s, ν))` (read-only import);
- the 20 Lean theorems `Iout_s_nu` (s ∈ {3, 5, 7, 9}, ν ∈ {2, ..., 10}) in `OuterValues.lean` and `OuterValues2.lean` agree. *Note:* the brief says 35 Lean values. These two files hold 20 `Iout` value theorems. `OuterValues58.lean` holds the (5, 8) Proposition A pieces, which are not plain `Iout s ν (3/40)` values.

## 4. Consequences for the margin

**Corollary 3 (PROOF-DRAFT given E13 Corollary 4; Lean `thetaPkg_odd_ge`, LEAN-CHECKED).** For every n ∈ ℕ, ν ≤ 10, M ≥ 3 and every value U of the analytic term: Θ(7 + 2n, ν; M, U) ≥ Θ(7, ν; M, U) + n·167/300.
*Proof.* Θ(s+2) − Θ(s) = D(s, ν) for every M ≥ 3 and every U (C108-LC3, `thetaPkg_sstep`; U is s-free, Xu §3, CITED via derivation §4). Apply Theorem 1 n times. ∎
Exact refinement (COMPUTED + Proposition 2): D(s, ν) ≥ 108349/115200 for every odd s ≥ 7, and Θ(s, ν) − Θ(11, ν) = (s − 11)·191/360 for odd s ≥ 11.

**Corollary 4 (the slice criterion; PROOF-DRAFT relative to E13 (PROOF-DRAFT) and E59 (COMPUTED)).** In the slice α = 3/40, even ν ≤ 10, for every odd s ≥ 7, every M ≥ 40 and every admissible comparison measure ρ:
  Θ(s, ν; M, ρ) ≥ 0.9058044 + ((s − 7)/2)·0.9405 > 0.
So Fauzan's bound package, written for general odd s, proves the irrationality of ζ(s) for no odd s ≥ 7 in this slice. Together with E59's rows (s = 3 closes for every ν; s = 5 closes at ν = 4, 6, and at ν = 8 with Prop. A), the package closes in the slice exactly for s ∈ {3, 5}.
*Proof.* E59 (`criterion_map/TABLE.md` §2-§3, COMPUTED) gives A*(7, ν) + LB(ν) ≥ +0.9058044 for every even ν ≤ 10, and A_M ≥ A* for M ≥ 40 (E33(e)). By Lemma 2 of derivation §4, U(ν; ρ) ≥ LB(ν) for every admissible ρ. So Θ(7, ν; M, ρ) ≥ 0.9058044. Apply Corollary 3 with U = U(ν; ρ), and use D ≥ 108349/115200 > 0.9405. ∎
Lean has only the implication part (`thetaPkg_odd_pos`: Θ(7) > 0 ⇒ Θ(7 + 2n) > 0, LEAN-CHECKED). The 0.9058 floor is COMPUTED, not formalized.

## 5. E13's admissibility conditions at large s (PROOF-DRAFT unless labelled)

These are the hypotheses that derivation.md (Theorem 3, §2-§3) places on (s, ν, α):
1. *Odd s ≥ 3, even ν ≥ 2, α ∈ (0, 1/3).* These hold. Oddness of s is used in §3 (H^(s)_(p−a) ≡ H^(s)_(a−1) mod p).
2. *L_a ≥ 0 at every inner prime* (holds for ν ≤ 10 at α = 3/40, skeptic2). L_a = T − b_a + ε_a, with T = ⌊2Hx⌋, H = λ + (ν/2)α and b_a = (ν/2)ℓ_N(a). This has no s in it (derivation §2.1-§2.2), so the condition is the same for every s.
3. *Degree side conditions of Prop. 4.1, "true for K large".* Fauzan (4.1), p. 9, CITED: K ∈ 40Z, K ≥ 200M², K/M < p ≤ K/3. Fauzan (4.9), p. 11, CITED: p ≥ 7, p ≤ K < 3p, p² > 2K, 2N < p, 5N ≤ 2p − 2, and "these conditions hold when K ≥ 200M² and K/3 < p ≤ K". For fixed s, M and α these constrain only K, and Θ is a K → ∞ limit. Whether the constant 200 must grow with s (Fauzan's reserved rows L₀ = 4M + 10 are written at s = 5) is not checked here (HEURISTIC that it is harmless: only K ≥ C(s)M² would be needed).
4. *Fauzan's (4.9) read as (ν − 1)α < (s − 1)/6.* For s ≥ 7 and ν ≤ 10: (ν−1)α ≤ 27/40 < 1 ≤ (s−1)/6. So every s ≥ 7 row satisfies the old hypothesis, and none relies on the rank clamp min(λ, ·). The rows that do rely on it are (5, 10) and (3, ν ≥ 6).
5. *c⁰(ℓ) = (s+2)(ℓ−2) with two zero weights needs ℓ < s + 5.* Here ℓ ≤ 6, so this holds for every s ≥ 2 (general_sq C3a checks s = 3..49, ℓ = 2..6).
6. *Moment cutoff (s4) and rank r_p = max(0, K + (ν−2)N − r(p−1)), r = (s−1)/2.* Both are valid for every odd s (derivation §1, §3). For s ≥ 7 + 6(ν−2)α the rank is 0 at every outer prime, which matches r̂ ≡ 0 in Proposition 2.
7. *Crude range* (3.12): its cost (s+1)⌊log_p 5K⌋ + v_p((s−1)!) enters Θ as (s+1)λ/M. That term is part of the step identity (derivation §2, Corollary) and is already inside D.

No condition fails or tightens as s grows. The s-dependent ones (4, 5, 6) get easier.

## 6. What this does not show

- Scope: α = 3/40, λ = 37/40, ν ≤ 10 (even for the margin; the Lean bound is for every real ν ≤ 10), and Fauzan's bound package exactly as E13 writes it. "Fails" is about the package, not about ζ(s): a different normaliser or sharper local bounds are outside it (derivation Theorem 3).
- The outer formulas themselves (E13 §3) are PROOF-DRAFT and not formalized. Lean checks only the consequences of their transcription. Novelty: not assessed (the librarian sets verdicts). The qualitative fact that larger s costs more on the arithmetic side is known (derivation.md sources: keithadler/zeta42 `zeta7/README.md`; librarian MAP.md §D(ii)). The uniform pointwise bound and the closed form 191/180 are computed here from E13's formulas.

## 7. Files and reproduction

- `sstep_all.py`, `sstep_all.out`: `python3 sstep_all.py` (about 45 s, exit 0, "ALL CHECKS PASSED").
- `SStepAll.lean`: master copy of the Lean file. It is copied byte-identically to `../lean_criterion/LeanCriterion/SStepAll.lean` (the file this task allowed outside the folder). `LeanCriterion.lean` was **not** edited. To rebuild and recheck: `cd ../lean_criterion && lake build LeanCriterion.SStepAll && lake build`, then, from the repo root, `python3 scripts/lean_check.py --root problems/108-zeta-odd-autopsy/evidence/lean_criterion --lib LeanCriterion --lib LeanCriterion.SStepAll --decl Mathathon.P108.sstep_ge --decl Mathathon.P108.sstep_pos --decl Mathathon.P108.thetaPkg_odd_ge --decl Mathathon.P108.thetaPkg_odd_pos --decl Mathathon.P108.Tout_sstep --decl Mathathon.P108.Tout_intervalIntegrable`. It passed at 09:06 PT: 6 declarations, axioms propext, Classical.choice, Quot.sound, no forbidden tokens. The probe's default `lake build` also passes.
- `LEAN_CHECK_sstep_all.md`: a copy of the report. lean_check.py writes its report to `../lean_criterion/log/LEAN_CHECK.md` and overwrote the 01:24 PT report there; that earlier report is preserved here as `prev_probe_LEAN_CHECK.md`.

**Credits** (AGENTS.md §3). Fauzan, Zenodo 22826419 v1: the package, (4.1) p. 9 and (4.9) p. 11 (pages checked with `pdftotext -f N -l N`), read in `~/mathathon-cache/108/fauzan.txt`. Lai, ai.vixra 2609.0080v1 (via derivation.md). Xu, Anchen0823/zeta9-research-notes@eb264a73 §3: U is s-free (via derivation.md §4). criterion5 `derivation.md` (E13, advocate:criterion5) and `general_sq.py`, `sstep_exact.out` (E14). Formalizer (Claude Opus 5.5): `OuterDefs.lean`, `SStep.lean` (`thetaPkg_sstep`, C108-LC3), `piece_integral`, `integral_concat`, `fl0`-`fl2`, reused here. criterion_map `TABLE.md` (E59, synthesis): the ζ(7) floor. skeptic2: L_a ≥ 0 only for ν ≤ 10. The scout's brief (queue row 31): the upside statement and the HEURISTIC observation that all 15 steps exceed 2λ/3. AI use: this whole file, the script and the Lean file are by Claude Opus 5.5. They were checked by exact recomputation against three independent implementations (above) and by the Lean gate.
