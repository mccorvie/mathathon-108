# #108 statement-comparison sheet (for the owner): LEAN-CHECKED → LEAN-VERIFIED?

**EVENT WORK** (#108, human-check preparer, Claude Opus 5.5, Fri Nov 13 2026, 23:08-23:25 PT). This file
upgrades nothing. Only a human who answers the checklists below may upgrade a LEAN-CHECKED claim to
LEAN-VERIFIED (AGENTS.md §2, §5). LEAN-CONDITIONAL claims (C108-LS2) cannot be upgraded by a statement
comparison at all: they keep named `sorry`s.

**Toolchain of the printed statements** (added Sat 01:29 PT by formalizer 5 / porter, Claude Opus 5.5, event
work). Every statement and axiom list quoted in (b) below was printed on **Lean/Mathlib v4.35.0** (Fri
23:13-23:15 PT), before the build target moved to v4.33.1. For **§1 (C108-LW1) and §3 (C108-LC1..LC6)** the
v4.33.1 gate runs (Sat 01:14 PT `lean_witness`, 9 declarations; Sat 01:24 PT `lean_criterion` and Sat 01:26 PT
repo root, 49 declarations each; reports in each probe's `log/LEAN_CHECK.md`, root copy in
`lean_criterion/log/LEAN_CHECK_root.md`) print **byte-identical** statements (`#check`) to the v4.35.0 gate
runs, with the same axioms, and no Lean source changed in the port; so (b) holds verbatim on v4.33.1. **§2
(C108-LS1, LS2, `lean_skip`)** is formalizer 4's port: until its v4.33.1 run is recorded here, read §2's (b) as
printed on v4.35.0 only.

**How to use it.** Each section: (a) the claim, (b) the Lean statement and every definition it uses,
verbatim with file:line, (c) the source each definition encodes, verbatim, (d) yes/no questions, (e) the
stated differences copied from `log/CLAIMS.md`, (f) a reading time. If every answer in (d) is "yes" and you
accept (e), the claim's row in `log/CLAIMS.md` can be changed to LEAN-VERIFIED by you.

**Mismatches found while preparing this sheet: none in the mathematics.** Two provenance notes, not
mismatches (no ⚠ needed):
- The per-folder `log/LEAN_CHECK.md` files were overwritten by the orchestrator's later re-runs: the
  `lean_witness` one (22:16 PT) now lists only `classLoss_witness`, the `lean_criterion` one (23:11 PT)
  only `innerR_shift`, `thetaPkg_sstep`, `lai_offset_gap_7_2`. The 9-declaration (witness) and
  49-declaration (criterion) PASS records survive only in `log/CLAIMS.md`, `log/EVENT_LOG.md` and the
  dossier. So I re-printed every statement and its axioms myself, read-only, at 23:13-23:15 PT
  (`lake env lean` on a scratch file that only imports the probe; no Lean file changed). Every statement
  quoted in (b) below is that output, and the axioms agree with the CLAIMS rows: `propext,
  Classical.choice, Quot.sound` everywhere, except `beta_eq` (none) and `laiSkips_all_of_ge_27`
  (`propext, Quot.sound`). The four C108-LS2 theorems and the two sorries show `sorryAx`, as stated.
  This is not a `lean_check.py` run. Outputs:
  `/private/tmp/claude-501/-Users-jack-Library-Application-Support-Claude-scratch-workspaces-f84c0719-1fc3-4a02-8618-d18d9fee307c-41484cae-f9fd-4f1a-aadb-82b393529446-scratch-2026-11-13-630807/06c2099f-dc87-4dcb-a268-9095e8abfc2a/scratchpad/humancheck/{AxW,AxS,AxC}.out`.
- `classLoss_witness` does **not** depend on `Z_decomp`. `Z_decomp` is what certifies that `entry` really
  is μ_X(Z/D_40) (see §1 (d) Q4), so read its statement too. Its axioms are standard (my re-print above).

Copies: `Mathathon/P108/{LaiSkip,LaiSkipData,InnerShift,Integrable,OffsetGap,OuterDefs,OuterValues,
OuterValues2,SStep,SStepTable}.lean` differ from the probe files `evidence/lean_skip/LeanSkip/*` and
`evidence/lean_criterion/LeanCriterion/*` **only in their `import` lines** (`diff`, 23:10 PT). Line numbers
below are the probe files' and are the same in the copies. `ClassLoss.lean` has no copy in `Mathathon/`.

Total reading time: about 40 minutes (§1 12, §2 13, §3 15).

---

## 1. C108-LW1: `Mathathon.P108.classLoss_witness` (dossier E21)

File: `problems/108-zeta-odd-autopsy/evidence/lean_witness/LeanWitness/ClassLoss.lean` (277 lines).

### (a) Claim

Take K = 40, N = 3, ν = 2, p = 13, and Z(t) = D_3(t)² ∏_{c∈{0,…,6}, c≠2} (t+c²)^10. Lai's Program 11 ζ(7)
functional, extended linearly over the partial fractions of Z/D_40, gives μ_X(Z/D_40) = A + B·X with
v_13(A) = −10 and v_13(B) = 0. The class count (the minimum over residues c mod 13 of the number of x-roots
≡ c minus the number of poles ≡ c) is β = −4, so the loss β − min(v_13 A, v_13 B) is 6.

### (b) Lean statement (printed by Lean) and definitions (verbatim)

```lean
Mathathon.P108.classLoss_witness : padicValRat 13 Mathathon.P108.entry.1 = -10 ∧
  padicValRat 13 Mathathon.P108.entry.2 = 0 ∧
    Mathathon.P108.beta = -4 ∧
      Mathathon.P108.beta - min (padicValRat 13 Mathathon.P108.entry.1) (padicValRat 13 Mathathon.P108.entry.2) = 6
```
Supporting statements, which are not dependencies of the theorem but carry its meaning:
```lean
Mathathon.P108.Z_decomp : (Mathathon.P108.QR.1.mul (Mathathon.P108.D 40)).add Mathathon.P108.poleSum = Mathathon.P108.Z
Mathathon.P108.QR_length : List.length Mathathon.P108.Z = 67 ∧ List.getLast? Mathathon.P108.Z = some 1 ∧
    List.length (Mathathon.P108.D 40) = 41 ∧ List.getLast? (Mathathon.P108.D 40) = some 1 ∧
        List.length Mathathon.P108.QR.1 = 27 ∧ List.length Mathathon.P108.QR.2 = 40 ∧ List.length Mathathon.P108.poleSum = 40
```
(`QR_length`'s line breaks are joined here.) `beta_eq` (l. 262) also states
`beta = -4 ∧ (∀ c : ℕ, c < 13 → -4 ≤ classCount c) ∧ classCount 2 = -4`.

Definitions, in dependency order (ClassLoss.lean):
```lean
-- l. 45
abbrev Poly := List ℚ
-- l. 50-53
def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q
-- l. 56
def smul (c : ℚ) (p : Poly) : Poly := p.map (c * ·)
-- l. 59-61
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)
-- l. 64-66
def pow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n + 1 => mul (pow p n) p
-- l. 69
def prod (ps : List Poly) : Poly := ps.foldr mul [1]
-- l. 72
def eval (p : Poly) (x : ℚ) : ℚ := p.foldr (fun a acc => a + x * acc) 0
-- l. 75
def deriv (p : Poly) : Poly := (p.zipIdx.map fun ai => (ai.2 : ℚ) * ai.1).tail
-- l. 94-96 (Euclidean division; its output is certified by Z_decomp, so you need not read
-- subScaled l. 79-82 and divLoop l. 87-90)
def divMonic (z d : Poly) : Poly × Poly :=
  let res := divLoop d.reverse.tail (z.length + 1 - d.length) [] z.reverse
  (res.1, res.2.reverse)
-- l. 105
def lin (γ : ℕ) : Poly := [((γ : ℕ) : ℚ) ^ 2, 1]
-- l. 108
def D (A : ℕ) : Poly := prod ((List.range A).map fun i => lin (i + 1))
-- l. 112
def Z : Poly := mul (pow (D 3) 2) (prod (((List.range 7).filter (· ≠ 2)).map fun c => pow (lin c) 10))
-- l. 115
def H7 (j : ℕ) : ℚ := ((List.range j).map fun v => 1 / ((v + 1 : ℕ) : ℚ) ^ 7).sum
-- l. 119-121
def muMono (bern : ℕ → ℚ) (e : ℕ) : ℚ :=
  (-1) ^ e * bern (2 * e + 2) *
    (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) * (2 * e + 6) * (2 * e + 7) : ℕ) : ℚ) / 720
-- l. 125
def muPole (j : ℕ) : ℚ × ℚ := (1 / (2 * (j : ℚ)) - 1 / 6 - (j : ℚ) ^ 6 * H7 j, (j : ℚ) ^ 6)
-- l. 128
def QR : Poly × Poly := divMonic Z (D 40)
-- l. 131
def resid (j : ℕ) : ℚ := QR.2.eval (-((j : ℚ) ^ 2)) / (deriv (D 40)).eval (-((j : ℚ) ^ 2))
-- l. 134
def Dexcept (j : ℕ) : Poly := prod (((List.range 40).filter (· + 1 ≠ j)).map fun i => lin (i + 1))
-- l. 137
def poleSum : Poly := ((List.range 40).map fun i => smul (resid (i + 1)) (Dexcept (i + 1))).foldr add []
-- l. 141-144
def entryWith (bern : ℕ → ℚ) : ℚ × ℚ :=
  (((List.range QR.1.length).map (fun e => QR.1.getD e 0 * muMono bern e)).sum +
      ((List.range 40).map fun i => resid (i + 1) * (muPole (i + 1)).1).sum,
    ((List.range 40).map fun i => resid (i + 1) * (muPole (i + 1)).2).sum)
-- l. 148
noncomputable def entry : ℚ × ℚ := entryWith bernoulli
-- l. 152-157
def xRoots : List ℤ :=
  List.replicate 7 0 ++
    ((List.range 3).flatMap fun i =>
      (List.replicate 2 [((i + 1 : ℕ) : ℤ), -((i + 1 : ℕ) : ℤ)]).flatten) ++
    (((List.range 7).filter (· ≠ 2)).flatMap fun c =>
      (List.replicate 10 [((c : ℕ) : ℤ), -((c : ℕ) : ℤ)]).flatten)
-- l. 160
def poles : List ℤ := (List.range 40).flatMap fun i => [((i + 1 : ℕ) : ℤ), -((i + 1 : ℕ) : ℤ)]
-- l. 163-164
def classCount (c : ℤ) : ℤ :=
  ((xRoots.countP fun x => decide (x % 13 = c)) : ℤ) - ((poles.countP fun x => decide (x % 13 = c)) : ℤ)
-- l. 167
def beta : ℤ := ((List.range 13).map fun c => classCount c).foldl min (classCount 0)
```
Mathlib primitives: `bernoulli` (Mathlib.NumberTheory.Bernoulli, `bernoulli n = (-1)^n * bernoulli' n`, so
B_1 = −1/2; only even indices 2…54 occur), `padicValRat`, `List.*`, `Int` `%` (= `Int.emod`, values in
0..12 for modulus 13). The proof replaces `bernoulli` by a table: `bernTab_eq` (l. 191,
`bernTab.getD n 0 = bernoulli' n` for n < 55, proved through Mathlib's `bernoulli'_def`) and `bernFast_eq`
(l. 203, `bernFast = bernoulli`). The table is used only in the proof, not in the statement.

### (c) Sources (verbatim)

Lai, laichunwing/Zeta7-is-Irrational@c42a984f `11_padic_valuation.txt`
(`~/mathathon-cache/108/repos/laichunwing_Zeta7-is-Irrational/`):
```python
# l. 12-15
K_val = 40
nu    = 2
N_val = (3 * K_val) // 40
h_val = (37 * K_val) // 40
# l. 33-41
D_K = Qt(1)
for k in range(1, K_val + 1):
    D_K *= (t + k**2)
D_K_prime = D_K.derivative()

H_vals = {j: sum(QQ(1)/QQ(v)**7 for v in range(1, j+1))
          for j in range(1, K_val + 1)}
D_Kp_at_pole = {j: D_K_prime(-j**2) for j in range(1, K_val + 1)}
# l. 46-73
def mu_entry_affine(i, j):
    """Return (a, b) such that μ_X(D_N^ν · t^(i+j) / D_K) = a + b·X."""
    R_num = D_N_nu * t**(i + j)
    Q_poly, R_rem = R_num.quo_rem(D_K)

    a = QQ(0)
    b = QQ(0)

    # Polynomial part: sum μ_X(t^e) * coeff (independent of X)
    for e in range(Q_poly.degree() + 1):
        coeff = Q_poly[e]
        if coeff == 0:
            continue
        B_e = bernoulli(2*e + 2)
        val = (-1)**e * B_e * (2*e+3)*(2*e+4)*(2*e+5)*(2*e+6)*(2*e+7) / QQ(720)
        a += coeff * val

    # Pole part: sum c_j * (j^6(X - H_j) + 1/(2j) - 1/6)
    # = (sum c_j · j^6) X  +  sum c_j · (1/(2j) - 1/6 - j^6 H_j)
    for j_pole in range(1, K_val + 1):
        c = R_rem(-j_pole**2) / D_Kp_at_pole[j_pole]
        if c == 0:
            continue
        Hj = H_vals[j_pole]
        b += c * j_pole**6
        a += c * (QQ(1)/(2*j_pole) - QQ(1)/6 - j_pole**6 * Hj)

    return (a, b)
```
Lai's note (ai.vixra 2609.0080v1, `~/mathathon-cache/108/lai.txt` l. 176-185, PDF p. 4; OCR text), the
linear extension that Program 11 implements (stated there for the ζ(5) functional):
```
Remark 4.3 (Well-definedness). Every R ∈ R admits a unique partial fraction decomposition
                                                ∑︂ cj
                                 R(t) = P (t) +          ,                              (13)
                                                  t + j2
                                                                          j≥1
where P ∈ Q[t] and cj ∈ Q are uniquely determined, and cj = 0 for all but finitely many j. Extend
µX linearly:                                             (︃        )︃
                                                ∑︂             1
                            µX (R) := µX (P ) +    cj µX              .                      (14)
                                                            t + j2
```
The numerator Z and the class count are not Lai's. They come from the advocate's
`evidence/lai-nu2-audit/class_loss.py`:
```python
# l. 141-148 (inside run(K, p, a, s, nu, e, Lo); called with K=40, p=13, a=2, s=7, nu=2, e=0, Lo=10)
    DN = [F(1)]
    for j in range(1, N + 1):
        DN = pmul(DN, [F(j * j), F(1)])
    Z = ppow(DN, nu)
    for c in range(0, m + 1):
        if c != a:
            Z = pmul(Z, ppow([F(c * c), F(1)], Lo))
    Z = pmul(Z, ppow([F(a * a), F(1)], e))
# l. 151-164
    # Zeta5's beta is the minimum over ALL residues c mod p of (#x-roots = c) - (#poles = c),
    # x-roots: s zeros (x^s), nu copies of +-j (j <= N), Lo copies of +-c (c != a), e copies of +-a
    roots = [0] * s
    for j in range(1, N + 1):
        roots += [j, -j] * nu
    for c in range(0, m + 1):
        if c != a:
            roots += [c, -c] * Lo
    roots += [a, -a] * e
    poles = [r for j in range(1, K + 1) for r in (j, -j)]
    beta = min(sum(1 for x in roots if (x - c) % p == 0) - sum(1 for r in poles if (r - c) % p == 0)
               for c in range(p))
    v = min(vp(A, p), vp(Bx, p))
    return beta_a, beta, vp(A, p), vp(Bx, p), beta - v
```
That code transcribes the ζ(5) class count of mo271/Zeta5@7fe73676 (`~/mathathon-cache/108/repos/Zeta5/`):
```lean
-- Apery/Arith/TEntry.lean l. 24
def xroots (M : Multiset ℤ) : Multiset ℤ := Multiset.replicate 5 0 + M + M.map (fun γ => -γ)
-- Apery/Arith/TEntry.lean l. 66-71
theorem μX_tpol_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Sep p (PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ ((if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) - (plc p (PlK K) c).card) :
    GV p (μX K (tpol M)) (β - 4) := by
-- Apery/Arith/Pullback.lean l. 77-78
def PlK (K : ℕ) : Finset ℤ :=
  (Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))
```
The output row this formalizes is `evidence/lai-nu2-audit/out/class_loss.txt` l. 49:
` 7   2  13  2  0 |     -4    -4   -10     0 |    6`.

### (d) Checklist

1. Is `muMono bernoulli e` (l. 119-121) Program 11 l. 59-60, `(-1)**e * bernoulli(2*e+2) * (2e+3)…(2e+7) / 720`?
   (Sage's and Mathlib's `bernoulli` agree at even indices.)
2. Is `muPole j` (l. 125), read as (constant term, coefficient of X), Program 11 l. 70-71
   (`b += c·j^6`, `a += c·(1/(2j) − 1/6 − j^6 H_j)`), with `H7 j` (l. 115) = l. 38 `sum 1/v^7, v = 1..j`?
3. Are the poles j = 1..40 (`List.range 40` with `i + 1`) and `resid j` (l. 131) the set and the coefficient of
   Program 11 l. 65-66 (`range(1, K_val + 1)`, `R_rem(-j²)/D_K'(-j²)`), with `deriv` (l. 75) the formal derivative?
4. Do `Z_decomp` (Z = QR.1·D_40 + Σ_j resid_j·D_40/(t+j²) as coefficient lists) and the list operations
   `add`/`mul`/`pow`/`prod` (l. 50-69) convince you that `entryWith` evaluates Lai's linear extension (13)-(14)
   on the unique partial-fraction decomposition of Z/D_40? (The identity alone suffices. Partial fractions are
   unique, so neither `divMonic` nor `QR_length` needs to be trusted.)
5. Is `Z` (l. 112) the class_loss.py numerator at N = 3, ν = 2, m = (13−1)/2 = 6, a = 2, Lo = 10, e = 0,
   i.e. D_3² ∏_{c∈{0..6}, c≠2}(t+c²)^10? (It is not a Program 11 entry D_N^ν t^{i+j}: stated difference (3).)
6. Is `beta` (l. 152-167) Zeta5's hβ class count (`xroots` with M = {1,2,3}×2 ∪ {0,1,3,4,5,6}×10, poles
   `PlK 40`), with `Multiset.replicate 5 0` replaced by 7 zeros (the x^s pullback at s = 7)? Note: by
   `beta_eq` the minimum −4 is attained at residue 2 (and at 11 = −2), which no zero reaches, so 5 or 7
   zeros give the same β.
7. Is β − min(v_13 A, v_13 B) the "loss" of class_loss.py l. 163-164 (`beta - v`, `v = min(vp(A), vp(Bx))`)?
   A and B are nonzero, so `padicValRat` (which is 0 at 0) agrees with `vp`.
8. Do you accept stated difference (1): the theorem gives loss 6, but the claim that Lai's certificate needs
   loss ≤ 0 at this entry is the advocate's reading, not Lean?

### (e) Stated differences (verbatim from `log/CLAIMS.md`, row C108-LW1)

> **Differences from the claim:** (1) only the finite computation is formal; that Lai's Gamma (constant nu-1 = 1) needs loss <= 0 at this entry is the advocate's reading (evidence/lai-nu2-audit C4-C5), not formalized; (2) mu_X is defined by Lai's two formulas (Program 11 l. 46-71), not proved to be the functional of Lai's note; (3) a Gram-type test entry, not a Hankel entry or a valuation of Delta_K; (4) polynomials are List Q, certified by Z_decomp and QR_length; Bernoulli numbers are Mathlib's bernoulli (bernTab_eq, bernFast_eq)

### (f) Reading time: about 12 minutes (Q1-Q3 and Q5 are line-by-line matches; Q4 and Q6 take most of it).

---

## 2. C108-LS1 (passing) and C108-LS2 (conditional): Lai's skip line at s = 11, p = 17 (dossier E23)

Files: `problems/108-zeta-odd-autopsy/evidence/lean_skip/LeanSkip/LaiSkip.lean` (342 lines) and
`LeanSkip/DeltaData.lean` (54 lines); copies `Mathathon/P108/LaiSkip.lean`, `Mathathon/P108/LaiSkipData.lean`.

### (a) Claims

- **LS1 (LEAN-CHECKED).** (a) At K = 40, Lai's Program 05 test `2p − 2 < s·⌊3K/40⌋` skips the outer prime
  p = 17 at s = 11, and 17 is the only outer prime (K/3 < p ≤ K) it skips there. At K = 4·10⁶, every s ≥ 27
  skips every p ≤ K. (b) v_17(S_40) = 24 for ν = 2. (c) The explicit degree-37 polynomial `DeltaLit` has
  17-adic Gauss valuation −271, attained at X⁰. (d) For every s, ν, n, coeff₀(det G_K(X)) = det G_K(0).
- **LS2 (LEAN-CONDITIONAL, sorries `Delta_eq`, `det_G40_zero`).** With G_40, Δ_40 = det G_40 and
  F_40 = S_40 Δ_40 at s = 11, ν = 2, we have v_17(content F_40) = −247 and v_17(F_40(0)) = −247, so F_40 is
  not 17-integral, although Lai's test skips p = 17.

### (b) Lean statements (printed by Lean) and definitions (verbatim)

LS1, passing (axioms `propext, Classical.choice, Quot.sound`; `laiSkips_all_of_ge_27`: `propext, Quot.sound`):
```lean
Mathathon.P108.Skip.laiSkips_11_40 : Nat.Prime 17 ∧
  40 / 3 < 17 ∧
    17 ≤ 40 ∧
      Mathathon.P108.Skip.laiSkips 11 40 17 ∧
        ∀ (p : ℕ), Nat.Prime p → 40 / 3 < p → p ≤ 40 → Mathathon.P108.Skip.laiSkips 11 40 p → p = 17
Mathathon.P108.Skip.laiSkips_all_of_ge_27 : ∀ (s : ℕ),
  27 ≤ s → ∀ p ≤ 4 * 10 ^ 6, Mathathon.P108.Skip.laiSkips s (4 * 10 ^ 6) p
Mathathon.P108.Skip.S_val : padicValRat 17 (Mathathon.P108.Skip.S 2 1) = 24
Mathathon.P108.Skip.DeltaLit_contentVal : Mathathon.P108.Skip.HasContentVal 17 Mathathon.P108.Skip.DeltaLit (-271)
Mathathon.P108.Skip.coeffData_check : Mathathon.P108.Skip.coeffData.all (Mathathon.P108.Skip.checkEntry 17 (-271)) =
  true
Mathathon.P108.Skip.coefQ_zero_val : padicValRat 17 (Mathathon.P108.Skip.coefQ 0) = -271
Mathathon.P108.Skip.Delta_coeff_zero : ∀ (s ν n : ℕ),
  (Mathathon.P108.Skip.Delta s ν n).coeff 0 = ((Mathathon.P108.Skip.G s ν n).map (Polynomial.eval 0)).det
@Mathathon.P108.Skip.padicValRat_of_check : ∀ {p : ℕ} [Fact (Nat.Prime p)] {v z : ℤ} {d a b : ℕ},
  Mathathon.P108.Skip.checkEntry p v (z, d, a, b) = true → ↑z / ↑d ≠ 0 ∧ padicValRat p (↑z / ↑d) = ↑a - ↑b ∧ v ≤ ↑a - ↑b
@Mathathon.P108.Skip.HasContentVal.C_mul : ∀ {p : ℕ} [Fact (Nat.Prime p)] {f : Polynomial ℚ} {v : ℤ},
  Mathathon.P108.Skip.HasContentVal p f v →
    ∀ {c : ℚ}, c ≠ 0 → Mathathon.P108.Skip.HasContentVal p (Polynomial.C c * f) (padicValRat p c + v)
```
`40 / 3` is ℕ division (= 13). The numerals are in ℕ because `p : ℕ`.

LS2, conditional (axioms include `sorryAx`):
```lean
Mathathon.P108.Skip.lai_skip_witness : Mathathon.P108.Skip.laiSkips 11 40 17 ∧
  Mathathon.P108.Skip.HasContentVal 17 (Mathathon.P108.Skip.F 11 2 1) (-247) ∧
    ¬∀ (i : ℕ), 0 ≤ padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff i)
Mathathon.P108.Skip.F40_contentVal17 : Mathathon.P108.Skip.HasContentVal 17 (Mathathon.P108.Skip.F 11 2 1) (-247)
Mathathon.P108.Skip.F40_coeff_zero_val : padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff 0) = -247
Mathathon.P108.Skip.F40_not_integral_at_17 : ¬∀ (i : ℕ), 0 ≤ padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff i)
-- the two sorries (l. 274-275, l. 317-318):
Mathathon.P108.Skip.Delta_eq : Mathathon.P108.Skip.Delta 11 2 1 = Mathathon.P108.Skip.DeltaLit
Mathathon.P108.Skip.det_G40_zero : ((Mathathon.P108.Skip.G 11 2 1).map (Polynomial.eval 0)).det =
  Mathathon.P108.Skip.coefQ 0
```
Dependencies: `lai_skip_witness` and `F40_contentVal17` use `Delta_eq`. `F40_not_integral_at_17` and
`F40_coeff_zero_val` use only `det_G40_zero` (LaiSkip.lean l. 302-340).

Definitions (LaiSkip.lean). `X` is `Polynomial.X`. It plays the role of t inside `D` and `G`'s numerator,
and the role of Lai's X in `muPole`. Lean does not compose the two roles.
```lean
-- l. 53
noncomputable def D (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C ((j : ℚ) ^ 2))
-- l. 56
def H (s k : ℕ) : ℚ := ∑ v ∈ Finset.Icc 1 k, 1 / (v : ℚ) ^ s
-- l. 60-62
def muMono (s e : ℕ) : ℚ :=
  (-1) ^ e * bernoulli (2 * e + 2) * ((2 * e + s).factorial : ℚ) /
    (((2 * e + 2).factorial : ℚ) * ((s - 1).factorial : ℚ))
-- l. 65-66
noncomputable def muPole (s k : ℕ) : ℚ[X] :=
  C ((k : ℚ) ^ (s - 1)) * (X - C (H s k)) + C (1 / (2 * (k : ℚ)) - 1 / ((s : ℚ) - 1))
-- l. 69
def dD (K k : ℕ) : ℚ := ∏ j ∈ (Finset.Icc 1 K).erase k, ((j : ℚ) ^ 2 - (k : ℚ) ^ 2)
-- l. 74-76
noncomputable def muX (s K : ℕ) (f : ℚ[X]) : ℚ[X] :=
  C (∑ e ∈ Finset.range ((f /ₘ D K).natDegree + 1), (f /ₘ D K).coeff e * muMono s e) +
    ∑ k ∈ Finset.Icc 1 K, C (f.eval (-((k : ℚ) ^ 2)) / dD K k) * muPole s k
-- l. 80-81
noncomputable def G (s ν n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] :=
  Matrix.of fun i j => muX s (40 * n) (D (3 * n) ^ ν * X ^ (i.val + j.val))
-- l. 84
noncomputable def Delta (s ν n : ℕ) : ℚ[X] := (G s ν n).det
-- l. 87-90
def S (ν n : ℕ) : ℚ :=
  ((40 * n).factorial : ℚ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) /
    (((3 * n).factorial : ℚ) ^ (2 * ν * (37 * n)) *
      ∏ i ∈ Finset.Icc 1 (37 * n - 1), ((2 * i).factorial : ℚ) ^ 2)
-- l. 93
noncomputable def F (s ν n : ℕ) : ℚ[X] := C (S ν n) * Delta s ν n
-- l. 97-99
def HasContentVal (p : ℕ) (f : ℚ[X]) (v : ℤ) : Prop :=
  f ≠ 0 ∧ (∀ i, f.coeff i ≠ 0 → v ≤ padicValRat p (f.coeff i)) ∧
    ∃ i, f.coeff i ≠ 0 ∧ padicValRat p (f.coeff i) = v
-- l. 103
def laiSkips (s K p : ℕ) : Prop := 2 * p - 2 < s * (3 * K / 40)
-- l. 134-137
def checkEntry (p : ℕ) (v : ℤ) : ℤ × ℕ × ℕ × ℕ → Bool
  | (z, d, a, b) => z != 0 && d != 0 &&
      z.natAbs == p ^ a * (z.natAbs / p ^ a) && (z.natAbs / p ^ a) % p != 0 &&
      d == p ^ b * (d / p ^ b) && (d / p ^ b) % p != 0 && decide (v ≤ (a : ℤ) - b)
-- l. 161-164
def coefQ (i : ℕ) : ℚ :=
  match coeffData[i]? with
  | some (z, d, _, _) => (z : ℚ) / d
  | none => 0
-- l. 167
noncomputable def DeltaLit : ℚ[X] := ∑ i ∈ Finset.range 38, C (coefQ i) * X ^ i
```
`DeltaData.lean` l. 13-14: `def coeffData : List (Int × Nat × Nat × Nat) := [`, followed by 38 tuples
`(num, den, v₁₇ num, v₁₇ den)`, generated by `py/gen_data.py` from `../witness/out/delta_s11_nu2_n1.txt`
(too long to quote: the numbers have hundreds of digits). `coeffData_length` (l. 169) proves there are 38.
Mathlib primitives: `Polynomial` (`X`, `C`, `/ₘ` = `divByMonic`, `eval`, `coeff`, `natDegree`), `Matrix.det`,
`Matrix.map`, `bernoulli`, `Nat.factorial`, `padicValRat`, `Nat.Prime`, ℕ `/` and `-` (truncating).

### (c) Sources (verbatim)

Lai, laichunwing/Irrationality-of-Zeta7-to-Zeta49@e05d19ba `05_master_table.txt`
(`~/mathathon-cache/108/repos/laichunwing_Irrationality-of-Zeta7-to-Zeta49/`):
```python
# l. 35-47
lam_f = 37.0 / 40.0
nu = 2
K_outer = 4 * 10**6

def certified_I_main(s, K_outer):
    N_val = (3 * K_outer) // 40
    h = (37 * K_outer) // 40
    C = s + 2
    total = RIF(0)

    for p in primerange(K_outer // 3 + 1, K_outer + 1):
        if s * N_val > 2 * p - 2:
            continue
# l. 53
        vp = 2 * h * (K_outer // p) - 2 * nu * h * (N_val // p) - 2 * sum_f
```
Lai's note (ai.vixra 2609.0080v1, `~/mathathon-cache/108/lai.txt`, OCR text): Def. 4.2 (11)-(12), PDF p. 4
(l. 165-172), the ζ(5) functional:
```
Definition 4.2 (Functional µX ). For e ≥ 0, set
                                                  (−1)e B2e+2 (2e + 3)(2e + 4)(2e + 5)
                                  µX (te ) :=                                          .                   (11)
                                                                   24
For j ≥ 1, set                             (︃            )︃
                                                   1                            (5)        1  1
                                      µX                      := j 4 (X − Hj ) −             + ,           (12)
                                                t + j2                                     4 2j
```
Def. 5.1-5.2 (27)-(30), PDF p. 6 (l. 315-331):
```
Definition 5.1 (Hankel matrix). For X ∈ C, define the h × h matrix
                                           DN (t)6 ti+j
                                     [︃ (︃              )︃]︃
                           GK (X) := µX                             .                         (27)
                                              DK (t)        0≤i,j<h
...
Definition 5.2 (Determinant and normaliser). Set
                                     ∆K (X) := det GK (X) ∈ Q[X].                             (28)
Also set
                                                   (K!)2h 4h−1
                                      SK :=             h−1
                                                                       ,                      (29)
                                                        ∏︂ (︁      )︁2
                                               (N !)12h       (2i)!
                                                           i=1
and
                                              FK := SK ∆K .                                   (30)
```
The ν-dependence of S_K in Lai's ν = 2 code, laichunwing/Zeta7-is-Irrational@c42a984f `07_outer_integral.txt`
l. 24-26:
```python
def vp_SK_outer(K, p, nu):
    N = (3*K)//40; h = (37*K)//40
    return 2*h*(K//p) - 2*nu*h*(N//p) - 2*sum_floor_2i(K, p)
```
The Gauss valuation Lai uses, Program 11 (c42a984f) l. 127-129:
```python
def vp_G(Delta, p):
    vals = [c.valuation(p) for c in Delta.list() if c != 0]
    return min(vals)
```
The general-s functional is not Lai's. It is the advocate's `evidence/witness/hankel.py` l. 10-15, 19-20:
```
  K = 40n, N = 3n, h = 37n, D_m(t) = prod_{j=1}^m (t + j^2),
  G_K(X)_{ij} = mu_X( D_N(t)^nu t^(i+j) / D_K(t) ),  0 <= i, j < h,
  mu_X(t^e)          = (-1)^e B_{2e+2} (2e+s)! / ((2e+2)! (s-1)!),
  mu_X(1/(t + j^2))  = j^(s-1) (X - H_j^(s)) + 1/(2j) - 1/(s-1),
  Delta_K(X) = det G_K(X),
  S_K = (K!)^(2h) 4^(h-1) / ((N!)^(2 nu h) prod_{i=1}^{h-1} ((2i)!)^2),   F_K = S_K Delta_K.
...
For general odd s they follow from the weight w_s(y) = 2(2pi)^(s-1)/(s-1)! y^s sum_l l^(s-1) e^(-2 pi l y)
(our derivation, checked numerically in check_functional.py; HEURISTIC for s not in {5, 7}).
```
At s = 7 the same formulas are Program 11 l. 59-60 and l. 63-71 (quoted in §1 (c)).

### (d) Checklist

1. Is `laiSkips s K p` (l. 103, ℕ arithmetic) Program 05 l. 40 and l. 46 (`N_val = (3*K)//40`, skip iff
   `s * N_val > 2*p - 2`)? (ℕ truncation in `2 * p - 2` matters only for p ≤ 1, which is not prime.)
2. Is "outer prime" `40 / 3 < p ∧ p ≤ 40` (ℕ: 13 < p ≤ 40) the range `primerange(K//3 + 1, K + 1)` of
   Program 05 l. 45?
3. Is `S ν n` (l. 87-90) Lai (29) with (N!)^{12h} written as (N!)^{2νh}, which is (29) at ν = 6 and agrees with
   the valuation Lai's ν = 2 code uses (Program 07 l. 26, Program 05 l. 53: −2νh⌊N/p⌋)?
4. At s = 5 and s = 7, are `muMono s e`, `muPole s k` (l. 60-66) Lai (11)-(12) and Program 11 l. 59-60, 70-71?
   (Check: (2e+s)!/((2e+2)!(s−1)!) = (2e+3)(2e+4)(2e+5)/24 at s = 5; the pole constant is 1/(2k) − 1/(s−1).
   At s = 11 these are hankel.py's formulas, a HEURISTIC: stated difference (2) of LS2.)
5. Is `muX s K f` (l. 74-76) Lai's extension (13)-(14)? It takes the polynomial part `f /ₘ D K` and residues
   `f(−k²)/dD K k`. Here f(−k²) = R(−k²) because D_K(−k²) = 0, and dD K k = ∏_{j≠k}(j²−k²) = D_K'(−k²), as in
   Program 11 l. 49 and l. 66.
6. Is `G s ν n` (l. 80-81) Lai (27) with D_N^6 → D_N^ν, i, j < h = 37n (Program 11 l. 48:
   `D_N_nu * t**(i + j)`), and are `Delta` and `F` (l. 84, 93) Lai (28) and (30)?
7. Is `HasContentVal p f v` (l. 97-99) Program 11's `vp_G` = v (min over the nonzero coefficients), plus f ≠ 0?
   Is "F_40 is 17-integral" faithfully `∀ i, 0 ≤ padicValRat 17 (coeff i)`? (A zero coefficient gives 0.)
8. LS1 (c) concerns `DeltaLit`, an explicit polynomial (38 coefficients from `coeffData`), and not det G_40.
   Do you agree that only `Delta_eq` (sorry) links them, so that LS1 (c) is not a statement about Lai's Δ_40?

### (e) Stated differences (verbatim from `log/CLAIMS.md`)

C108-LS1:
> **Differences from the claim:** (c) is about the explicit polynomial, not about det G_40 (that identity is the sorry of C108-LS2); "content valuation" is the predicate HasContentVal (min over nonzero coefficients of padicValRat), since Mathlib's Polynomial.content is trivial over Q; the skip count 180,763 is not formalized

C108-LS2:
> **Differences from the claim:** (1) the determinant is not formal (the two sorries); (2) mu_X at s = 11 is the advocate's general-s derivation (hankel.py: HEURISTIC for s not in {5, 7}; my float check at s = 11 agrees to 9-20 digits), not shown to be Lai's zeta(11) functional; (3) only K = 40: that Lai's Program 05 (run at K = 4*10^6) needs v_p(F_K) >= 0 for skipped p at every K is the advocate's reading (W4), not formalized; K = 80 and s = 13..49 not formalized

### (f) Reading time: about 13 minutes (Q1-Q3 take 4; Q4-Q6 take 6; LS2 stays LEAN-CONDITIONAL whatever you answer).

### (g) Update, formalizer 4 (EVENT WORK, Claude Opus 5.5, Sat 01:55 PT): v4.33.1 run, and `det_G40_zero` proved

**v4.33.1.** lean_check on v4.33.1 (Sat 01:47-01:52 PT, `lean_skip/log/LEAN_CHECK.md`) printed every §2 statement
quoted in (b) again: each is identical to (b) up to line breaks (checked by script, whitespace-normalized), with the
same axioms. No Lean source of (b) changed in the port; so (b) holds verbatim on v4.33.1.

**`det_G40_zero` is now proved** (`lean_skip/LeanSkip/DetG0*.lean`; `lean_skip/README.md`, section "Formalizer 4"), so
two LS2 declarations are LEAN-CHECKED, new row **C108-LS3** in `log/CLAIMS.md`, axioms `propext, Classical.choice,
Quot.sound`:
```lean
Mathathon.P108.Skip.det_G40_zero : ((Mathathon.P108.Skip.G 11 2 1).map (Polynomial.eval 0)).det =
  Mathathon.P108.Skip.coefQ 0
Mathathon.P108.Skip.F40_coeff_zero_val : padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff 0) = -247
Mathathon.P108.Skip.F40_not_integral_at_17 : ¬∀ (i : ℕ), 0 ≤ padicValRat 17 ((Mathathon.P108.Skip.F 11 2 1).coeff i)
```
`lai_skip_witness`, `F40_contentVal17` and `Delta40_contentVal17` still use `Delta_eq` (sorry): LEAN-CONDITIONAL.

**What a human must compare for LS3.** No new definition enters these statements: they use only `G`, `muX`,
`muMono`, `muPole`, `dD`, `D`, `H`, `S`, `F`, `coefQ`, quoted in (b). So the comparison is Q3-Q7 of (d), with the
sources quoted in (c): `muMono`, `muPole` against Lai (11)-(12) (with the s = 11 caveat, stated difference (2)),
`muX` against Lai's extension (13)-(14), `G` against (27) with D_N^6 → D_N^ν, `S` and `F` against (29), (30), and
"not 17-integral" as `¬ ∀ i, 0 ≤ padicValRat 17 (coeff i)` (Q7). The helpers in `DetG0*.lean` (`ofL`, `qrSeq`, `g0C`, `ldlAux`, …) occur only in
proofs. `DetG0.lean` repeats the definitions of (b) verbatim, because `LaiSkip.lean` imports it; the proof
`det_G40_zero := DetG0.det_G40_zero'` type-checks only because the kernel finds the two statements definitionally
equal, so the copies cannot drift unnoticed. Reading time for LS3: Q3-Q7 as in (f), about 7 minutes.

---

## 3. Criterion declarations that pass `lean_check` (C108-LC1..LC6, dossier E27)

Files: `problems/108-zeta-odd-autopsy/evidence/lean_criterion/LeanCriterion/{InnerShift,Integrable,OuterDefs,
OuterValues,OuterValues2,SStep,SStepTable,OffsetGap}.lean`.

**What exists.** `lean_check` passed on 49 declarations (Fri 23:05-23:06 PT, per the dossier and EVENT_LOG
23:09; the per-folder log now holds only the orchestrator's 23:11 re-run of 3 of them). I re-printed all 49:
all have axioms `propext, Classical.choice, Quot.sound`. `log/CLAIMS.md` has rows **C108-LC1..LC6**.
LC5 and LC6 were appended by formalizer 3 while this sheet was being written (present at 23:20 PT). Every
declaration of the 49 belongs to one of LC1..LC6, or is a helper of LC1 (`measurable_innerR`, `bdd_innerR`).
Nothing in this section is pending.

**Automatic cross-check (done for you).** The 20 values `Iout s ν (3/40)` and the 15 s-steps proved in Lean
are identical, as exact rationals, to the advocate's `criterion5/sstep_exact.out`. Each Lean s-step also equals
2·(37/40)/3 + ΔI_out (0 mismatches). Script:
`/private/tmp/claude-501/-Users-jack-Library-Application-Support-Claude-scratch-workspaces-f84c0719-1fc3-4a02-8618-d18d9fee307c-41484cae-f9fd-4f1a-aadb-82b393529446-scratch-2026-11-13-630807/06c2099f-dc87-4dcb-a268-9095e8abfc2a/scratchpad/humancheck/xcheck.py`
(Lean output against `sstep_exact.out`). This checks Lean against the advocate's code. It does not check either
of them against Fauzan.

### 3.0 Shared definitions (verbatim)

InnerShift.lean (ℝ throughout; `⌊·⌋` is `Int.floor` cast to ℝ):
```lean
-- l. 39
def ell (x z : ℝ) : ℝ := (⌊x - z⌋ : ℝ) + (⌊x + z⌋ : ℝ) + 1
-- l. 106
def Hc (ν α : ℝ) : ℝ := (1 - α) + ν / 2 * α
-- l. 109
def Tc (ν α x : ℝ) : ℝ := (⌊2 * Hc ν α * x⌋ : ℝ)
-- l. 112
def sigmaC (ν α x : ℝ) : ℝ := Hc ν α * x - Tc ν α x / 2
-- l. 115
def nplus (x : ℝ) : ℝ := (2 * x - (⌊2 * x⌋ : ℝ)) / 2
-- l. 118-119
def gammaIntegrand (s ν α x z : ℝ) : ℝ :=
  (Tc ν α x - ν / 2 * ell (α * x) z) * (Tc ν α x + ν / 2 * ell (α * x) z - ell x z - s)
-- l. 123-125
def innerGamma (s ν α x : ℝ) : ℝ :=
  (∫ z in (0:ℝ)..(1/2), gammaIntegrand s ν α x z)
    + sigmaC ν α x * (2 * Tc ν α x - (⌊2 * x⌋ : ℝ) - s) + max (sigmaC ν α x - nplus x) 0
-- l. 128
def Jfun (u : ℝ) : ℝ := (⌊2 * u⌋ : ℝ) * u - (⌊2 * u⌋ : ℝ) * ((⌊2 * u⌋ : ℝ) + 1) / 4
-- l. 131-132
def innerN (ν α x : ℝ) : ℝ :=
  2 * (1 - α) * x * (⌊x⌋ : ℝ) - 2 * ν * (1 - α) * x * (⌊α * x⌋ : ℝ) - 2 * Jfun ((1 - α) * x)
-- l. 135
def innerR (s ν α x : ℝ) : ℝ := -innerGamma s ν α x - innerN ν α x
```
Integrable.lean l. 20: `def BddOn {X : Type*} (f : X → ℝ) (S : Set X) : Prop := ∃ C, ∀ x ∈ S, |f x| ≤ C`.

OuterDefs.lean (`⌊·⌋₊` is `Nat.floor`):
```lean
-- l. 39-40
def cRem (s ν : ℝ) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (l - 2), max 0 ((l : ℝ) + s - 1 - ν - 2 * (i : ℝ))
-- l. 44-45
def zRem (s ν : ℝ) (l : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (l - 2), if (l : ℝ) + s - 1 - ν - 2 * (i : ℝ) ≤ 0 then (1 : ℝ) else 0
-- l. 48-64
def gOuter (s ν α y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y ≤ 1 then
    let k : ℕ := ⌊1 / y⌋₊
    let v : ℝ := 1 - (k : ℝ) * y
    let u : ℝ := max 0 (α + v - y)
    let mv : ℝ := min α v
    let d0 : ℝ := α - mv
    let d1 : ℝ := mv - u
    let d2 : ℝ := u
    let cost : ℝ := (s + 2) * ((1 - y) - (d0 * (2 * (k : ℝ) - 2) + d1 * (2 * (k : ℝ) + 1 - 2)
        + d2 * (2 * (k : ℝ) + 2 - 2)))
      + (d0 * cRem s ν (2 * k) + d1 * cRem s ν (2 * k + 1) + d2 * cRem s ν (2 * k + 2))
    let zz : ℝ := (y - 2 * α)
      + (d0 * zRem s ν (2 * k) + d1 * zRem s ν (2 * k + 1) + d2 * zRem s ν (2 * k + 2))
    let r : ℝ := min (1 - α) (max 0 (1 + (ν - 2) * α - (s - 1) / 2 * y))
    cost + min r zz
  else 0
-- l. 67-68
def legendreTerm (α y : ℝ) : ℝ :=
  -2 * (1 - α) * (⌊1 / y⌋₊ : ℝ) + ∑ j ∈ Finset.range 6, max (2 * (1 - α) - ((j : ℝ) + 1) * y) 0
-- l. 71
def Tout (s ν α y : ℝ) : ℝ := gOuter s ν α y + legendreTerm α y
-- l. 75
def Iout (s ν α : ℝ) : ℝ := ∫ y in (1 / 3 : ℝ)..(2 * (1 - α)), Tout s ν α y
```
SStep.lean l. 34-35:
```lean
def thetaPkg (s ν α M U : ℝ) : ℝ :=
  U + Iout s ν α + (s + 1) * (1 - α) / M + ∫ x in (3:ℝ)..M, innerR s ν α x / x ^ 3
```
Mathlib primitives: `Int.floor`, `Nat.floor`, `intervalIntegral` (`∫ x in a..b`; it is 0 for a
non-integrable integrand, so watch for junk values), `IntervalIntegrable`, `Measurable`, `max`, `min`,
`Finset.sum`. Junk values are excluded here: `gammaIntegrand` is proved integrable in z (InnerShift l. 137),
`innerR/x³` on [3, M] (`innerR_div_intervalIntegrable`), and every `Iout` value is proved piece by piece by
`piece_integral` (OuterDefs l. 99), which also yields integrability.

### 3.0 Sources (verbatim)

Fauzan (Zenodo 22826419, `~/mathathon-cache/108/fauzan.txt` l. 754-774, PDF p. 14), the (s, ν) = (5, 6) case:
```
                    ℓ(x, z) = ⌊x − z⌋ + ⌊x + z⌋ + 1,            b(x, z) = 3ℓ(αx, z).
In the following formulas,
                 T = ⌊2Hx⌋ ,       s = Hx − T /2,        q = ⌊2x⌋ ,   n+ = (2x − q)/2.
Define
                              ∫︂ 1/2
                     Γ(x) =            (T − b(x, z))(T + b(x, z) − ℓ(x, z) − 5) dz
                               0
                              + s(2T − q − 5) + (s − n+ )+ .                                 (5.4)
...
                                           m(m + 1)
                              J(u) = mu −            ,    m = ⌊2u⌋ ,
                                               4
                             N (x) = 2λx ⌊x⌋ − 12λx ⌊αx⌋ − 2J(λx),                           (5.5)
                             R(x) = −Γ(x) − N (x).                                           (5.6)
```
Fauzan l. 820-834, PDF p. 15 (excerpt):
```
                                                         5
                                                        ∑︂
                        −vp (SK ) = K ⎝−2λ ⌊1/y⌋ +            (2λ − jy)+ ⎠ + O(1).
                                                        j=1
The relevant integral is
                      ∫︂ 2λ                                  5
                              ⎝R0 (y) − d(y) − 2λ ⌊1/y⌋ +
                                                            ∑︂                                 127751
             Iout =                                               (2λ − jy)+ ⎠ dy =                   .      (5.10)
                       1/3                                  j=1
                                                                                               96000
```
The (s, ν) generalisation is the advocate's (PROOF-DRAFT), `criterion5/derivation.md` (sha256 6af34453…, the
version the Lean files cite, unchanged at 23:10 PT), l. 62-63 (2.2):
```
  Γ_(s,ν)(x) = ∫_0^(1/2) (T − b)(T + b − ℓ − s) dz + σ(2T − ⌊2x⌋ − s) + (σ − n₊)₊,  b = (ν/2)ℓ(αx, z),
  N_ν(x) = 2λx⌊x⌋ − 2νλx⌊αx⌋ − 2J(λx),  R_(s,ν) = −Γ_(s,ν) − N_ν,
```
l. 65: "with T = ⌊2Hx⌋, σ = Hx − T/2, n₊ = {2x}/2, ℓ, J as in Fauzan." l. 86-89 (§3):
```
  g_(s,ν)(y) = (s+2)[(1 − y) − Σ_ℓ dens(ℓ)(ℓ−2)] + Σ_ℓ dens(ℓ)c¹(ℓ) + min(r̂, ẑ),
  ẑ = y − 2α + Σ_ℓ dens(ℓ)z¹(ℓ),  r̂ = min(λ, (1 + (ν−2)α − ry)₊),

  I_out(s, ν) = ∫_(1/3)^(2λ) [g_(s,ν)(y) − 2λ⌊1/y⌋ + Σ_(j≥1)(2λ − jy)₊] dy.
```
with l. 82: "c¹(ℓ) = Σ_(i=0)^(ℓ−3) max(0, ℓ + s − 1 − ν − 2i), z¹(ℓ) = 1 + #{i ≤ ℓ−3 : ℓ + s − 1 − ν − 2i ≤ 0}",
and l. 108 (§5): "I_out through (s+2) and r = (s−1)/2". §5, l. 106:
"**Θ(s, ν, α; M, ρ) = U(ν, α; ρ) + I_out(s, ν, α) + (s+1)λ/M + ∫_3^M x^(−2)[(s−1)λ + 2λ{x} − 2νλ{αx}] dx + ∫_3^M Q_ν(x)x^(−3) dx.**"
The code the Lean transcribes, `criterion5/general_sq.py` (`AL` = 3/40, `LAM` = 37/40 are fixed there):
```python
# l. 46-55
def c_rem(s, nu, l):
    return sum(max(0, l + s - 1 - nu - 2 * i) for i in range(l - 2))
def z_rem(s, nu, l):
    return 1 + sum(1 for i in range(l - 2) if l + s - 1 - nu - 2 * i <= 0)
# l. 67-83
def g_general(s, nu, y):
    if not (Fr(1, 3) < y <= 1):
        return Fr(0)
    k = fl(1 / y)                       # 2 on (1/3, 1/2], 1 on (1/2, 1]
    v = 1 - k * y
    u = max(Fr(0), AL + v - y)          # removed classes with both extra members
    mv = min(AL, v)
    base = 2 * k                        # members a, p-a (k=1) or a, p-a, p+a, 2p-a (k=2)
    dens = {base: AL - mv, base + 1: mv - u, base + 2: u}      # removed classes by l (per K)
    poles_above = (1 - y)               # j in (p, K], minus the zero class j = 2p (k=2): (1-y)K + O(1)
    rem_above = sum(dn * (l - 2) for l, dn in dens.items())
    cost = (s + 2) * (poles_above - rem_above) + sum(dn * c_rem(s, nu, l) for l, dn in dens.items())
    # unremoved classes: (m - N)/K = y/2 - alpha of them, two zero weights each
    zz = 2 * (y / 2 - AL) + sum(dn * z_rem(s, nu, l) for l, dn in dens.items())
    r = min(LAM, max(Fr(0), 1 + (nu - 2) * AL - Fr(s - 1, 2) * y))
    return cost + min(r, zz)
# l. 92-94
    def Tout(self, y):
        scal = -2 * LAM * fl(1 / y) + sum(max(2 * LAM - j * y, Fr(0)) for j in range(1, 7))
        return g_general(self.s, self.nu, y) + scal
```
(The docstrings at l. 47-48, 53-54 and 68 are left out; the code lines are verbatim.)

### 3.0 Checklist (shared definitions; answer once for §3.1-3.5)

1. Is `innerGamma`/`innerN`/`innerR` (l. 118-135) Fauzan (5.4)-(5.6) after 3 → ν/2 (in b and in H), 5 → s,
   12 → 2ν, i.e. derivation.md (2.2)? (Fauzan's "s = Hx − T/2" is `sigmaC`; his q = ⌊2x⌋, n₊ = (2x − q)/2.)
2. Is `Hc ν α = λ + (ν/2)α` Fauzan's H? (At ν = 6, α = 3/40: 37/40 + 9/40 = 23/20, Lai (8).)
3. Is `gOuter` (OuterDefs l. 48-64) `g_general` with `AL` → α and `LAM` → 1 − α? (Line by line: `zz` is
   2(y/2 − α) + … = (y − 2α) + …; `range(l - 2)` is `Finset.range (l - 2)`; `fl(1/y)` is `⌊1/y⌋₊` for y > 0.)
4. Is `legendreTerm` (l. 67-68) Fauzan's −2λ⌊1/y⌋ + Σ_{j=1}^{5}(2λ − jy)₊? Lean and the code sum j = 1..6,
   and the j = 6 term is (2λ − 6y)₊ = 0 for y ≥ 1/3, λ ≤ 1.
5. Is `Iout` (l. 75) ∫_{1/3}^{2λ} T_out, as in Fauzan (5.10), and does the anchor `Iout_5_6 = 127751/96000`
   reproduce (5.10)?
6. Is `thetaPkg` (SStep l. 34-35) derivation.md §5's Θ, with U(ν, α; ρ) replaced by a free real U and the last
   two integrals kept as the single ∫_3^M R_(s,ν)/x³ (they are equal by Prop. 1, which is not formalized)?
7. The hypotheses are only `3 ≤ M` (derivation.md: M ≥ 40) and real s, ν, α (derivation.md: odd s, even
   ν ≤ 10, α ∈ (0, 1/3)). Do you agree these only make the Lean theorems more general?

### 3.1 C108-LC1: the inner s-shift (LEAN-CHECKED)

(a) For all real s, s′, ν, α, x: R_(s,ν)(x) − R_(s′,ν)(x) = (s − s′)λx. Also ∫_0^{1/2} ℓ(y, z) dz = y, the
integral identity ∫_3^M (R_(s+2) − R_s)/x³ = 2λ(1/3 − 1/M) for M ≥ 3, integrability of R/x³ on [3, M], and the
exact inner-plus-crude cost 2λ/3 per step.

(b) Printed statements:
```lean
Mathathon.P108.innerR_shift : ∀ (s s' ν α x : ℝ),
  Mathathon.P108.innerR s ν α x - Mathathon.P108.innerR s' ν α x = (s - s') * (1 - α) * x
Mathathon.P108.integral_ell : ∀ (y : ℝ), ∫ (z : ℝ) in 0..1 / 2, Mathathon.P108.ell y z = y
Mathathon.P108.inner_sstep_integral : ∀ (s ν α M : ℝ),
  3 ≤ M →
    ∫ (x : ℝ) in 3..M, (Mathathon.P108.innerR (s + 2) ν α x - Mathathon.P108.innerR s ν α x) / x ^ 3 =
      2 * (1 - α) * (1 / 3 - 1 / M)
Mathathon.P108.inner_crude_sstep : ∀ (s ν α M : ℝ),
  3 ≤ M →
    IntervalIntegrable (fun x => Mathathon.P108.innerR s ν α x / x ^ 3) MeasureTheory.volume 3 M →
      ((s + 2 + 1) * (1 - α) / M + ∫ (x : ℝ) in 3..M, Mathathon.P108.innerR (s + 2) ν α x / x ^ 3) -
          ((s + 1) * (1 - α) / M + ∫ (x : ℝ) in 3..M, Mathathon.P108.innerR s ν α x / x ^ 3) =
        2 * (1 - α) / 3
Mathathon.P108.innerR_div_intervalIntegrable : ∀ (s ν α M : ℝ),
  3 ≤ M → IntervalIntegrable (fun x => Mathathon.P108.innerR s ν α x / x ^ 3) MeasureTheory.volume 3 M
Mathathon.P108.measurable_innerR : ∀ (s ν α : ℝ), Measurable fun x => Mathathon.P108.innerR s ν α x
Mathathon.P108.bdd_innerR : ∀ (s ν α M : ℝ),
  3 ≤ M → Mathathon.P108.BddOn (fun x => Mathathon.P108.innerR s ν α x) (Set.Icc 3 M)
```
(c) derivation.md l. 67-70 (Prop. 1), "In particular **R_(s,ν)(x) − R_(s′,ν)(x) = (s − s′)λx exactly**", and
l. 74: "**Corollary (inner s-cost).** For every M ≥ 40: ∫_3^M R_(s+2,ν)x^(−3) dx − ∫_3^M R_(s,ν)x^(−3) dx =
2λ(1/3 − 1/M). … **Together, the primes p ≤ K/3 cost exactly 2λ/3 per step s → s + 2, for every M.**"

(d) Extra questions: (i) `inner_crude_sstep` keeps the hypothesis `hint`, which `innerR_div_intervalIntegrable`
discharges. Do you accept the pair as the corollary? (ii) Is the crude term `(s + 1)(1 − α)/M` derivation.md's
"(s+1)λ/M"?

(e) Verbatim from CLAIMS C108-LC1:
> **Differences from the claim:** R is defined by the advocate's formula (a transcription of derivation.md (2.2) and theta.py Pkg.R reading S); that this formula is the (s, nu) form of Fauzan's inner bound is E13's PROOF-DRAFT, not formalized; parameters are real, no parity or range assumed (more general than the claim)

(f) About 5 minutes (most of it is §3.0 Q1-Q2).

### 3.2 C108-LC2: five exact outer integrals at α = 3/40 (LEAN-CHECKED)

(a) I_out(5,6) = 127751/96000, I_out(7,6) = 27071/16000, I_out(7,2) = 31511/16000, I_out(7,8) = 453803/288000,
I_out(5,8) = 125021/96000.

(b) Printed statements (OuterValues.lean l. 67, 126, 178, 240, 309):
```lean
Mathathon.P108.Iout_5_6 : Mathathon.P108.Iout 5 6 (3 / 40) = 127751 / 96000
Mathathon.P108.Iout_7_6 : Mathathon.P108.Iout 7 6 (3 / 40) = 27071 / 16000
Mathathon.P108.Iout_7_2 : Mathathon.P108.Iout 7 2 (3 / 40) = 31511 / 16000
Mathathon.P108.Iout_7_8 : Mathathon.P108.Iout 7 8 (3 / 40) = 453803 / 288000
Mathathon.P108.Iout_5_8 : Mathathon.P108.Iout 5 8 (3 / 40) = 125021 / 96000
```
(c) Fauzan (5.10), p. 15 (quoted in §3.0): 127751/96000 at (5, 6). The 7-8 value is our prior audit's
`ZetaSeven.outerIntegral_value` (prior work, [team handle]/zeta7-irrational@be55b3a4). The others are the advocate's
`sstep_exact.out` (identical, by the cross-check above).

(d) Extra question: does `Iout_5_6` = Fauzan (5.10) (§3.0 Q5) convince you that `gOuter`'s rank term
min(r̂, ẑ) is read as Fauzan's R_0 − d (Fauzan uses min(r, z); Zeta5's Lean uses r, +9/640)?

(e) Verbatim from CLAIMS C108-LC2:
> **Differences:** formulas transcribed from the advocate's code (their derivation from Fauzan (4.10)-(4.14) is PROOF-DRAFT); Legendre sum truncated at j = 6 as in the code (the dropped terms vanish for y >= 1/3); alpha = 3/40 only; uses min(r, z) as Fauzan does (Zeta5's Lean uses r, +9/640 at (5,6))

(f) About 3 minutes after §3.0.

### 3.3 C108-LC3: Corollary 4, the general s-step (LEAN-CHECKED)

(a) For all real s, ν, α, U and every M ≥ 3: Θ(s+2) − Θ(s) = 2λ/3 + I_out(s+2) − I_out(s).

(b)
```lean
Mathathon.P108.thetaPkg_sstep : ∀ (s ν α M U : ℝ),
  3 ≤ M →
    Mathathon.P108.thetaPkg (s + 2) ν α M U - Mathathon.P108.thetaPkg s ν α M U =
      2 * (1 - α) / 3 + (Mathathon.P108.Iout (s + 2) ν α - Mathathon.P108.Iout s ν α)
```
(c) derivation.md l. 115-117: "**Corollary 4 (the s-step; PROOF-DRAFT, exact values COMPUTED).** For fixed
(ν, α) and every M ≥ 40 and ρ, Θ(s+2, ν; M, ρ) − Θ(s, ν; M, ρ) = 2λ/3 + I_out(s+2, ν) − I_out(s, ν),
independent of M and of ρ."

(d) Extra question: the same U appears on both sides. Do you accept that U(ν, α; ρ) does not depend on s?
(Lean cannot check this; see (e).)

(e) Verbatim from CLAIMS C108-LC3:
> **Differences:** U is a free real number (the analytic bound U(nu; rho) = lam M_0 - I(rho) + C*(nu) is not formalized; that it does not depend on s is Xu's statement, which is why the same U appears on both sides); R and I_out as in C108-LC1, LC2

(f) About 2 minutes.

### 3.4 C108-LC4: E14's exact s-steps 5 → 7 at ν = 6, 8 (LEAN-CHECKED)

(b)
```lean
Mathathon.P108.theta_sstep_7_6 : ∀ (M U : ℝ),
  3 ≤ M → Mathathon.P108.thetaPkg 7 6 (3 / 40) M U - Mathathon.P108.thetaPkg 5 6 (3 / 40) M U = 751 / 768
Mathathon.P108.theta_sstep_7_8 : ∀ (M U : ℝ),
  3 ≤ M → Mathathon.P108.thetaPkg 7 8 (3 / 40) M U - Mathathon.P108.thetaPkg 5 8 (3 / 40) M U = 12817 / 14400
Mathathon.P108.sstep_value_nu6 : 2 * (1 - 3 / 40) / 3 +
    (Mathathon.P108.Iout 7 6 (3 / 40) - Mathathon.P108.Iout 5 6 (3 / 40)) =
  751 / 768
Mathathon.P108.sstep_value_nu8 : 2 * (1 - 3 / 40) / 3 +
    (Mathathon.P108.Iout 7 8 (3 / 40) - Mathathon.P108.Iout 5 8 (3 / 40)) =
  12817 / 14400
```
(c) derivation.md l. 117: "At α = 3/40 (sstep_exact.out): ν = 6, s = 5 → 7: **751/768 ≈ 0.9779**; ν = 8, 5 → 7:
12817/14400 ≈ 0.8901". `sstep_exact.out` l. 9 and l. 12 give the same.

(e) Verbatim from CLAIMS C108-LC4: "**Differences:** as C108-LC3".

(f) About 1 minute.

### 3.5 C108-LC5 (the 15 s-steps table) and C108-LC6 (the offset gap) (LEAN-CHECKED)

(a) LC5: for every M ≥ 3 and real U, Θ(s+2, ν) − Θ(s, ν) at α = 3/40 equals the 15 exact values of
`sstep_exact.out` (ν ∈ {2,4,6,8,10}, s ∈ {3,5,7}), from 20 exact I_out(s, ν). LC6: for all real c, c′, ν, α
and M ≥ 3, ∫_3^M R_(c,ν)/x³ − ∫_3^M R_(c′,ν)/x³ = (c − c′)λ(1/3 − 1/M). At (7 against 1, ν = 2, α = 3/40,
M = 200) the gap is 21867/12000.

(b) LC6, the offset gap (OffsetGap.lean l. 26-28, 53-55):
```lean
Mathathon.P108.inner_integral_shift : ∀ (c c' ν α M : ℝ),
  3 ≤ M →
    (∫ (x : ℝ) in 3..M, Mathathon.P108.innerR c ν α x / x ^ 3) -
        ∫ (x : ℝ) in 3..M, Mathathon.P108.innerR c' ν α x / x ^ 3 =
      (c - c') * (1 - α) * (1 / 3 - 1 / M)
Mathathon.P108.lai_offset_gap_7_2 : (∫ (x : ℝ) in 3..200, Mathathon.P108.innerR 7 2 (3 / 40) x / x ^ 3) -
    ∫ (x : ℝ) in 3..200, Mathathon.P108.innerR 1 2 (3 / 40) x / x ^ 3 =
  21867 / 12000
```
LC5, the table (OuterValues2.lean, SStepTable.lean l. 19-123). There are 15 more `Iout s ν (3/40) = q`, at
(s, ν) ∈ {3,5,9}×{2} ∪ {3,5,7,9}×{4} ∪ {3,9}×{6} ∪ {3,9}×{8} ∪ {3,5,7,9}×{10}, and 15
`theta_sstep_{3_5,5_7,7_9}_nu{2,4,6,8,10}`, each of the form
`∀ (M U : ℝ), 3 ≤ M → thetaPkg (s+2) ν (3 / 40) M U - thetaPkg s ν (3 / 40) M U = q`. All 30 printed statements
are in
`/private/tmp/claude-501/-Users-jack-Library-Application-Support-Claude-scratch-workspaces-f84c0719-1fc3-4a02-8618-d18d9fee307c-41484cae-f9fd-4f1a-aadb-82b393529446-scratch-2026-11-13-630807/06c2099f-dc87-4dcb-a268-9095e8abfc2a/scratchpad/humancheck/AxC.out`.
All 30 values equal `criterion5/sstep_exact.out` (cross-check above). Example:
```lean
Mathathon.P108.theta_sstep_3_5_nu2 : ∀ (M U : ℝ),
  3 ≤ M → Mathathon.P108.thetaPkg 5 2 (3 / 40) M U - Mathathon.P108.thetaPkg 3 2 (3 / 40) M U = 52213 / 57600
```
(c) The offset gap uses `evidence/lai-nu2-audit/README.md` (C3d, C7: A_200 = 3.6428078823 with constant 7
against 1.8205578823 with Lai's constant 1). The table comes from `criterion5/sstep_exact.out` l. 2-16.

(d) (i) In `lai_offset_gap_7_2`, `innerR 1 2 (3/40)` stands for Lai's Program 06/08 inner function (constant
ν − 1 = 1). Do you accept that this is the audit's reading and not a Lean fact? (ii) Is 21867/12000 =
6·(37/40)·(197/600)? (Check: 6·37·197 = 43734 and 40·600 = 24000, so the product is 43734/24000 =
21867/12000.)

(e) Verbatim from CLAIMS C108-LC5:
> **Differences:** as C108-LC2 and LC3 (advocate's formulas; U free; alpha = 3/40 only)

Verbatim from CLAIMS C108-LC6:
> **Differences:** that innerR 1 2 (3/40) is the inner function of Lai's Programs 06/08 (constant nu-1, N coefficient 2 nu) is the audit's reading of his code (C3d), not checked in Lean; the A_200 values themselves are COMPUTED (Python), only their difference is Lean-checked

(f) About 4 minutes.

### 3.6 C108-LC7: the ν = 8 rescue arithmetic at (5, 8) (LEAN-CHECKED; section added by the orchestrator, Sat 08:32 PT)

(a) E60. At α = 3/40, on (1/3, 17/40] Proposition A's outer weight y·R_(5,8)(1/y) lies strictly below the package's
T_out(5,8) and touches it at 17/40. The gain is ∫_{1/3}^{17/40} (T_out − y·R(1/y)) dy = 1159/28800, and the new outer
integral is I_out(5,8) − gain = 363473/288000 (= 125021/96000 − 1159/28800).

(b) Printed statements. They are in the root project, `Mathathon/P108/OuterValues58.lean`, copied from the probe's
`lean_criterion/LeanCriterion/OuterValues58.lean` with only the two import lines changed. Gate PASS at the root,
Sat 08:30 PT; axioms `propext, Classical.choice, Quot.sound`.
```lean
Mathathon.P108.gain58_formal : ∫ (y : ℝ) in 1 / 3..17 / 40,
    Mathathon.P108.Tout 5 8 (3 / 40) y - y * Mathathon.P108.innerR 5 8 (3 / 40) (1 / y) =
  1159 / 28800
Mathathon.P108.Iout_new_5_8 : Mathathon.P108.Iout 5 8 (3 / 40) -
    ∫ (y : ℝ) in 1 / 3..17 / 40, Mathathon.P108.Tout 5 8 (3 / 40) y - y * Mathathon.P108.innerR 5 8 (3 / 40) (1 / y) =
  363473 / 288000
Mathathon.P108.gain58_pos : ∀ y ∈ Set.Ioo (1 / 3) (17 / 40),
  y * Mathathon.P108.innerR 5 8 (3 / 40) (1 / y) < Mathathon.P108.Tout 5 8 (3 / 40) y
Mathathon.P108.gain58_end : 17 / 40 * Mathathon.P108.innerR 5 8 (3 / 40) (1 / (17 / 40)) =
  Mathathon.P108.Tout 5 8 (3 / 40) (17 / 40)
Mathathon.P108.IoutNew58_formal : (∫ (y : ℝ) in 1 / 3..17 / 40, y * Mathathon.P108.innerR 5 8 (3 / 40) (1 / y)) +
    ∫ (y : ℝ) in 17 / 40..2 * (1 - 3 / 40), Mathathon.P108.Tout 5 8 (3 / 40) y =
  363473 / 288000
```
`Tout` and `Iout` are the §3.0 definitions (OuterDefs.lean), and `innerR` is §3.1's (InnerShift.lean). Nothing new
is defined for the statements. The file's own piecewise-affine `TnewA58` and `ToutPkg58` are proved equal to
`y * innerR 5 8 (3/40) (1/y)` and `Tout 5 8 (3/40) y` on (1/3, 17/40], so no piece is trusted from Python.

(c) Source: `nu8_rescue/derive_fauzan-residue/derivation.md`, Proposition A and its "Consequence". There, for
K/3 < p ≤ 17K/40, i.e. y = p/K ∈ (1/3, 17/40], the outer weight becomes y·R_(5,8)(1/y), with γ* = 17/40.
`residue58.py integral` gives 1159/28800 (exact rationals).

(d) Questions.
1. Is `y * innerR 5 8 (3/40) (1/y)` the weight that Proposition A gives (derivation.md, "Consequence")? The Lean file
   takes it as stated; it does not prove Proposition A. That proof is the 30-minute item of the addendum below.
2. Are the limits right? y = p/K runs over (1/3, 17/40] for K/3 < p ≤ 17K/40, and the outer integral ends at
   2λ = 37/20, as in §3.0.
3. Do `gain58_pos` and `gain58_end` say what E48 needs: a strict gain inside the range, and continuity at 17/40?
4. Is 363473/288000 ≈ 1.2620590 the I_out that `nu8_rescue/combine/COMBINED.md` feeds into the certified margin?

(e) Verbatim from CLAIMS C108-LC7:
> Differences: that Proposition A's weight is y * innerR(1/y) on this range is E48 (PROOF-DRAFT), not formalised; Iout_5_8 is reused from C108-LC2

(f) About 5 minutes after §3.0.

### 3.7 C108-LC8: the s-step is ≥ 167/300 for every real s ≥ 7 (LEAN-CHECKED; section added by the orchestrator, Sat 09:51 PT)

(a) E62. At α = 3/40, for every real s ≥ 7 and ν ≤ 10, the s-step is 2λ/3 + I_out(s+2) − I_out(s) ≥ 167/300. Hence
Θ(7 + 2n) ≥ Θ(7) + n·167/300 for all n ∈ ℕ, every M ≥ 3 and every real U. With E59's floor Θ(7, ν) ≥ 0.9058 (not in
Lean), this is the report's "the package proves ζ(s) irrational for no odd s ≥ 7".

(b) Printed statements: root project, `Mathathon/P108/SStepAll.lean`; gate PASS Sat 09:48 PT; axioms `propext,
Classical.choice, Quot.sound`.
```lean
Mathathon.P108.sstep_ge : ∀ (s ν : ℝ),
  7 ≤ s →
    ν ≤ 10 →
      167 / 300 ≤ 2 * (1 - 3 / 40) / 3 + (Mathathon.P108.Iout (s + 2) ν (3 / 40) - Mathathon.P108.Iout s ν (3 / 40))
Mathathon.P108.thetaPkg_odd_ge : ∀ (n : ℕ) (ν M U : ℝ),
  ν ≤ 10 →
    3 ≤ M →
      Mathathon.P108.thetaPkg 7 ν (3 / 40) M U + ↑n * (167 / 300) ≤ Mathathon.P108.thetaPkg (7 + 2 * ↑n) ν (3 / 40) M U
Mathathon.P108.thetaPkg_odd_pos : ∀ (n : ℕ) (ν M U : ℝ),
  ν ≤ 10 →
    3 ≤ M → 0 < Mathathon.P108.thetaPkg 7 ν (3 / 40) M U → 0 < Mathathon.P108.thetaPkg (7 + 2 * ↑n) ν (3 / 40) M U
Mathathon.P108.Tout_sstep : ∀ (s ν y : ℝ),
  7 ≤ s →
    ν ≤ 10 → -max 0 (8 / 5 - 3 * y) ≤ Mathathon.P108.Tout (s + 2) ν (3 / 40) y - Mathathon.P108.Tout s ν (3 / 40) y
```
(plus `sstep_pos`, the same as `sstep_ge` with `0 <`, and `Tout_intervalIntegrable`). No new definitions:
`Iout`, `Tout` and `thetaPkg` are those of §3.0 and §3.3.

(c) Source: `sstep_all_s/proof.md`, Theorem 1, Lemma 2 and Corollary 3. Why the bound holds: going from s to s + 2,
the per-pole term gains 2·B(y) ≥ 0, every removed-class cost is non-decreasing in s, and min(r̂, ẑ) ≥ 0. The only
loss is min(r̂, ẑ) at s, which is ≤ r̂ ≤ max(0, 8/5 − 3y) once s ≥ 7 and ν ≤ 10. Then ∫_{1/3}^{37/20} max(0, 8/5 − 3y)
dy = 3/50, and 37/60 − 3/50 = 167/300.

(d) Questions.
1. Is "ν ≤ 10 real" acceptable? The report claims even ν ≤ 10; the Lean statement is stronger.
2. `thetaPkg_odd_ge` is for every M ≥ 3 and every real U. The same U on both sides is §3.3's question (U does not
   depend on s); do you accept it here too?
3. Is it clear that Lean does not prove the floor Θ(7, ν) > 0? That is E59, COMPUTED by interval arithmetic; Lean
   proves only that positivity at s = 7 propagates to every odd s ≥ 7.

(e) Verbatim from CLAIMS C108-LC8:
> Differences: Iout/Tout/thetaPkg are the Lean transcriptions of E13's package (C108-LC1-LC3: U is a free real number, the analytic bound is not formalised); the floor Theta(7, nu) >= 0.9058044 (E59) and hence "the package proves irrationality for no odd s >= 7" (Corollary 4) are not formalised

(f) About 5 minutes after §3.0 and §3.3.

## Addendum (orchestrator, Claude Opus 5.5, Sat 06:17 PT): one non-Lean proof that now carries a certified result

E50 says Fauzan's method also closes ζ(5) at ν = 8 once one outer estimate is improved. The sign is certified by interval arithmetic, but only relative to **Proposition A** (E48, PROOF-DRAFT), so in the report E50 is a CONJECTURE until you read the proof. About 30 minutes, with Fauzan (Zenodo 22826419) pp. 6-14 open next to `nu8_rescue/derive_fauzan-residue/derivation.md` §2:
1. Fauzan's Prop. 4.1 proof (pp. 10-11) run with (4.1) replaced by K/3 < p ≤ 17K/40. Check:
   - near poles z ∈ {−3, …, 2};
   - T ∈ [5, 7], so L_a ≥ 1 and degree ≤ 2(T+1) ≤ 16 ≤ p+1;
   - the zero block L_0 = 2, with degree 13 and poles ±1, ±2;
   - ℓ_K takes two consecutive values;
   - the zero-source half-weight 5/2 is at least every ordinary weight (equality possible at T = 7, ε = 1, ℓ_K = 5);
   - no rank term is needed, because Lemma 3.1 (p. 6) absorbs the polynomial moments.
2. Leading order: γ_p^in = pΓ_{5,8}(K/p) + O(1), uniformly for 40/17 ≤ K/p < 3. **Updated Sat 09:57: this is now Theorem U, written in full** in `nu8_rescue/propA_uniform/proof.md` §3 (finite, about two pages; §5 is the prime-sum step).
   - Statement: R = γ_p^in − pΓ(K/p) is exactly 15, 27/2, 19/2, 10 or 9 on the five ranges of p/K. Hence γ_p^in ≥ pΓ(K/p) + 9, which is the direction E50 uses.
   - Checks: an adversarial verifier passed it with its own code (R matches at all 200,647 pairs n ≤ 1000). Before Theorem U this item was only a sketch.
   - Reading §3 replaces this item; one small fix: Corollary U2's constant is 10.1951, not 10.195.
3. The analytic side for the new measure ρ_BR320 (Lai Lemma 11.4, p. 15 / Xu (12)). Its support [7.3·10⁻⁴, 0.8653] lies inside (0, ∞).

If 1-3 hold, E50 becomes "PROVED relative to E13" (E13 itself is item §1 of this sheet's reading list: `criterion5/derivation.md` §1-3).
