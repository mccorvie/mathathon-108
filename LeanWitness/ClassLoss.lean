import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# #108: the one-rational class-loss witness against Lai's ζ(7), ν = 2 certificate

EVENT WORK (#108, formalizer, Claude Opus 5.5, Fri Nov 13 2026).

Formalizes "Lean target 2" of `problems/108-zeta-odd-autopsy/evidence/lai-nu2-audit/README.md`
(claim C5; the row `s=7 nu=2 p=13 a=2 e=0` of `class_loss.py`, output `out/class_loss.txt`).

**Objects.** `K = 40`, `N = 3K/40 = 3`, `ν = 2`, prime `p = 13`, class `a = 2`, `e = 0`, `Lo = 10`.
* `D_A(t) = ∏_{k=1}^{A} (t + k²)`.
* `Z(t) = D_3(t)^2 · ∏_{c ∈ {0,…,6}, c ≠ 2} (t + c²)^10` (degree 66).
* Lai's ζ(7) functional `μ_X` (laichunwing/Zeta7-is-Irrational@c42a984f, Program 11
  `11_padic_valuation.txt`, `mu_entry_affine`, l. 46-71), extended linearly:
  `μ_X(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)(2e+6)(2e+7)/720` and
  `μ_X(1/(t + j²)) = j^6 (X - H_j^(7)) + 1/(2j) - 1/6`, with `H_j^(7) = ∑_{v ≤ j} v^(-7)`.
  As in Program 11, `μ_X(Z/D_40)` is evaluated through the Euclidean division `Z = Q·D_40 + R`
  and the partial fractions `R/D_40 = ∑_j c_j/(t + j²)`, `c_j = R(-j²)/D_40'(-j²)`.
* The class count `β` of Zeta5's entry bound (mo271/Zeta5@7fe73676 `Apery/Arith/TEntry.lean`),
  as in `class_loss.py`: the minimum over residues `c mod 13` of
  `#{x-roots ≡ c} - #{poles ≡ c}`, where the x-roots are `s = 7` zeros at `0` (the pullback `x^s`)
  and `±γ`, with multiplicity, for every factor `(t + γ²)` of `Z`, and the poles are `±j`, `j ≤ 40`.

**Result** (`classLoss_witness`). `μ_X(Z/D_40) = A + B·X` with `v_13(A) = -10`, `v_13(B) = 0`,
and `β = -4`; so the loss `β - min(v_13 A, v_13 B)` is `6`. The exact rationals `A`, `B` are
`A_lit`, `B_lit` below (`entry_eq`).

**Not formalized here** (see the README of this folder): that Lai's certificate needs loss `≤ 0`
in every such entry (the advocate's reading of Lai's Γ, constant `ν - 1 = 1`); and the Zeta5
bound itself. Lean checks the finite rational computation only.

All computations are closed by `decide +kernel` (kernel reduction only, no compiler-trusting tactic); the
Bernoulli numbers are Mathlib's `bernoulli`, matched with a table through Mathlib's own recurrence
`bernoulli'_def` (`bernTab_eq`).
-/

namespace Mathathon.P108

/-! ## Polynomials as coefficient lists -/

/-- Polynomials in `t` with rational coefficients, as coefficient lists, lowest degree first. -/
abbrev Poly := List ℚ

namespace Poly

/-- Sum of two polynomials. -/
def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Scalar multiple `c · p`. -/
def smul (c : ℚ) (p : Poly) : Poly := p.map (c * ·)

/-- Product of two polynomials. -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- `p ^ n`. -/
def pow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n + 1 => mul (pow p n) p

/-- Product of a list of polynomials. -/
def prod (ps : List Poly) : Poly := ps.foldr mul [1]

/-- Evaluation at `x` (Horner). -/
def eval (p : Poly) (x : ℚ) : ℚ := p.foldr (fun a acc => a + x * acc) 0

/-- Formal derivative `d/dt`. -/
def deriv (p : Poly) : Poly := (p.zipIdx.map fun ai => (ai.2 : ℚ) * ai.1).tail

/-- `subScaled c r d`: subtract `c · d` from the leading entries of `r` (lists highest degree
first). -/
def subScaled (c : ℚ) : List ℚ → List ℚ → List ℚ
  | x :: xs, y :: ys => (x - c * y) :: subScaled c xs ys
  | xs, [] => xs
  | [], _ :: _ => []

/-- Long division by a monic divisor whose highest-first coefficient list is `1 :: dTail`,
on highest-first lists, for `fuel` steps. Returns the quotient (lowest degree first) and the
remainder (highest degree first). -/
def divLoop (dTail : List ℚ) : ℕ → List ℚ → List ℚ → List ℚ × List ℚ
  | 0, q, r => (q, r)
  | _ + 1, q, [] => (q, [])
  | k + 1, q, c :: r => divLoop dTail k (c :: q) (subScaled c r dTail)

/-- Euclidean division of `z` by a monic `d`: `(quotient, remainder)`, both lowest degree first.
(Its output for `Z` and `D_40` is certified by `Z_decomp`.) -/
def divMonic (z d : Poly) : Poly × Poly :=
  let res := divLoop d.reverse.tail (z.length + 1 - d.length) [] z.reverse
  (res.1, res.2.reverse)

end Poly

open Poly

/-! ## The objects -/

/-- The linear factor `t + γ²`. -/
def lin (γ : ℕ) : Poly := [((γ : ℕ) : ℚ) ^ 2, 1]

/-- `D_A(t) = ∏_{k=1}^{A} (t + k²)`. -/
def D (A : ℕ) : Poly := prod ((List.range A).map fun i => lin (i + 1))

/-- The numerator `Z(t) = D_3(t)^2 · ∏_{c ∈ {0,…,6}, c ≠ 2} (t + c²)^10`
(`K = 40`, `N = 3`, `ν = 2`, `p = 13`, `a = 2`, `e = 0`, `Lo = 10`). -/
def Z : Poly := mul (pow (D 3) 2) (prod (((List.range 7).filter (· ≠ 2)).map fun c => pow (lin c) 10))

/-- `H_j^(7) = ∑_{v=1}^{j} 1/v^7`. -/
def H7 (j : ℕ) : ℚ := ((List.range j).map fun v => 1 / ((v + 1 : ℕ) : ℚ) ^ 7).sum

/-- Lai's ζ(7) functional on monomials (Program 11, l. 59-60), for a Bernoulli sequence `bern`:
`μ_X(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)(2e+6)(2e+7)/720`. -/
def muMono (bern : ℕ → ℚ) (e : ℕ) : ℚ :=
  (-1) ^ e * bern (2 * e + 2) *
    (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) * (2 * e + 6) * (2 * e + 7) : ℕ) : ℚ) / 720

/-- Lai's ζ(7) functional on simple poles (Program 11, l. 63-71):
`μ_X(1/(t + j²)) = j^6 (X - H_j^(7)) + 1/(2j) - 1/6`, as (constant term, coefficient of `X`). -/
def muPole (j : ℕ) : ℚ × ℚ := (1 / (2 * (j : ℚ)) - 1 / 6 - (j : ℚ) ^ 6 * H7 j, (j : ℚ) ^ 6)

/-- Quotient and remainder of `Z` by `D_40`. -/
def QR : Poly × Poly := divMonic Z (D 40)

/-- The partial-fraction coefficient `c_j = R(-j²)/D_40'(-j²)` (Program 11, l. 66). -/
def resid (j : ℕ) : ℚ := QR.2.eval (-((j : ℚ) ^ 2)) / (deriv (D 40)).eval (-((j : ℚ) ^ 2))

/-- `D_40(t)/(t + j²) = ∏_{k ≤ 40, k ≠ j} (t + k²)`. -/
def Dexcept (j : ℕ) : Poly := prod (((List.range 40).filter (· + 1 ≠ j)).map fun i => lin (i + 1))

/-- `∑_{j=1}^{40} c_j · D_40(t)/(t + j²)`. -/
def poleSum : Poly := ((List.range 40).map fun i => smul (resid (i + 1)) (Dexcept (i + 1))).foldr add []

/-- `(A, B)` with `μ_X(Z/D_40) = A + B·X`, for a Bernoulli sequence `bern`:
`A = ∑_e Q_e μ_X(t^e) + ∑_j c_j (1/(2j) - 1/6 - j^6 H_j^(7))`, `B = ∑_j c_j j^6`. -/
def entryWith (bern : ℕ → ℚ) : ℚ × ℚ :=
  (((List.range QR.1.length).map (fun e => QR.1.getD e 0 * muMono bern e)).sum +
      ((List.range 40).map fun i => resid (i + 1) * (muPole (i + 1)).1).sum,
    ((List.range 40).map fun i => resid (i + 1) * (muPole (i + 1)).2).sum)

/-- The entry `μ_X(Z/D_40) = A + B·X` with Mathlib's Bernoulli numbers `bernoulli`
(`B_1 = -1/2`; only even indices occur). -/
noncomputable def entry : ℚ × ℚ := entryWith bernoulli

/-- The x-roots of the class count: `s = 7` zeros at `0`, and `±γ` with multiplicity for every
factor `(t + γ²)` of `Z` (`ν = 2` copies for `γ = 1, 2, 3`; `10` copies for `γ ∈ {0,1,3,4,5,6}`). -/
def xRoots : List ℤ :=
  List.replicate 7 0 ++
    ((List.range 3).flatMap fun i =>
      (List.replicate 2 [((i + 1 : ℕ) : ℤ), -((i + 1 : ℕ) : ℤ)]).flatten) ++
    (((List.range 7).filter (· ≠ 2)).flatMap fun c =>
      (List.replicate 10 [((c : ℕ) : ℤ), -((c : ℕ) : ℤ)]).flatten)

/-- The poles: `±j` for `1 ≤ j ≤ 40`. -/
def poles : List ℤ := (List.range 40).flatMap fun i => [((i + 1 : ℕ) : ℤ), -((i + 1 : ℕ) : ℤ)]

/-- Class count at the residue `c mod 13`: `#{x-roots ≡ c} - #{poles ≡ c}`. -/
def classCount (c : ℤ) : ℤ :=
  ((xRoots.countP fun x => decide (x % 13 = c)) : ℤ) - ((poles.countP fun x => decide (x % 13 = c)) : ℤ)

/-- `β = min_{c mod 13} classCount c`. -/
def beta : ℤ := ((List.range 13).map fun c => classCount c).foldl min (classCount 0)

/-! ## Bernoulli numbers: a table checked against Mathlib's `bernoulli'` -/

/-- `bernoulli' n` (Mathlib's convention, `B'_1 = +1/2`) for `n ≤ 54`. -/
def bernTab : List ℚ :=
  [1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, 0, -3617/510, 0,
    43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730, 0, 8553103/6, 0,
    -23749461029/870, 0, 8615841276005/14322, 0, -7709321041217/510, 0, 2577687858367/6, 0,
    -26315271553053477373/1919190, 0, 2929993913841559/6, 0, -261082718496449122051/13530, 0,
    1520097643918070802691/1806, 0, -27833269579301024235023/690, 0,
    596451111593912163277961/282, 0, -5609403368997817686249127547/46410, 0,
    495057205241079648212477525/66, 0, -801165718135489957347924991853/1590, 0,
    29149963634884862421418123812691/798]

/-- Binomial coefficient through factorials (fast in the kernel). -/
def chooseF (n k : ℕ) : ℕ := n.factorial / (k.factorial * (n - k).factorial)

/-- The table satisfies Mathlib's recurrence `bernoulli'_def` for `n < 55`. -/
theorem bernTab_rec : ∀ n < 55, bernTab.getD n 0 =
    1 - ∑ k ∈ Finset.range n, ((chooseF n k : ℕ) : ℚ) / ((n : ℚ) - k + 1) * bernTab.getD k 0 := by
  decide +kernel

/-- The table is Mathlib's `bernoulli'` for `n < 55`. -/
theorem bernTab_eq (n : ℕ) (hn : n < 55) : bernTab.getD n 0 = bernoulli' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [bernTab_rec n hn, bernoulli'_def n]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    rw [ih k hk' (by omega), chooseF, ← Nat.choose_eq_factorial_div_factorial hk'.le]

/-- Mathlib's `bernoulli`, read from the table below `55`. -/
def bernFast (n : ℕ) : ℚ := if n < 55 then (-1) ^ n * bernTab.getD n 0 else bernoulli n

theorem bernFast_eq : bernFast = bernoulli := by
  funext n
  unfold bernFast
  split_ifs with h
  · rw [bernTab_eq n h, bernoulli]
  · rfl

/-! ## The computation -/

/-- `Z = Q · D_40 + ∑_j c_j · D_40/(t + j²)`: the quotient and the partial-fraction coefficients
used by `entry` are those of `Z/D_40` (exact polynomial identity). -/
theorem Z_decomp : add (mul QR.1 (D 40)) poleSum = Z := by decide +kernel

/-- Degrees: `Z` has degree `66` and is monic; `D_40` has degree `40` and is monic; the quotient
has degree `26` (so `B_2, …, B_54` occur); the remainder and `∑_j c_j D_40/(t + j²)` have degree
`< 40`. With `Z_decomp` this makes `QR.1` the polynomial part of `Z/D_40` and
`∑_j c_j/(t + j²)` its proper part. -/
theorem QR_length : Z.length = 67 ∧ Z.getLast? = some 1 ∧ (D 40).length = 41 ∧
    (D 40).getLast? = some 1 ∧ QR.1.length = 27 ∧ QR.2.length = 40 ∧ poleSum.length = 40 := by
  decide +kernel

/-- The constant term `A` of the entry, exactly. -/
def A_lit : ℚ :=
  (22190144868112692868022927328504909846556766485153926675422125473704871597281426730446055702530608122724599759522687716151414494559193670380675712224531737614097368129384581935167497671124366572139682650410601590304553460066104 : ℚ) /
    92683033967465507454095666737377645309969430524431957261493162594660899124506826610875619881272322233905525710296630859375

/-- The coefficient `B` of `X` in the entry, exactly (an integer). -/
def B_lit : ℚ :=
  -237437277650662751791518090481657979804900085728238516398647012076018886357777182452746931893181536534528

/-- `μ_X(Z/D_40) = A_lit + B_lit · X`. -/
theorem entry_eq : entry = (A_lit, B_lit) := by
  rw [entry, ← bernFast_eq]
  decide +kernel

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem padicValRat_A_lit : padicValRat 13 A_lit = -10 := by
  have hnum : A_lit.num =
      22190144868112692868022927328504909846556766485153926675422125473704871597281426730446055702530608122724599759522687716151414494559193670380675712224531737614097368129384581935167497671124366572139682650410601590304553460066104 := by
    decide +kernel
  have hden : A_lit.den =
      13 ^ 10 * 672305584693205919754074784310297966561424619929884876957059555063005418186502756442726329141363289642333984375 := by
    decide +kernel
  rw [padicValRat_def, hnum, hden,
    padicValInt.eq_zero_of_not_dvd (by norm_num),
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem padicValRat_B_lit : padicValRat 13 B_lit = 0 := by
  have hnum : B_lit.num =
      -237437277650662751791518090481657979804900085728238516398647012076018886357777182452746931893181536534528 := by
    decide +kernel
  have hden : B_lit.den = 1 := by decide +kernel
  rw [padicValRat_def, hnum, hden, padicValInt.eq_zero_of_not_dvd (by norm_num)]
  simp

/-- `β = -4`, and it is the minimum of the class counts over all residues mod 13. -/
theorem beta_eq : beta = -4 ∧ (∀ c : ℕ, c < 13 → -4 ≤ classCount c) ∧ classCount 2 = -4 := by
  decide +kernel

/-- **Class-loss witness against Lai's ζ(7), ν = 2 certificate** (K = 40, p = 13, a = 2, e = 0).
For `Z(t) = D_3(t)^2 ∏_{c ∈ {0,…,6}, c ≠ 2} (t + c²)^10`, Lai's ζ(7) functional gives
`μ_X(Z/D_40) = A + B·X` with `v_13(A) = -10` and `v_13(B) = 0`, while the class count is `β = -4`;
so the loss `β - min(v_13 A, v_13 B)` equals `6` (Lai's Γ with constant `ν - 1 = 1` corresponds
to loss `≤ 0`). -/
theorem classLoss_witness :
    padicValRat 13 entry.1 = -10 ∧ padicValRat 13 entry.2 = 0 ∧ beta = -4 ∧
      beta - min (padicValRat 13 entry.1) (padicValRat 13 entry.2) = 6 := by
  rw [entry_eq]
  simp only [padicValRat_A_lit, padicValRat_B_lit, beta_eq.1]
  norm_num

end Mathathon.P108
