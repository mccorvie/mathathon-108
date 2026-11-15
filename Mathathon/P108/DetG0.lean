import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Bernoulli
import Mathathon.P108.LaiSkipData
import Mathathon.P108.DetG0Poly
import Mathathon.P108.DetG0Bern
import Mathathon.P108.DetG0LDL

/-!
# #108 `det_G40_zero`: `det G_40(0) = coefQ 0`, kernel-checked

EVENT WORK (#108, formalizer 4, Claude Opus 5.5, Sat Nov 14 2026, started 00:35 PT).

`LeanSkip/LaiSkip.lean` imports this file, so this file cannot import the definitions there.
It repeats them **verbatim** (`D`, `H`, `muMono`, `muPole`, `dD`, `muX`, `G`, `coefQ`, in the
namespace `Mathathon.P108.Skip.DetG0`), and `LaiSkip.det_G40_zero` is proved by
`DetG0.det_G40_zero'`, which the kernel accepts only because the two sets of definitions unfold
to the same terms (definitional equality, checked by the kernel; no transcription is trusted).

Proof:
1. *Division.* `qrSeq m` is the quotient/remainder of `D_3^2 X^m` by the monic `D_40`, built by
   the recurrence `f_{m+1} = X f_m` (`divStep`, proved for all `m`), so
   `(D_3^2 X^m) /ₘ D_40 = ofL (qrSeq m).1` by uniqueness of division (`div_eq`, no computation).
2. *Entries.* `eval 0 (muX 11 40 (D_3^2 X^m)) = g0C m`, an explicit computable rational
   (`entry_eq`; Bernoulli numbers by `bernoulli'_eq_bernC`), and
   `G_40(0) = (g0C (i+j))_{i,j<37}` (`map_G_eq`).
3. *Determinant.* An `L D Lᵀ` factorization computed by the unverified elimination `ldlAux` is
   checked by the kernel on the lower triangle (`checkLDLsym_sound`, `G_40(0)` is symmetric), so
   `det = ∏ d_i`, and the kernel checks `∏ d_i = coefQ 0` in the same evaluation (`finalCheck`).
All checks are `decide +kernel` (kernel reduction with GMP-accelerated `Nat`); no
`native_decide`, no `sorry`, no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Mathathon.P108.Skip.DetG0

open Polynomial

/-! ## Verbatim copies of the definitions of `LeanSkip/LaiSkip.lean` -/

/-- `D_m(t) = ∏_{j=1}^{m} (t + j²)` (copy of `Skip.D`). -/
noncomputable def D (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C ((j : ℚ) ^ 2))

/-- Copy of `Skip.H`. -/
def H (s k : ℕ) : ℚ := ∑ v ∈ Finset.Icc 1 k, 1 / (v : ℚ) ^ s

/-- Copy of `Skip.muMono`. -/
def muMono (s e : ℕ) : ℚ :=
  (-1) ^ e * bernoulli (2 * e + 2) * ((2 * e + s).factorial : ℚ) /
    (((2 * e + 2).factorial : ℚ) * ((s - 1).factorial : ℚ))

/-- Copy of `Skip.muPole`. -/
noncomputable def muPole (s k : ℕ) : ℚ[X] :=
  C ((k : ℚ) ^ (s - 1)) * (X - C (H s k)) + C (1 / (2 * (k : ℚ)) - 1 / ((s : ℚ) - 1))

/-- Copy of `Skip.dD`. -/
def dD (K k : ℕ) : ℚ := ∏ j ∈ (Finset.Icc 1 K).erase k, ((j : ℚ) ^ 2 - (k : ℚ) ^ 2)

/-- Copy of `Skip.muX`. -/
noncomputable def muX (s K : ℕ) (f : ℚ[X]) : ℚ[X] :=
  C (∑ e ∈ Finset.range ((f /ₘ D K).natDegree + 1), (f /ₘ D K).coeff e * muMono s e) +
    ∑ k ∈ Finset.Icc 1 K, C (f.eval (-((k : ℚ) ^ 2)) / dD K k) * muPole s k

/-- Copy of `Skip.G`. -/
noncomputable def G (s ν n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] :=
  Matrix.of fun i j => muX s (40 * n) (D (3 * n) ^ ν * X ^ (i.val + j.val))

/-- Copy of `Skip.coefQ`. -/
def coefQ (i : ℕ) : ℚ :=
  match coeffData[i]? with
  | some (z, d, _, _) => (z : ℚ) / d
  | none => 0

/-! ## Step 1a: the division `(D_3^2 X^m) /ₘ D_40`, by a proved recurrence (no search) -/

theorem D_eq (m : ℕ) : D m = ofL (dL m) := prod_eq_ofL_dL m

theorem D_monic (m : ℕ) : (D m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem D_natDegree (m : ℕ) : (D m).natDegree = m := by
  rw [D, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _),
    Finset.sum_congr rfl (fun (j : ℕ) _ => natDegree_X_add_C (((j : ℕ) : ℚ) ^ 2))]
  simp

theorem D40_degree : (D 40).degree = (40 : ℕ) := by
  rw [degree_eq_natDegree (D_monic 40).ne_zero, D_natDegree]

/-- One division step: `(q, r) ↦ (c :: q, (X r - c D_40)` truncated), `c = r[39]`. -/
def qrStep (qr : List ℚ × List ℚ) : List ℚ × List ℚ :=
  (qr.2.getD 39 0 :: qr.1, (addL (0 :: qr.2) (smulL (-(qr.2.getD 39 0)) (dL 40))).take 40)

/-- Quotient and remainder of `D_3^2 X^m` by `D_40`, computed on lists. -/
def qrSeq : ℕ → List ℚ × List ℚ
  | 0 => ([], mulL (dL 3) (dL 3))
  | m + 1 => qrStep (qrSeq m)

theorem dL40_getD : (dL 40).getD 40 0 = 1 := by decide +kernel

theorem dL40_length : (dL 40).length ≤ 41 := by decide +kernel

theorem qrSeq_spec (m : ℕ) :
    D 3 ^ 2 * X ^ m = D 40 * ofL (qrSeq m).1 + ofL (qrSeq m).2 ∧ (qrSeq m).2.length ≤ 40 := by
  induction m with
  | zero =>
      refine ⟨?_, by decide +kernel⟩
      rw [qrSeq, pow_zero, mul_one, D_eq 3, sq, ← ofL_mulL]
      simp [ofL]
  | succ m ih =>
      refine ⟨?_, List.length_take_le _ _⟩
      have h : D 3 ^ 2 * X ^ (m + 1) = X * (D 3 ^ 2 * X ^ m) := by ring
      rw [h, qrSeq, qrStep]
      exact divStep (D_eq 40).symm dL40_getD dL40_length ih.2 ih.1

theorem div_eq (m : ℕ) : (D 3 ^ 2 * X ^ m) /ₘ D 40 = ofL (qrSeq m).1 :=
  divByMonic_eq_ofL (D_monic 40) 40 D40_degree _ _ (qrSeq_spec m).2 (qrSeq_spec m).1

theorem natDegree_q_lt (m : ℕ) : (ofL (qrSeq m).1).natDegree < m + 6 - 40 + 1 := by
  rw [← div_eq, natDegree_divByMonic _ (D_monic 40),
    natDegree_mul (pow_ne_zero _ (D_monic 3).ne_zero) (pow_ne_zero _ X_ne_zero),
    natDegree_pow, natDegree_X_pow, D_natDegree, D_natDegree]
  omega

/-! ## Step 1b: the entries `eval 0 (muX 11 40 (D_3^2 X^m))` -/

/-- `eval 0 (muPole 11 k)`, computably. -/
def poleVal (k : ℕ) : ℚ :=
  (k : ℚ) ^ (11 - 1) * (0 - H 11 k) + (1 / (2 * (k : ℚ)) - 1 / (((11 : ℕ) : ℚ) - 1))

theorem eval_muPole (k : ℕ) : eval 0 (muPole 11 k) = poleVal k := by
  simp only [muPole, poleVal, eval_add, eval_mul, eval_C, eval_sub, eval_X]

theorem eval_f (m : ℕ) (x : ℚ) :
    eval x (D 3 ^ 2 * X ^ m) = (∏ j ∈ Finset.Icc (1 : ℕ) 3, (x + (j : ℚ) ^ 2)) ^ 2 * x ^ m := by
  simp only [D, eval_mul, eval_pow, eval_prod, eval_add, eval_X, eval_C]

/-- `muMono 11 e`, computably (`bernoulli n = (-1)^n B'_n`, `B'_n = bernC n`). -/
def muMonoC (e : ℕ) : ℚ :=
  (-1) ^ e * ((-1) ^ (2 * e + 2) * bernC (2 * e + 2)) * ((2 * e + 11).factorial : ℚ) /
    (((2 * e + 2).factorial : ℚ) * ((11 - 1).factorial : ℚ))

theorem muMono_eq (e : ℕ) : muMono 11 e = muMonoC e := by
  rw [muMono, muMonoC, bernoulli, bernoulli'_eq_bernC]

/-- The `m`-independent weight of the pole `k`: `D_3(-k²)^2 / D_40'(-k²) · μ_X(1/(t+k²))|_{X=0}`. -/
def wK (k : ℕ) : ℚ :=
  (∏ j ∈ Finset.Icc (1 : ℕ) 3, (-((k : ℚ) ^ 2) + (j : ℚ) ^ 2)) ^ 2 / dD 40 k * poleVal k

/-- The entry for `i + j = m`, given the quotient list `qr.1`. -/
def g0Val (m : ℕ) (qr : List ℚ × List ℚ) : ℚ :=
  (∑ e ∈ Finset.range (m + 6 - 40 + 1), qr.1.getD e 0 * muMonoC e) +
    ∑ k ∈ Finset.Icc (1 : ℕ) 40, wK k * (-((k : ℚ) ^ 2)) ^ m

/-- The entry `G_40(0)_{ij}` for `i + j = m`, as an explicit computable rational. -/
def g0C (m : ℕ) : ℚ := g0Val m (qrSeq m)

theorem sum_range_natDegree (p : ℚ[X]) (g : ℕ → ℚ) (N : ℕ) (hN : p.natDegree < N) :
    ∑ e ∈ Finset.range (p.natDegree + 1), p.coeff e * g e =
      ∑ e ∈ Finset.range N, p.coeff e * g e := by
  have h0 : ∀ n, (fun (e : ℕ) (c : ℚ) => c * g e) n 0 = 0 := fun n => zero_mul _
  exact (sum_over_range (f := fun e c => c * g e) p h0).symm.trans
    (sum_over_range' (f := fun e c => c * g e) p h0 N hN)

theorem entry_eq (m : ℕ) : eval 0 (muX 11 40 (D 3 ^ 2 * X ^ m)) = g0C m := by
  rw [muX, div_eq m, eval_add, eval_C, eval_finsetSum, g0C, g0Val]
  congr 1
  · rw [sum_range_natDegree _ _ _ (natDegree_q_lt m)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coeff_ofL, muMono_eq]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_muPole, eval_f, wK]
    ring

/-- All 73 Hankel values in one pass (the kernel then evaluates each division step once). -/
def g0Pass : ℕ → ℕ → List ℚ × List ℚ → List ℚ
  | 0, _, _ => []
  | k + 1, m, qr => g0Val m qr :: g0Pass k (m + 1) (qrStep qr)

theorem g0Pass_getD : ∀ (k m j : ℕ), j < k → (g0Pass k m (qrSeq m)).getD j 0 = g0C (m + j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, m, 0, _ => by rw [g0Pass, List.getD_cons_zero, Nat.add_zero, g0C]
  | k + 1, m, j + 1, h => by
      rw [g0Pass, List.getD_cons_succ, show qrStep (qrSeq m) = qrSeq (m + 1) from rfl,
        g0Pass_getD k (m + 1) j (by omega), show m + 1 + j = m + (j + 1) by omega]

/-- The 73 Hankel values `G_40(0)_{ij}`, `m = i + j ≤ 72`. -/
def g0List : List ℚ := g0Pass 73 0 (qrSeq 0)

theorem g0List_getD (m : ℕ) (hm : m < 73) : g0List.getD m 0 = g0C m := by
  rw [g0List, g0Pass_getD 73 0 m hm, Nat.zero_add]

theorem map_G_eq :
    (G 11 2 1).map (eval 0) = Matrix.of fun i j : Fin (37 * 1) => g0List.getD (i.val + j.val) 0 := by
  ext i j
  have hij : i.val + j.val < 73 := by have := i.isLt; have := j.isLt; omega
  rw [Matrix.map_apply, G, Matrix.of_apply, Matrix.of_apply, g0List_getD _ hij]
  exact entry_eq _

/-! ## Step 2: the determinant -/

/-- The rows of `G_40(0)`. -/
def Mrows : List (List ℚ) :=
  (List.range 37).map fun i => (List.range 37).map fun j => g0List.getD (i + j) 0

/-- The `L D Lᵀ` certificate (pivots, multiplier columns), computed by `ldlAux`. -/
def cert : List ℚ × List (List ℚ) := ldlAux 37 Mrows

/-- Everything the kernel checks for the determinant, in one evaluation (shared work). -/
def finalCheck : Bool :=
  checkLDLsym (n := 37 * 1) (fun i j => g0List.getD (i.val + j.val) 0) (ldlL cert.2)
      (fun i => cert.1.getD i.val 0) &&
    decide ((List.ofFn fun i : Fin (37 * 1) => cert.1.getD i.val 0).prod = coefQ 0)

theorem finalCheck_true : finalCheck = true := by decide +kernel

theorem final_parts :
    checkLDLsym (n := 37 * 1) (fun i j => g0List.getD (i.val + j.val) 0) (ldlL cert.2)
        (fun i => cert.1.getD i.val 0) = true ∧
      (List.ofFn fun i : Fin (37 * 1) => cert.1.getD i.val 0).prod = coefQ 0 := by
  have h := finalCheck_true
  rw [finalCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- **`det G_40(0) = coefQ 0`** (s = 11, ν = 2, K = 40), stated with the copied definitions. -/
theorem det_G40_zero' : ((G 11 2 1).map (Polynomial.eval 0)).det = coefQ 0 := by
  rw [map_G_eq, checkLDLsym_sound _
    (fun i j => congrArg (fun t => g0List.getD t 0) (Nat.add_comm i.val j.val)) _ _
    final_parts.1, ← List.prod_ofFn, final_parts.2]

end Mathathon.P108.Skip.DetG0
