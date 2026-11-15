import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

/-!
# #108 `det_G40_zero`, part 1: a list model of `ℚ[X]`

EVENT WORK (#108, formalizer 4, Claude Opus 5.5, Sat Nov 14 2026, started 00:35 PT).

Computable coefficient lists (index = power of `X`) with a general soundness lemma for each
operation (`ofL_addL`, `ofL_mulL`, ...), so that a polynomial identity over `ℚ[X]` reduces to a
list computation that the kernel evaluates (`decide +kernel`). Used for the division
`(D_3^2 X^m) /ₘ D_40` in `LeanSkip/DetG0.lean` via `Polynomial.div_modByMonic_unique`.
No `sorry`, no `native_decide`.
-/

namespace Mathathon.P108.Skip.DetG0

open Polynomial

/-- The polynomial `∑ i, l[i] X^i` of a coefficient list. -/
noncomputable def ofL : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a + X * ofL l

/-- Coefficientwise sum (the shorter list is padded with zeros). -/
def addL : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Scalar multiple. -/
def smulL (a : ℚ) : List ℚ → List ℚ
  | [] => []
  | b :: l => (a * b) :: smulL a l

/-- Product (schoolbook). -/
def mulL : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => addL (smulL a m) (0 :: mulL l m)

/-- All entries are zero. -/
def allZero : List ℚ → Bool
  | [] => true
  | a :: l => decide (a = 0) && allZero l

/-- Equality of the polynomials of two lists (trailing zeros ignored); structural recursion on
the first list, so that the kernel evaluates it. -/
def eqL : List ℚ → List ℚ → Bool
  | [], m => allZero m
  | a :: l, [] => allZero (a :: l)
  | a :: l, b :: m => decide (a = b) && eqL l m

theorem ofL_addL : ∀ l m : List ℚ, ofL (addL l m) = ofL l + ofL m
  | [], m => by simp [addL, ofL]
  | a :: l, [] => by simp [addL, ofL]
  | a :: l, b :: m => by
      simp only [addL, ofL, ofL_addL l m, C_add]
      ring

theorem ofL_smulL (a : ℚ) : ∀ l : List ℚ, ofL (smulL a l) = C a * ofL l
  | [] => by simp [smulL, ofL]
  | b :: l => by
      simp only [smulL, ofL, ofL_smulL a l, C_mul]
      ring

theorem ofL_mulL : ∀ l m : List ℚ, ofL (mulL l m) = ofL l * ofL m
  | [], m => by simp [mulL, ofL]
  | a :: l, m => by
      simp only [mulL, ofL_addL, ofL_smulL, ofL, ofL_mulL l m, C_0]
      ring

theorem coeff_ofL : ∀ (l : List ℚ) (n : ℕ), (ofL l).coeff n = l.getD n 0
  | [], n => by simp [ofL]
  | a :: l, 0 => by simp [ofL]
  | a :: l, n + 1 => by
      simp [ofL, coeff_X_mul, coeff_ofL l n]

theorem allZero_getD : ∀ l : List ℚ, allZero l = true → ∀ n, l.getD n 0 = 0
  | [], _, _ => rfl
  | a :: l, h, n => by
      simp only [allZero, Bool.and_eq_true, decide_eq_true_eq] at h
      cases n with
      | zero => simp [h.1]
      | succ n => simpa using allZero_getD l h.2 n

theorem eqL_getD : ∀ l m : List ℚ, eqL l m = true → ∀ n, l.getD n 0 = m.getD n 0
  | [], m, h, n => by
      rw [eqL] at h
      rw [allZero_getD m h n]
      rfl
  | a :: l, [], h, n => by
      rw [eqL] at h
      rw [allZero_getD _ h n]
      rfl
  | a :: l, b :: m, h, n => by
      simp only [eqL, Bool.and_eq_true, decide_eq_true_eq] at h
      cases n with
      | zero => simp [h.1]
      | succ n => simpa using eqL_getD l m h.2 n

theorem ofL_eq_of_eqL {l m : List ℚ} (h : eqL l m = true) : ofL l = ofL m := by
  ext n
  rw [coeff_ofL, coeff_ofL]
  exact eqL_getD l m h n

theorem degree_ofL_lt (l : List ℚ) : (ofL l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_ofL]
  exact List.getD_eq_default _ _ hn

theorem natDegree_ofL_lt (l : List ℚ) : (ofL l).natDegree < l.length + 1 := by
  have : (ofL l).natDegree ≤ l.length := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_ofL]
    exact List.getD_eq_default _ _ hN.le
  omega

/-! ## The polynomials `D_m` and `X^m` as lists -/

/-- Coefficients of `∏_{j=1}^m (X + j²)`. -/
def dL : ℕ → List ℚ
  | 0 => [1]
  | m + 1 => mulL (dL m) [((m + 1 : ℕ) : ℚ) ^ 2, 1]

theorem prod_eq_ofL_dL (m : ℕ) :
    ∏ j ∈ Finset.Icc 1 m, (X + C ((j : ℚ) ^ 2)) = ofL (dL m) := by
  induction m with
  | zero => simp [dL, ofL]
  | succ m ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, dL, ofL_mulL]
      simp only [ofL, mul_zero, add_zero, C_1, mul_one]
      ring

/-- Coefficients of `X^m`. -/
def xL : ℕ → List ℚ
  | 0 => [1]
  | m + 1 => 0 :: xL m

theorem X_pow_eq_ofL_xL (m : ℕ) : (X : ℚ[X]) ^ m = ofL (xL m) := by
  induction m with
  | zero => simp [xL, ofL]
  | succ m ih => rw [pow_succ', ih, xL, ofL, C_0, zero_add]

/-! ## Division by a monic polynomial through a list certificate -/

/-- If `f = g q + r` with `deg r < deg g` (`r` given by a list of length `≤ deg g`), then
`f /ₘ g = q` (uniqueness of division, `Polynomial.div_modByMonic_unique`). -/
theorem divByMonic_eq_ofL {f g : ℚ[X]} (hg : g.Monic) (dg : ℕ) (hdg : g.degree = dg)
    (q r : List ℚ) (hr : r.length ≤ dg) (h : f = g * ofL q + ofL r) : f /ₘ g = ofL q := by
  refine (div_modByMonic_unique (ofL q) (ofL r) hg ⟨by rw [h]; ring, ?_⟩).1
  rw [hdg]
  exact lt_of_lt_of_le (degree_ofL_lt r) (by exact_mod_cast hr)

/-- Monic long division on coefficient lists (no correctness proof needed: its output is
only used as a certificate, checked by `eqL`). Returns `(q, r)` with `r` truncated to
`deg g` coefficients. -/
def divL (f g : List ℚ) : List ℚ × List ℚ :=
  let dg := g.length - 1
  let nq := f.length - dg
  let qr := (List.range nq).reverse.foldl
    (fun (qr : List ℚ × List ℚ) k =>
      let c := qr.2.getD (k + dg) 0
      (qr.1.set k c, addL qr.2 (List.replicate k 0 ++ smulL (-c) g)))
    (List.replicate nq 0, f)
  (qr.1, qr.2.take dg)

/-! ## Coefficientwise lemmas and one step of division by a monic polynomial of degree 40 -/

theorem getD_addL : ∀ (l m : List ℚ) (n : ℕ), (addL l m).getD n 0 = l.getD n 0 + m.getD n 0
  | [], m, n => by simp [addL]
  | a :: l, [], n => by simp [addL]
  | a :: l, b :: m, 0 => by simp [addL]
  | a :: l, b :: m, n + 1 => by
      rw [addL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, getD_addL l m n]

theorem getD_smulL (a : ℚ) : ∀ (l : List ℚ) (n : ℕ), (smulL a l).getD n 0 = a * l.getD n 0
  | [], n => by simp [smulL]
  | b :: l, 0 => by simp [smulL]
  | b :: l, n + 1 => by
      rw [smulL, List.getD_cons_succ, List.getD_cons_succ, getD_smulL a l n]

theorem ofL_take (l : List ℚ) (k : ℕ) (h : ∀ n, k ≤ n → l.getD n 0 = 0) :
    ofL (l.take k) = ofL l := by
  ext n
  rw [coeff_ofL, coeff_ofL]
  by_cases hn : n < k
  · simp [List.getD_eq_getElem?_getD, hn]
  · rw [h n (by omega)]
    simp [List.getD_eq_getElem?_getD, hn]

/-- **One step of long division.** If `f = D q + r` with `r` of length `≤ 40` and `D = ofL d`
monic of degree 40 (`d` of length `≤ 41`, `d[40] = 1`), then with `c = r[39]`,
`X f = D (c + X q) + r'` where `r' = (X r - c D)` truncated to 40 coefficients. -/
theorem divStep {f D : ℚ[X]} {d q r : List ℚ} (hD : ofL d = D) (hd40 : d.getD 40 0 = 1)
    (hdlen : d.length ≤ 41) (hrlen : r.length ≤ 40) (hf : f = D * ofL q + ofL r) :
    X * f = D * ofL (r.getD 39 0 :: q) +
      ofL ((addL (0 :: r) (smulL (-(r.getD 39 0)) d)).take 40) := by
  rw [ofL_take]
  · rw [ofL_addL, ofL_smulL, hD, hf]
    simp only [ofL, C_0, zero_add, C_neg]
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [getD_addL, getD_smulL, List.getD_cons_succ]
    rcases Nat.lt_or_ge k 40 with hk | hk
    · obtain rfl : k = 39 := by omega
      rw [hd40]; ring
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default d _ (by omega)]
      ring

end Mathathon.P108.Skip.DetG0
