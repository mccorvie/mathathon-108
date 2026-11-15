import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-!
# #108 L4: Hankel determinants through a kernel-checked modified-moment certificate

EVENT WORK (#108, lane L task L4, Claude Opus 5.5, Sat Nov 14 2026, started 15:33 PT).

For a moment sequence `h : ℕ → ℚ` let `Lf h p = ∑_j p_j h_j` (a linear functional on `ℚ[X]`)
and let `P_i` be the monic polynomials of the three-term recurrence
`P_{-1} = 0`, `P_0 = 1`, `P_{i+1} = (X - α_i) P_i - β_i P_{i-1}` for **arbitrary** `α, β`.
`hankel_det`: if `Lf h (X^k P_i) = 0` for all `k < i < n`, then
`det (h (i + j))_{i,j<n} = ∏_{i<n} Lf h (X^i P_i)` (with `C_{ij} = coeff P_i j`, unit lower
triangular, `C H Cᵀ` is diagonal).

The kernel computes the modified moments `r_i(k) = Lf h (X^k P_i)` by the recurrence
`r_{i+1}(k) = r_i(k+1) - α_i r_i(k) - β_i r_{i-1}(k)` (`rows`, `O(n²)` rational operations),
with `α_i, β_i` read off the rows (Chebyshev's algorithm; any choice is sound, this one makes
the lower entries vanish), and checks the vanishing (`chebPass`). `hankel_det_of_pass` turns a
`true` check into the determinant value. No `sorry`, no `native_decide`, no axiom.

Imports are targeted (not `import Mathlib`): `LaiSkip.lean` has `open Polynomial`, and full Mathlib
would make its `bernoulli` ambiguous with `Polynomial.bernoulli`.
-/

namespace Mathathon.P108.Skip.DeltaEq

open Polynomial Matrix

/-! ## The moment functional and the three-term recurrence -/

/-- `Lf h p = ∑_j p_j h_j`. -/
noncomputable def Lf (h : ℕ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ := lsum fun j => h j • LinearMap.id

theorem Lf_C_mul_X_pow (h : ℕ → ℚ) (a : ℚ) (m : ℕ) : Lf h (C a * X ^ m) = a * h m := by
  rw [Lf, lsum_apply, C_mul_X_pow_eq_monomial, sum_monomial_index]
  · simp [mul_comm]
  · simp

theorem Lf_C_mul (h : ℕ → ℚ) (a : ℚ) (p : ℚ[X]) : Lf h (C a * p) = a * Lf h p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem Lf_X_pow_mul (h : ℕ → ℚ) (p : ℚ[X]) (N k : ℕ) (hp : p.natDegree < N) :
    Lf h (X ^ k * p) = ∑ j ∈ Finset.range N, p.coeff j * h (j + k) := by
  conv_lhs => rw [p.as_sum_range' N hp]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial,
    show X ^ k * (C (p.coeff j) * X ^ j) = C (p.coeff j) * X ^ (j + k) by ring, Lf_C_mul_X_pow]

theorem Lf_mul (h : ℕ → ℚ) (q p : ℚ[X]) (N : ℕ) (hq : q.natDegree < N) :
    Lf h (q * p) = ∑ k ∈ Finset.range N, q.coeff k * Lf h (X ^ k * p) := by
  conv_lhs => rw [q.as_sum_range' N hq]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, Lf_C_mul]

theorem Lf_step (h : ℕ → ℚ) (a b : ℚ) (P Q : ℚ[X]) (k : ℕ) :
    Lf h (X ^ k * ((X - C a) * P - C b * Q)) =
      Lf h (X ^ (k + 1) * P) - a * Lf h (X ^ k * P) - b * Lf h (X ^ k * Q) := by
  have e : X ^ k * ((X - C a) * P - C b * Q) =
      X ^ (k + 1) * P - C a * (X ^ k * P) - C b * (X ^ k * Q) := by ring
  rw [e, map_sub, map_sub, Lf_C_mul, Lf_C_mul]

/-- `(P_{i-1}, P_i)`, with `P_{-1} = 0`, `P_0 = 1`, `P_{i+1} = (X - α_i) P_i - β_i P_{i-1}`. -/
noncomputable def PP (α β : ℕ → ℚ) : ℕ → ℚ[X] × ℚ[X]
  | 0 => (0, 1)
  | i + 1 => ((PP α β i).2, (X - C (α i)) * (PP α β i).2 - C (β i) * (PP α β i).1)

theorem PP_spec (α β : ℕ → ℚ) :
    ∀ i, (PP α β i).2.Monic ∧ (PP α β i).2.natDegree = i ∧ (PP α β i).1.degree < i
  | 0 => by simp [PP]
  | i + 1 => by
      obtain ⟨hm, hd, h1⟩ := PP_spec α β i
      have hXm : (X - C (α i)).Monic := monic_X_sub_C _
      have hprod : ((X - C (α i)) * (PP α β i).2).Monic := hXm.mul hm
      have hpd : ((X - C (α i)) * (PP α β i).2).natDegree = i + 1 := by
        rw [hXm.natDegree_mul hm, natDegree_X_sub_C, hd, add_comm]
      have hpdeg : ((X - C (α i)) * (PP α β i).2).degree = ((i + 1 : ℕ) : WithBot ℕ) := by
        rw [degree_eq_natDegree hprod.ne_zero, hpd]
      have hlt : (C (β i) * (PP α β i).1).degree < ((X - C (α i)) * (PP α β i).2).degree := by
        rw [← smul_eq_C_mul, hpdeg]
        refine (degree_smul_le _ _).trans_lt (h1.trans ?_)
        exact_mod_cast Nat.lt_succ_self i
      refine ⟨hprod.sub_of_left hlt, ?_, ?_⟩
      · show ((X - C (α i)) * (PP α β i).2 - C (β i) * (PP α β i).1).natDegree = i + 1
        rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlt), hpd]
      · show (PP α β i).2.degree < ((i + 1 : ℕ) : WithBot ℕ)
        rw [degree_eq_natDegree hm.ne_zero, hd]
        exact_mod_cast Nat.lt_succ_self i

/-! ## The determinant of a Hankel matrix from orthogonality -/

/-- **Hankel determinant from a three-term recurrence.** For any `α, β`, if
`Lf h (X^k P_i) = 0` for `k < i < n`, then `det (h (i+j))_{i,j<n} = ∏_{i<n} Lf h (X^i P_i)`. -/
theorem hankel_det (h : ℕ → ℚ) (α β : ℕ → ℚ) (n : ℕ)
    (hz : ∀ i < n, ∀ k < i, Lf h (X ^ k * (PP α β i).2) = 0) :
    (Matrix.of fun i j : Fin n => h (i.val + j.val)).det =
      ∏ i : Fin n, Lf h (X ^ i.val * (PP α β i.val).2) := by
  have hdeg : ∀ i, ((PP α β i).2).natDegree = i := fun i => (PP_spec α β i).2.1
  have hmon : ∀ i, ((PP α β i).2).Monic := fun i => (PP_spec α β i).1
  -- orthogonality for `l ≤ i`
  have orth_le : ∀ i l : ℕ, i < n → l ≤ i →
      Lf h ((PP α β l).2 * (PP α β i).2) = if l = i then Lf h (X ^ i * (PP α β i).2) else 0 := by
    intro i l hi hli
    rw [Lf_mul h _ _ (l + 1) (by rw [hdeg]; omega)]
    rcases eq_or_lt_of_le hli with rfl | hlt
    · rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => by
        rw [hz l hi k (Finset.mem_range.1 hk), mul_zero]]
      have h1 : ((PP α β l).2).coeff l = 1 := by
        have := (hmon l).coeff_natDegree; rwa [hdeg] at this
      rw [h1, zero_add, one_mul]
    · rw [if_neg hlt.ne]
      exact Finset.sum_eq_zero fun k hk => by
        rw [hz i hi k (by have := Finset.mem_range.1 hk; omega), mul_zero]
  have orth : ∀ i l : ℕ, i < n → l < n →
      Lf h ((PP α β l).2 * (PP α β i).2) = if l = i then Lf h (X ^ i * (PP α β i).2) else 0 := by
    intro i l hi hl
    rcases le_total l i with hli | hil
    · exact orth_le i l hi hli
    · rcases eq_or_lt_of_le hil with rfl | hlt
      · exact orth_le i i hi le_rfl
      · rw [mul_comm, orth_le l i hl hil, if_neg hlt.ne, if_neg hlt.ne']
  set Cm : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => ((PP α β i.val).2).coeff j.val
    with hCm
  set Hm : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => h (i.val + j.val) with hHm
  have hCH : Cm * Hm * Cmᵀ = Matrix.diagonal fun i => Lf h (X ^ i.val * (PP α β i.val).2) := by
    ext i l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hCm, hHm, Matrix.of_apply,
      Matrix.diagonal_apply]
    have e1 : ∀ k : Fin n, ∑ j : Fin n, ((PP α β i.val).2).coeff j.val * h (j.val + k.val) =
        Lf h (X ^ k.val * (PP α β i.val).2) := by
      intro k
      rw [Lf_X_pow_mul h _ n k.val (by rw [hdeg]; exact i.isLt)]
      exact Fin.sum_univ_eq_sum_range (fun j => ((PP α β i.val).2).coeff j * h (j + k.val)) n
    simp_rw [e1]
    have e2 : ∑ k : Fin n, Lf h (X ^ k.val * (PP α β i.val).2) * ((PP α β l.val).2).coeff k.val =
        Lf h ((PP α β l.val).2 * (PP α β i.val).2) := by
      rw [Lf_mul h _ _ n (by rw [hdeg]; exact l.isLt)]
      rw [← Fin.sum_univ_eq_sum_range (fun k => ((PP α β l.val).2).coeff k *
        Lf h (X ^ k * (PP α β i.val).2)) n]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [e2, orth i.val l.val i.isLt l.isLt]
    by_cases hil : i = l
    · subst hil; simp
    · rw [if_neg hil, if_neg (fun h => hil (Fin.ext h.symm))]
  have hdetC : Cm.det = 1 := by
    rw [det_of_isLowerTriangular Cm ?_]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp only [hCm, Matrix.of_apply]
      have := (hmon i.val).coeff_natDegree; rwa [hdeg] at this
    · intro i j hij
      have hij' : i < j := hij
      simp only [hCm, Matrix.of_apply]
      exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hij')
  have := congrArg Matrix.det hCH
  rw [det_mul, det_mul, det_transpose, hdetC, det_diagonal, one_mul, mul_one] at this
  exact this

/-! ## The kernel computation: modified-moment rows -/

/-- `nxt a b r p = (r(k+1) - a r(k) - b p(k))_{k < |r| - 1}` (`p` padded with zeros). -/
def nxt (a b : ℚ) : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: t, p =>
      match t with
      | [] => []
      | y :: _ => (y - a * x - b * p.headD 0) :: nxt a b t p.tail

theorem nxt_length (a b : ℚ) : ∀ (r p : List ℚ), (nxt a b r p).length = r.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: t, p => by
      rw [nxt, List.length_cons, nxt_length a b (y :: t) p.tail]
      simp

theorem getD_tail (p : List ℚ) (k : ℕ) : p.tail.getD k 0 = p.getD (k + 1) 0 := by
  cases p <;> simp

theorem headD_eq_getD (p : List ℚ) : p.headD 0 = p.getD 0 0 := by
  cases p <;> simp

theorem nxt_getD (a b : ℚ) : ∀ (r p : List ℚ) (k : ℕ), k + 1 < r.length →
    (nxt a b r p).getD k 0 = r.getD (k + 1) 0 - a * r.getD k 0 - b * p.getD k 0
  | [], _, _, h => absurd h (by simp)
  | [_], _, _, h => absurd h (by simp)
  | x :: y :: t, p, 0, _ => by
      rw [nxt, List.getD_cons_zero, headD_eq_getD]
      simp
  | x :: y :: t, p, k + 1, h => by
      rw [nxt, List.getD_cons_succ, nxt_getD a b (y :: t) p.tail k (by simp at h ⊢; omega),
        getD_tail]
      simp

/-- `β_i = r_i(i) / r_{i-1}(i-1)` from the state `(r_{i-1}, r_i)`. -/
def betaOf (i : ℕ) (s : List ℚ × List ℚ) : ℚ := s.2.getD i 0 / s.1.getD (i - 1) 0

/-- `α_i = (r_i(i+1) - β_i r_{i-1}(i)) / r_i(i)`. -/
def alphaOf (i : ℕ) (s : List ℚ × List ℚ) : ℚ :=
  (s.2.getD (i + 1) 0 - betaOf i s * s.1.getD i 0) / s.2.getD i 0

/-- `(r_{i-1}, r_i) ↦ (r_i, r_{i+1})`. -/
def step (i : ℕ) (s : List ℚ × List ℚ) : List ℚ × List ℚ :=
  (s.2, nxt (alphaOf i s) (betaOf i s) s.2 s.1)

/-- `(r_{i-1}, r_i)`, starting from `(0, h)`. -/
def rows (h0 : List ℚ) : ℕ → List ℚ × List ℚ
  | 0 => ([], h0)
  | i + 1 => step i (rows h0 i)

/-- The recurrence coefficients actually used by `rows`. -/
def αs (h0 : List ℚ) (i : ℕ) : ℚ := alphaOf i (rows h0 i)

/-- The recurrence coefficients actually used by `rows`. -/
def βs (h0 : List ℚ) (i : ℕ) : ℚ := betaOf i (rows h0 i)

/-- One pass over the rows `i, i+1, …, i+c-1`: checks `r_j(k) = 0` for `k < j` and returns the
product of the diagonal entries `r_j(j)`. -/
def chebPass : ℕ → ℕ → List ℚ × List ℚ → Bool × ℚ
  | 0, _, _ => (true, 1)
  | c + 1, i, s =>
      let r := chebPass c (i + 1) (step i s)
      ((List.range i).all (fun k => decide (s.2.getD k 0 = 0)) && r.1, s.2.getD i 0 * r.2)

theorem rows_spec (h0 : List ℚ) : ∀ i, i ≤ h0.length →
    (rows h0 i).2.length = h0.length - i ∧
    ∀ k, k < h0.length - i →
      (rows h0 i).2.getD k 0 = Lf (fun m => h0.getD m 0) (X ^ k * (PP (αs h0) (βs h0) i).2) ∧
      (rows h0 i).1.getD k 0 = Lf (fun m => h0.getD m 0) (X ^ k * (PP (αs h0) (βs h0) i).1)
  | 0, _ => by
      refine ⟨by simp [rows], fun k _ => ⟨?_, ?_⟩⟩
      · simp only [rows, PP, mul_one]
        rw [← one_mul (X ^ k), ← C_1, Lf_C_mul_X_pow, one_mul]
      · simp [rows, PP]
  | i + 1, hi => by
      obtain ⟨hlen, hval⟩ := rows_spec h0 i (by omega)
      have hr : rows h0 (i + 1) = ((rows h0 i).2,
          nxt (αs h0 i) (βs h0 i) (rows h0 i).2 (rows h0 i).1) := rfl
      have hP : PP (αs h0) (βs h0) (i + 1) = ((PP (αs h0) (βs h0) i).2,
          (X - C (αs h0 i)) * (PP (αs h0) (βs h0) i).2 -
            C (βs h0 i) * (PP (αs h0) (βs h0) i).1) := rfl
      rw [hr, hP]
      refine ⟨by rw [nxt_length, hlen]; omega, fun k hk => ⟨?_, (hval k (by omega)).1⟩⟩
      rw [nxt_getD _ _ _ _ _ (by rw [hlen]; omega), (hval (k + 1) (by omega)).1,
        (hval k (by omega)).1, (hval k (by omega)).2, Lf_step]

theorem chebPass_spec (h0 : List ℚ) : ∀ c i, (chebPass c i (rows h0 i)).1 = true →
    (∀ j < c, ∀ k < i + j, (rows h0 (i + j)).2.getD k 0 = 0) ∧
    (chebPass c i (rows h0 i)).2 = ∏ j ∈ Finset.range c, (rows h0 (i + j)).2.getD (i + j) 0
  | 0, i, _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by simp [chebPass]⟩
  | c + 1, i, hc => by
      have hstep : step i (rows h0 i) = rows h0 (i + 1) := rfl
      simp only [chebPass, hstep, Bool.and_eq_true, List.all_eq_true, List.mem_range,
        decide_eq_true_eq] at hc ⊢
      obtain ⟨hz, hr⟩ := hc
      obtain ⟨ih1, ih2⟩ := chebPass_spec h0 c (i + 1) hr
      have hj : ∀ j, i + 1 + j = i + (j + 1) := fun j => by omega
      refine ⟨fun j hjc k hk => ?_, ?_⟩
      · rcases j with _ | j
        · exact hz k (by simpa using hk)
        · have := ih1 j (by omega) k (by omega)
          rwa [hj] at this
      · rw [ih2, Finset.prod_range_succ', mul_comm]
        simp only [hj, Nat.add_zero]

/-- **The kernel certificate gives the determinant.** If `chebPass` succeeds on the moment list
`h0` (`2n - 1 ≤ |h0|`), the Hankel determinant `det (h0[i+j])_{i,j<n}` is the returned product. -/
theorem hankel_det_of_pass (h0 : List ℚ) (n : ℕ) (hL : 2 * n ≤ h0.length + 1)
    (hc : (chebPass n 0 (rows h0 0)).1 = true) :
    (Matrix.of fun i j : Fin n => h0.getD (i.val + j.val) 0).det = (chebPass n 0 (rows h0 0)).2 := by
  obtain ⟨hz, hp⟩ := chebPass_spec h0 n 0 hc
  simp only [Nat.zero_add] at hz hp
  have key : ∀ i < n, ∀ k ≤ i, (rows h0 i).2.getD k 0 =
      Lf (fun m => h0.getD m 0) (X ^ k * (PP (αs h0) (βs h0) i).2) := fun i hi k hk =>
    ((rows_spec h0 i (by omega)).2 k (by omega)).1
  rw [hankel_det (fun m => h0.getD m 0) (αs h0) (βs h0) n
    (fun i hi k hk => by rw [← key i hi k hk.le]; exact hz i hi k hk), hp,
    ← Fin.prod_univ_eq_prod_range (fun i => (rows h0 i).2.getD i 0) n]
  exact Finset.prod_congr rfl fun i _ => (key i.val i.isLt i.val le_rfl).symm

end Mathathon.P108.Skip.DeltaEq
