import Mathlib.NumberTheory.Bernoulli

/-!
# #108 `det_G40_zero`, part 2: computable Bernoulli numbers equal to Mathlib's

EVENT WORK (#108, formalizer 4, Claude Opus 5.5, Sat Nov 14 2026, started 00:35 PT).

Mathlib's `bernoulli'` is defined by well-founded recursion, which the kernel does not evaluate
usefully. `bernList n` is the list of the first `n` values built by structural recursion from
the same recurrence (`bernoulli'_def`), with binomial coefficients as quotients of factorials
(`Nat.choose_eq_factorial_div_factorial`); `bernoulli'_eq_bernC` proves `bernoulli' n = bernC n`
for **every** `n` (no computation involved). No `sorry`, no `native_decide`.
-/

namespace Mathathon.P108.Skip.DetG0

open Finset

/-- `n.choose k` through factorials (kernel-friendly; equal to `Nat.choose` for `k ≤ n`). -/
def chooseC (n k : ℕ) : ℕ := n.factorial / (k.factorial * (n - k).factorial)

/-- One step of the recurrence `B'_n = 1 - ∑_{k<n} C(n,k)/(n-k+1) B'_k`. -/
def bernNext (L : List ℚ) (n : ℕ) : ℚ :=
  1 - ∑ k ∈ range n, ((chooseC n k : ℕ) : ℚ) / ((n : ℚ) - k + 1) * L.getD k 0

/-- The first `n` values `B'_0, …, B'_{n-1}`. -/
def bernList : ℕ → List ℚ
  | 0 => []
  | n + 1 => bernList n ++ [bernNext (bernList n) n]

/-- `B'_n`, computably. -/
def bernC (n : ℕ) : ℚ := (bernList (n + 1)).getD n 0

theorem length_bernList (n : ℕ) : (bernList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bernList, ih]

theorem bernList_getD (n : ℕ) : ∀ k < n, (bernList n).getD k 0 = bernoulli' k := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      rw [bernList]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [List.getD_append _ _ _ _ (by rw [length_bernList]; exact hk)]
        exact ih k hk
      · rw [List.getD_append_right _ _ _ _ (by rw [length_bernList]), length_bernList,
          Nat.sub_self, List.getD_cons_zero, bernNext, bernoulli'_def]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.1 hj
        rw [ih j hj', chooseC, ← Nat.choose_eq_factorial_div_factorial hj'.le]

/-- **`bernoulli' n = bernC n` for every `n`.** -/
theorem bernoulli'_eq_bernC (n : ℕ) : bernoulli' n = bernC n :=
  (bernList_getD (n + 1) n (Nat.lt_succ_self n)).symm

end Mathathon.P108.Skip.DetG0
