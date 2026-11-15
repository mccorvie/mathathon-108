import Mathlib
import Zeta5S.PoleFun

/-!
# The monomial formula for `τ_s` (general `s`)

General-`s` counterparts of the first part of mo271/Zeta5@be1c0d82 `Apery/Arith/Pullback.lean`
(linearity of `τ`, `tau_X_pow`, `tau_X_pow_odd`, `tau_pull_poly`) and of the definitions `μmono`,
`μpoly` of `Apery/Construction.lean`.

formalizer (L7 scout): Claude Fable 5.2 subagent, 2026-11-14 (event work).
-/

open Finset Polynomial

namespace AperyS

/-! ### Linearity of `τ_s` -/

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:19-23 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_add`]
lemma tauS_add (s : ℕ) (P Q : ℚ[X]) : tauS s (P + Q) = tauS s P + tauS s Q := by
  unfold tauS
  rw [iterate_map_add, Lb_add]
  ring

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:25-29 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_C_mul`]
lemma tauS_C_mul (s : ℕ) (c : ℚ) (P : ℚ[X]) : tauS s (C c * P) = c * tauS s P := by
  unfold tauS
  rw [iterate_derivative_C_mul, Lb_C_mul]
  ring

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:31-32 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_neg`]
lemma tauS_neg (s : ℕ) (P : ℚ[X]) : tauS s (-P) = -tauS s P := by
  rw [show -P = C (-1) * P by simp, tauS_C_mul]; ring

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:34-38 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_sum`]
lemma tauS_sum (s : ℕ) {ι : Type*} (t : Finset ι) (f : ι → ℚ[X]) :
    tauS s (∑ i ∈ t, f i) = ∑ i ∈ t, tauS s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [tauS, Lb]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauS_add, ih]

/-! ### Monomials -/

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:40-43 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_X_pow`]
/-- `τ_s(x^n) = n(n-1)⋯(n-s+3) B_{n-(s-2)} / (s-1)!` (truncated subtractions, as upstream). -/
lemma tauS_X_pow (s n : ℕ) :
    tauS s (X ^ n) =
      (n.descFactorial (s - 2) : ℚ) * _root_.bernoulli (n - (s - 2)) / ((s - 1).factorial : ℚ) := by
  unfold tauS
  rw [iterate_derivative_X_pow_eq_smul, Lb_smul, Lb_X_pow]

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:32-35 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `μmono`]
/-- The polynomial moments for general `s`:
`μ_s(t^e) = (-1)^e B_{2e+2} (2e+s)! / ((2e+2)! (s-1)!)`.
Upstream `μmono` is `s = 5`: `(-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`. -/
def μmonoS (s e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) *
    (((2 * e + s).factorial : ℚ) / ((2 * e + 2).factorial : ℚ)) / ((s - 1).factorial : ℚ)

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:37-38 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `μpoly`]
/-- `μ_s` on polynomials in `t`, extended `ℚ`-linearly from the monomials. -/
noncomputable def μpolyS (s : ℕ) (P : ℚ[X]) : ℚ := P.sum fun e c => c * μmonoS s e

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:45-51 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_X_pow_odd`]
/-- **Monomial formula**: `τ_s((-1)^e x^{2e+s}) = μ_s(t^e)`, i.e.
`τ_s(x^{s+2e}) = B_{2e+2} (2e+s)! / ((s-1)! (2e+2)!)`, for `s ≥ 2`. -/
lemma tauS_X_pow_odd (s : ℕ) (hs : 2 ≤ s) (e : ℕ) :
    tauS s (C ((-1 : ℚ) ^ e) * X ^ (2 * e + s)) = μmonoS s e := by
  rw [tauS_C_mul, tauS_X_pow, μmonoS]
  rw [show 2 * e + s - (s - 2) = 2 * e + 2 by omega]
  have hf : ((2 * e + 2).factorial : ℚ) * ((2 * e + s).descFactorial (s - 2) : ℚ) =
      ((2 * e + s).factorial : ℚ) := by
    have := Nat.factorial_mul_descFactorial (show s - 2 ≤ 2 * e + s by omega)
    rw [show 2 * e + s - (s - 2) = 2 * e + 2 by omega] at this
    exact_mod_cast this
  have h0 : ((2 * e + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * e + 2).factorial_ne_zero
  rw [← hf, mul_div_cancel_left₀ _ h0]
  ring

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:53-66 (Firsching; Paul-Lez), Apache-2.0 [GENERALIZED to symbolic s; upstream name `tau_pull_poly`]
/-- `τ_s(x^s Q(-x²)) = μ_s(Q)` for `s ≥ 2`. -/
lemma tauS_pull_poly (s : ℕ) (hs : 2 ≤ s) (Q : ℚ[X]) :
    tauS s (X ^ s * Q.comp (-X ^ 2)) = μpolyS s Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, mul_add, tauS_add, hP, hQ]
    unfold μpolyS
    rw [Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)]
  | monomial e a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
    have : X ^ s * (C a * (-X ^ 2) ^ e) = C a * (C ((-1 : ℚ) ^ e) * X ^ (2 * e + s)) := by
      rw [neg_pow, ← pow_mul, map_pow, map_neg, map_one]; ring
    rw [this, tauS_C_mul, tauS_X_pow_odd s hs]
    unfold μpolyS
    rw [C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index _ _ (by simp)]

end AperyS
