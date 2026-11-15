import Mathlib
import Zeta5S.DirectPoly
import Zeta5S.Monomial
import Zeta5S.Pullback
import Zeta5S.TEntry
import Zeta5S.MomentVal
import Zeta5S.ClassFrame
import Zeta5S.InnerAlloc
import Zeta5S.PoleVal
import Zeta5S.SmallPrimeF
import Zeta5S.OuterFrame

/-!
# Specialisation at `s = 5`: the statements of mo271/Zeta5@be1c0d82, recovered

`AperyS.Upstream` holds faithful copies (same bodies, same binder names; only the namespace differs)
of the five `s = 5` definitions of Zeta5 that the chain behind `tauX_direct` uses (`μmono`, `μpoly`,
`H5`, `tau`, `tauX`). Each is proved equal to the general-`s` definition at `s = 5`, and each
upstream theorem of the chain is re-proved, with its upstream statement copied character for
character, from the general-`s` theorem.

formalizer (L7 scout): Claude Fable 5.2 subagent, 2026-11-14 (event work).
-/

open Finset Polynomial

namespace AperyS.Upstream

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Faithful copies of the upstream definitions -/

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:32-35 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The polynomial moments (2.2): `μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`.
Mathlib's `bernoulli` uses the convention `B₁ = -1/2`, as does the paper. -/
def μmono (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) * ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)) / 24

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:37-38 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `μ` on polynomials in `t`, extended `ℚ`-linearly from the monomials. -/
noncomputable def μpoly (P : ℚ[X]) : ℚ := P.sum fun e c => c * μmono e

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:40-41 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The generalized harmonic number `H_j^{(5)} = ∑_{v=1}^j v⁻⁵`. -/
def H5 (j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, 1 / (v : ℚ) ^ 5

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/TauBound.lean:18-19 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `τ(P) = L(P''')/24`. -/
noncomputable def tau (P : ℚ[X]) : ℚ := Lb (derivative^[3] P) / 24

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/PoleFun.lean:41-43 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The functional `τ_X`. -/
noncomputable def tauX (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  C (tau (polyPart A Pl)) + ∑ r ∈ Pl, C (resP A Pl r) * (C (H5 (dd r)) - X)

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:43-46 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The pole values (2.3), as polynomials in the indeterminate `X`:
`μ_X(1/(t + j²)) = j⁴ (X - H_j^{(5)}) - 1/4 + 1/(2j)`. -/
noncomputable def poleValue (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (H5 j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:48-54 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `μ_X(P(t) / D_K(t))` for a polynomial `P` in `t`, as a polynomial in `X`.
Since `D_K` is monic with the simple roots `t = -j²` (`1 ≤ j ≤ K`),
`P / D_K = (P /ₘ D_K) + ∑_j (P(-j²) / D_K'(-j²)) / (t + j²)`, and `μ_X` is applied termwise. -/
noncomputable def μX (K : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (μpoly (P /ₘ D K)) +
    ∑ j ∈ Icc 1 K,
      C (P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)) * poleValue j

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:113-114 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `pull K P = (-1)^K x⁵ P(-x²)`. -/
noncomputable def pull (K : ℕ) (P : ℚ[X]) : ℚ[X] := C ((-1 : ℚ) ^ K) * X ^ 5 * P.comp (-X ^ 2)

/-! ### The upstream definitions are the general ones at `s = 5` -/

theorem poleValue_eq_poleValueS (j : ℕ) : poleValue j = poleValueS 5 j := by
  unfold poleValue poleValueS
  have h : H5 j = Hs 5 j := rfl
  rw [h]
  norm_num

theorem pull_eq_pullS (K : ℕ) (P : ℚ[X]) : pull K P = pullS 5 K P := rfl


theorem tau_eq_tauS (P : ℚ[X]) : tau P = tauS 5 P := by
  unfold tau tauS
  norm_num [Nat.factorial]

theorem H5_eq_Hs (j : ℕ) : H5 j = Hs 5 j := rfl

theorem tauX_eq_tauXs (A : ℚ[X]) (Pl : Finset ℤ) : tauX A Pl = tauXs 5 A Pl := by
  unfold tauX tauXs
  simp only [tau_eq_tauS, H5_eq_Hs]

theorem μmono_eq_μmonoS (e : ℕ) : μmono e = μmonoS 5 e := by
  unfold μmono μmonoS
  have h1 : (2 * e + 5).factorial = (2 * e + 5) * (2 * e + 4).factorial :=
    Nat.factorial_succ (2 * e + 4)
  have h2 : (2 * e + 4).factorial = (2 * e + 4) * (2 * e + 3).factorial :=
    Nat.factorial_succ (2 * e + 3)
  have h3 : (2 * e + 3).factorial = (2 * e + 3) * (2 * e + 2).factorial :=
    Nat.factorial_succ (2 * e + 2)
  have h4 : ((5 - 1 : ℕ).factorial : ℚ) = 24 := by norm_num [Nat.factorial]
  have h0 : ((2 * e + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * e + 2).factorial_ne_zero
  rw [h1, h2, h3, h4]
  push_cast
  field_simp

theorem μpoly_eq_μpolyS (P : ℚ[X]) : μpoly P = μpolyS 5 P := by
  unfold μpoly μpolyS
  simp only [μmono_eq_μmonoS]

theorem μX_eq_μXS (K : ℕ) (P : ℚ[X]) : μX K P = μXS 5 K P := by
  unfold μX μXS
  simp only [μpoly_eq_μpolyS, poleValue_eq_poleValueS]

/-! ### The upstream theorems, from the general-`s` theorems -/

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/TauBound.lean:115-120 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauS_bound`
/-- **(3.9)**: `v_p(τ(P)) ≥ β - 4 ⌊log_p (d+1)⌋ - v_p(24)` if `deg P ≤ d` and
`v_p(P(m)) ≥ β` for `0 ≤ m ≤ d`. -/
theorem tau_bound {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) :
    VG p (tau P) (β - 4 * Nat.log p (d + 1) - padicValNat p 24) := by
  rw [tau_eq_tauS]
  have h := tauS_bound (p := p) 5 (by norm_num) hd hv
  have e1 : (5 - 1 : ℕ).factorial = 24 := rfl
  have e2 : ((5 : ℕ) : ℚ) - 1 = 4 := by norm_num
  rw [e1, e2] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/DirectBound.lean:84 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `VG_Hs`
lemma VG_H5 {m : ℕ} (hm : m < p ^ 2) : VG p (H5 m) (-5) := by
  rw [H5_eq_Hs]
  have h := VG_Hs (p := p) 5 hm
  have e : (-((5 : ℕ) : ℚ)) = -5 := by norm_num
  rw [e] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/DirectPoly.lean:264-268 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauXs_direct`
/-- **The direct bound** `v_p^G(τ_X(g)) ≥ min_c (e_c - ℓ_c) - 4`. -/
theorem tauX_direct (hp5 : 5 ≤ p) (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (hH : ∀ r ∈ Pl, dd r < p ^ 2) (hdeg : Z.card - Pl.card + 1 < p ^ 2)
    (β : ℚ) (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card) :
    GV p (tauX (numOf κ Z) Pl) (β - 4) := by
  rw [tauX_eq_tauXs]
  have h := tauXs_direct (p := p) 5 (by norm_num) hp5 κ hκ Z Pl hsep hH hdeg β hβ
  have e2 : ((5 : ℕ) : ℚ) - 1 = 4 := by norm_num
  rw [e2] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:40-41 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauS_X_pow`
lemma tau_X_pow (n : ℕ) :
    tau (X ^ n) = (n.descFactorial 3 : ℚ) * _root_.bernoulli (n - 3) / 24 := by
  rw [tau_eq_tauS, tauS_X_pow]
  have e1 : ((5 - 1 : ℕ).factorial : ℚ) = 24 := by norm_num [Nat.factorial]
  rw [e1]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:45 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauS_X_pow_odd`
lemma tau_X_pow_odd (e : ℕ) : tau (C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5)) = μmono e := by
  rw [tau_eq_tauS, μmono_eq_μmonoS, tauS_X_pow_odd 5 (by norm_num)]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:53-54 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauS_pull_poly`
/-- `τ(x⁵ Q(-x²)) = μ(Q)`. -/
lemma tau_pull_poly (Q : ℚ[X]) : tau (X ^ 5 * Q.comp (-X ^ 2)) = μpoly Q := by
  rw [tau_eq_tauS, μpoly_eq_μpolyS, tauS_pull_poly 5 (by norm_num)]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:68 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `tauS_qS`
lemma tau_cubic (a : ℚ) : tau (-X ^ 3 - C a * X) = -1 / 4 := by
  rw [tau_eq_tauS, ← qS_two]
  have h := tauS_qS 1 a
  norm_num at h
  rw [h]; ring

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:142-145 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `polyPart_pullS`
/-- The polynomial part of the pulled-back function. -/
theorem polyPart_pull (K : ℕ) (P : ℚ[X]) :
    polyPart (pull K P) (PlK K) = X ^ 5 * (P /ₘ D K).comp (-X ^ 2) +
      ∑ j ∈ Icc 1 K, C (res K P j) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X) := by
  have h := polyPart_pullS 2 K P
  simp only [qS_two] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:187-189 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `resP_pullS`
lemma resP_pull (K : ℕ) (P : ℚ[X]) {r : ℤ} (hr : r ∈ PlK K) (hr0 : r ≠ 0) :
    resP (pull K P) (PlK K) r =
      -((r : ℚ) ^ 4 / 2) * (P.eval (-(r : ℚ) ^ 2) / (derivative (D K)).eval (-(r : ℚ) ^ 2)) := by
  exact resP_pullS 4 K P hr hr0

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:209 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `Hs_succ_eq`
lemma H5_succ_eq {j : ℕ} (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / (j : ℚ) ^ 5 := by
  exact Hs_succ_eq 5 hj

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/Pullback.lean:214-215 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `μXS_eq_tauXs`
/-- **The pullback identity (3.1)**: `μ_X(P / D_K) = τ_X((-1)^K x⁵ P(-x²) / ∏_{r ∈ PlK} (x - r))`. -/
theorem μX_eq_tauX (K : ℕ) (P : ℚ[X]) : μX K P = tauX (pull K P) (PlK K) := by
  rw [μX_eq_μXS, tauX_eq_tauXs, pull_eq_pullS]
  exact μXS_eq_tauXs 5 ⟨2, rfl⟩ (by norm_num) K P

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/TEntry.lean:23-24 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The `x`-roots of the pullback of `tpol M`. -/
def xroots (M : Multiset ℤ) : Multiset ℤ := Multiset.replicate 5 0 + M + M.map (fun γ => -γ)

theorem xroots_eq_xrootsS (M : Multiset ℤ) : xroots M = xrootsS 5 M := rfl

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/TEntry.lean:26-27 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `pullS_tpol`
lemma pull_tpol (K : ℕ) (M : Multiset ℤ) :
    pull K (tpol M) = numOf ((-1 : ℚ) ^ (K + M.card)) (xroots M) := by
  exact pullS_tpol 5 K M

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/TEntry.lean:43-47 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `cnt_xrootsS`
/-- Number of `x`-roots in the class `c`. -/
lemma cnt_xroots (p : ℕ) (M : Multiset ℤ) (c : ZMod p) :
    cnt p (xroots M) c = (if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card := by
  exact cnt_xrootsS 5 p M c

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/TEntry.lean:65-71 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `μXS_tpol_bound`
/-- **Entry bound** for `μ_X(tpol M / D_K)`. -/
theorem μX_tpol_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Sep p (PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ ((if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) - (plc p (PlK K) c).card) :
    GV p (μX K (tpol M)) (β - 4) := by
  rw [μX_eq_μXS]
  have h := μXS_tpol_bound (p := p) 5 ⟨2, rfl⟩ (by norm_num) hp5 K M hsep hK hdeg β hβ
  have e2 : ((5 : ℕ) : ℚ) - 1 = 4 := by norm_num
  rw [e2] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/MomentVal.lean:50 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `VG_inv_factorial_pred`
lemma VG_inv24 (hp5 : 5 ≤ p) : VG p ((24 : ℚ)⁻¹) 0 := by
  have h := VG_inv_factorial_pred (p := p) 5 hp5
  have e : (((5 - 1 : ℕ).factorial : ℕ) : ℚ) = 24 := by norm_num [Nat.factorial]
  rw [e] at h
  exact h

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/MomentVal.lean:54-55 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `VG_μmonoS`
/-- `v_p(μ(t^e)) ≥ -1`. -/
theorem VG_μmono (hp5 : 5 ≤ p) (e : ℕ) : VG p (μmono e) (-1) := by
  rw [μmono_eq_μmonoS]
  exact VG_μmonoS 5 (by norm_num) hp5 e

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/MomentVal.lean:67-68 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `VG_μmonoS_int`
/-- `μ(t^e)` is `p`-integral for `e < 2p - 3`. -/
theorem VG_μmono_int (hp5 : 5 ≤ p) {e : ℕ} (he : e + 3 < 2 * p) : VG p (μmono e) 0 := by
  rw [μmono_eq_μmonoS]
  exact VG_μmonoS_int 5 (by norm_num) hp5 (by omega)

/-! ### The Hankel determinant and the class-basis framework (`ν = 6`, `K = 40n`, `N = 3n`, `h = 37n`) -/

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:56-59 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The `h × h` Hankel matrix `G_K(X)` of (2.4), whose `(i, j)` entry is
`μ_X (D_N(t)^6 t^(i+j) / D_K(t))`, with `K = 40 n`, `N = 3 n`, `h = 37 n`. -/
noncomputable def G (n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] :=
  fun i j => μX (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ)))

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:61-62 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `Δ_K(X) = det G_K(X)`, a polynomial in `X` (of degree `h`, by (2.9)). -/
noncomputable def Δ (n : ℕ) : ℚ[X] := (G n).det

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/ClassFrame.lean:86-89 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The `t`-roots of the numerator `D_N⁶ E_s E_t`. -/
def entryRoots {m : ℕ} (N : ℕ) (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    Multiset ℤ :=
  6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)) + classRoots L s.1 s.2 + classRoots L t.1 t.2

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/ClassFrame.lean:91-94 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The per-class count appearing in the entry bound. -/
noncomputable def classCount (p : ℕ) (K : ℕ) (M : Multiset ℤ) (c : ZMod p) : ℚ :=
  (((if c = 0 then 5 else 0) + (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
    (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) : ℚ) - (plc p (PlK K) c).card

theorem G_eq_GS (n : ℕ) : G n = GS 5 6 (40 * n) (3 * n) (37 * n) := by
  funext i j
  exact μX_eq_μXS _ _

theorem Δ_eq_ΔS (n : ℕ) : Δ n = ΔS 5 6 (40 * n) (3 * n) (37 * n) := by
  unfold Δ ΔS
  rw [G_eq_GS]

theorem entryRoots_eq_entryRootsS {m : ℕ} (N : ℕ) (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) : entryRoots N L s t = entryRootsS 6 N L s t := rfl

theorem classCount_eq_classCountS (p : ℕ) (K : ℕ) (M : Multiset ℤ) (c : ZMod p) :
    classCount p K M c = classCountS 5 p K M c := rfl

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/BasisChange.lean:75-79 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `det_basis_changeS`
/-- **Change of basis**. -/
theorem det_basis_change (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((coeffMat E).det ^ 2) * Δ n := by
  rw [Δ_eq_ΔS, ← det_basis_changeS 5 6 (40 * n) (3 * n) (37 * n) E hE]
  simp only [μX_eq_μXS]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/ClassFrame.lean:96-104 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `class_frameS`
/-- **The class-basis framework**: `v_p^G(Δ) ≥ 2 ∑ w`. -/
theorem class_frame {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {m : ℕ} (hm : 2 * m + 1 = p)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (w : (Σ a : Fin (m + 1), Fin (L a)) → ℚ)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hentry : ∀ s t : (Σ a : Fin (m + 1), Fin (L a)), ∀ c : ZMod p,
      w s + w t + 4 ≤ classCount p (40 * n) (entryRoots (3 * n) L s t) c) :
    GV p (Δ n) (2 * ∑ s, w s) := by
  rw [Δ_eq_ΔS]
  refine class_frameS 5 ⟨2, rfl⟩ (by norm_num) hp5 hm 6 (40 * n) (3 * n) (37 * n) L hL w hsep hK
    (by omega) (fun x y c => ?_)
  have h := hentry x y c
  have e : ((5 : ℕ) : ℚ) - 1 = 4 := by norm_num
  rw [e]
  exact h

/-! ### The inner-range bound (`Apery/Arith/ClassCount.lean`, `InnerWeights.lean`) -/

section Inner

variable {m : ℕ}

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/ClassCount.lean:101-103 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The class constant `5[a = 0] + 6 S_N(a) - S_K(a)`. -/
noncomputable def Bse (p K N : ℕ) (a : ℕ) : ℚ :=
  (if a = 0 then 5 else 0) + 6 * (SX p N (((a : ℤ) : ZMod p)) : ℚ) - SX p K (((a : ℤ) : ZMod p))

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/InnerWeights.lean:20-22 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `top a = L a + (b a - 4)/2`. -/
noncomputable def topw (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (a : Fin (m + 1)) : ℚ :=
  L a + (b a - 4) / 2

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/InnerWeights.lean:24-26 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The minimum of `top` over the ordinary classes. -/
noncomputable def tmin (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) : ℚ :=
  (Finset.univ.erase (0 : Fin (m + 1))).inf' ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩ (topw L b)

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/InnerWeights.lean:112-114 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- Uncapped weights. -/
noncomputable def wraw (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - 4) / 2 else (s.2 : ℚ) + (b s.1 - 4) / 2

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/InnerWeights.lean:116-119 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- Capped weights `min (wraw) (min_{c ≠ 0} top c)`. -/
noncomputable def wcap (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  min (wraw L b s) (tmin hm L b)

theorem Bse_eq_BseS (p K N : ℕ) : Bse p K N = BseS 5 6 p K N := by
  funext a
  unfold Bse BseS
  norm_num

theorem tmin_eq_tminS (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) :
    tmin hm L b = tminS 4 hm L b := rfl

theorem wcap_eq_wcapS (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : wcap hm L b s = wcapS 4 hm L b s := rfl

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/InnerWeights.lean:177-184 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `inner_bound_capS`
/-- **Inner-range determinant bound** with capped weights; only the zero-class condition. -/
theorem inner_bound_cap {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hZ : tmin hm1 L (Bse p (40 * n) (3 * n)) ≤
      2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, wcap hm1 L (Bse p (40 * n) (3 * n)) s) := by
  have e : ((5 : ℕ) : ℚ) - 1 = 4 := by norm_num
  have h := inner_bound_capS (p := p) 5 ⟨2, rfl⟩ (by norm_num) hp5 hm hm1 6 (40 * n) (3 * n)
    (37 * n) L hL hsep hK (by omega)
  rw [e, ← Bse_eq_BseS] at h
  rw [Δ_eq_ΔS]
  exact h hZ

end Inner

/-! ### Pole values, small primes, the outer frame -/

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/PoleVal.lean:169-171 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `GV_poleValueS_congr`
/-- **The congruence** `poleValue (p - c) ≡ poleValue c (mod p)` for `1 ≤ c < p`. -/
theorem GV_poleValue_congr (hp3 : 3 ≤ p) {c : ℕ} (hc : 1 ≤ c) (hcp : c < p) :
    GV p (poleValue (p - c) - poleValue c) 1 := by
  rw [poleValue_eq_poleValueS, poleValue_eq_poleValueS]
  exact GV_poleValueS_congr 5 ⟨2, rfl⟩ hp3 hc hcp

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/SmallPrimeTau.lean:80-84 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `crude_tauXs`
/-- **The analogue of Lemma 3.3** for the poles `±1, …, ±K`. -/
theorem crude_tauX {K d : ℕ} (hK : 1 ≤ K) (hdK : 2 * K ≤ d) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (d + 1) : ℚ) - padicValNat p 24) := by
  rw [tauX_eq_tauXs]
  have h := crude_tauXs (p := p) 5 (by norm_num) hK hdK A hA hint
  have e1 : (-(((5 : ℕ) : ℚ) + 1)) = -6 := by norm_num
  have e2 : (5 - 1 : ℕ).factorial = 24 := rfl
  rw [e1, e2] at h
  exact h

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:64-68 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The scalar `S_K` of (2.5). -/
noncomputable def S (n : ℕ) : ℚ :=
  ((40 * n).factorial : ℚ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) /
    (((3 * n).factorial : ℚ) ^ (12 * (37 * n)) *
      ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℚ) ^ 2)

-- adapted from mo271/Zeta5@be1c0d82 Apery/Construction.lean:70-71 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- `F_K = S_K Δ_K` of (2.5). -/
noncomputable def F (n : ℕ) : ℚ[X] := C (S n) * Δ n

theorem S_eq_SS (n : ℕ) : S n = SS 6 (40 * n) (3 * n) (37 * n) := by
  unfold S SS
  rw [show 2 * 6 * (37 * n) = 12 * (37 * n) by ring]

theorem F_eq_FS (n : ℕ) : F n = FS 5 6 (40 * n) (3 * n) (37 * n) := by
  unfold F FS
  rw [S_eq_SS, Δ_eq_ΔS]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/SmallPrimeF.lean:200-202 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `small_prime_boundS` and monotonicity of `Nat.log` (184 n + 2 ≤ 200 n)
/-- **The bound (3.12)** at every prime. -/
theorem small_prime_bound {n : ℕ} (hn : 1 ≤ n) :
    GV p (F n) (-(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℚ) + (37 * n : ℕ) * padicValNat p 24)) := by
  rw [F_eq_FS]
  have h := small_prime_boundS (p := p) 5 ⟨2, rfl⟩ (by norm_num) 6 (40 * n) (3 * n) (37 * n)
    (by omega) (by omega) (by omega)
  refine h.mono ?_
  have hlog : (Nat.log p (5 + 2 * (6 * (3 * n)) + 4 * (37 * n - 1) + 1) : ℚ) ≤
      Nat.log p (200 * n) := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have hH : (0 : ℚ) ≤ ((37 * n : ℕ) : ℚ) := Nat.cast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num : (0 : ℚ) ≤ 6) hH)
  have e2 : (5 - 1 : ℕ).factorial = 24 := rfl
  have e5 : ((5 : ℕ) : ℚ) + 1 = 6 := by norm_num
  rw [e2, e5]
  linarith

-- adapted from mo271/Zeta5@be1c0d82 Apery/Arith/OuterFrame.lean:22-24 (Firsching; Paul-Lez), Apache-2.0 [verbatim]
/-- The moments `e ≥ 2p - 3` of a polynomial. -/
noncomputable def μGe (p : ℕ) (Q : ℚ[X]) : ℚ :=
  ∑ e ∈ range (Q.natDegree + 1), if 2 * p ≤ e + 3 then Q.coeff e * μmono e else 0

theorem μGe_eq_μGeS (p : ℕ) (Q : ℚ[X]) : μGe p Q = μGeS 5 (2 * p - 3) Q := by
  unfold μGe μGeS
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [μmono_eq_μmonoS]
  by_cases h : 2 * p ≤ e + 3
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

-- statement copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterFrame.lean:95-108 (Firsching; Paul-Lez), Apache-2.0; proof: specialisation of `outer_frameS` at threshold `T = 2p - 3`
/-- **The outer-range framework.** -/
theorem outer_frame (hp5 : 5 ≤ p) (n : ℕ) (Ez : Fin (37 * n) → ℤ[X])
    (hdegZ : ∀ s, (Ez s).natDegree < 37 * n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (Lc : ι → ℕ) (cls : Fin (37 * n) → ι)
    (idx : Fin (37 * n) → ℕ) (hidx : ∀ a, idx a < Lc (cls a))
    (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ Lc c) * (X - C (γ (cls a))) ^ idx a)
    (w : Fin (37 * n) → ℚ) (hw : ∀ s, w s ≤ 0)
    (hA : ∀ s t, GV p (μX (40 * n) (D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) -
      C (μGe p ((D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) /ₘ D (40 * n)))) (w s + w t)) :
    GV p (Δ n) (2 * ∑ s, w s - ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  rw [Δ_eq_ΔS]
  have h := outer_frameS (p := p) 5 (by norm_num) hp5 (2 * p - 3) 6 (40 * n) (3 * n) (37 * n)
    (by omega) Ez hdegZ γ hγ Lc cls idx hidx hinj hred w hw (fun s t => by
      have := hA s t
      rw [μX_eq_μXS, μGe_eq_μGeS] at this
      exact this)
  have e : 2 * p - 3 + 40 * n - 6 * (3 * n) = 2 * p + 22 * n - 3 := by omega
  rw [e] at h
  exact h

end AperyS.Upstream
