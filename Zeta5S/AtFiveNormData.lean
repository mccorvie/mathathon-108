import Zeta5S.AtFiveOuter
import Zeta5S.InnerAlloc

-- L7/R2 exponent-data anchors. Source definitions only; proofs are separate.
open Finset Polynomial Classical
namespace AperyS.Upstream
noncomputable section

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:26-27 (Firsching; Paul-Lez), Apache-2.0
/-- The cutoff `M` separating small primes from the inner range. -/
def Mcut : ℕ := 400

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:29-30 (Firsching; Paul-Lez), Apache-2.0
/-- `v_p(S_K)`. -/
noncomputable def vSK (n p : ℕ) : ℤ := padicValRat p (S n)

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:32-34 (Firsching; Paul-Lez), Apache-2.0
/-- The small-prime exponent (3.12). -/
noncomputable def Lsmall (n p : ℕ) : ℤ :=
  -(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℤ) + (37 * n : ℕ) * (padicValNat p 24 : ℤ))

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:36-38 (Firsching; Paul-Lez), Apache-2.0
/-- The class offsets `β_c = 6 ℓ_N(c) - ℓ_K(c) - 4`. -/
noncomputable def betaI (n p : ℕ) {m : ℕ} (c : Fin (m + 1)) : ℤ :=
  6 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - 4

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:40-41 (Firsching; Paul-Lez), Apache-2.0
/-- The water-filling parameters. -/
def kloI (n p : ℕ) : ℤ := -2 * ((40 * n / p : ℕ) : ℤ) - 6

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:42-42 (Firsching; Paul-Lez), Apache-2.0
def ktopI (n p : ℕ) : ℤ := 8 * ((40 * n / p : ℕ) : ℤ) + 20

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:43-43 (Firsching; Paul-Lez), Apache-2.0
def L0I (n p : ℕ) : ℕ := 3 * (40 * n / p) + 6

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:45-48 (Firsching; Paul-Lez), Apache-2.0
/-- The inner allocation. -/
noncomputable def allocI (n p m : ℕ) : Fin (m + 1) → ℕ :=
  allocK (betaI n p (m := m)) (37 * n)
    (kfSel (betaI n p (m := m)) (37 * n) (L0I n p) (kloI n p) (ktopI n p))

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:50-56 (Firsching; Paul-Lez), Apache-2.0
/-- The side conditions of the inner bound. -/
def InnerOK (n p : ℕ) : Prop :=
  ∃ hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2, 5 ≤ p ∧ Sep p (PlK (40 * n)) ∧ 40 * n < p ^ 2 ∧
    5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2 ∧
    ∑ c, allocI n p (p / 2) c = 37 * n ∧
    tmin hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) ≤
      2 * (allocI n p (p / 2) 0 : ℚ) + (Bse p (40 * n) (3 * n) 0 - 4) / 2

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:58-60 (Firsching; Paul-Lez), Apache-2.0
/-- The inner weight sum (for `m = p / 2`). -/
noncomputable def WI (n p : ℕ) : ℚ :=
  if hm1 : 1 ≤ p / 2 then ∑ s, wcap hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) s else 0

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:62-64 (Firsching; Paul-Lez), Apache-2.0
/-- The side conditions of the outer bound. -/
def OuterOK (n p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ 7 ≤ p ∧ 40 * n < 3 * p ∧ 2 * (40 * n) < p ^ 2 ∧ 3 * n < p

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:66-74 (Firsching; Paul-Lez), Apache-2.0
/-- The outer weight sum minus the rank loss (for `m = p / 2`). -/
noncomputable def WO (n p : ℕ) : ℚ :=
  if hpp : p.Prime then
    if hm : 2 * (p / 2) + 1 = p then
      haveI : Fact p.Prime := ⟨hpp⟩
      2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)
    else 0
  else 0

-- copied from mo271/Zeta5@be1c0d82 Apery/Norm.lean:77-82 (Firsching; Paul-Lez), Apache-2.0
/-- **The local exponent.** -/
noncomputable def Lp (n p : ℕ) : ℤ :=
  if p * Mcut ≤ 40 * n then Lsmall n p
  else if 3 * p ≤ 40 * n then
    (if InnerOK n p then vSK n p + ⌊2 * WI n p⌋ else Lsmall n p)
  else (if OuterOK n p then vSK n p + ⌊WO n p⌋ else Lsmall n p)

end
end AperyS.Upstream
