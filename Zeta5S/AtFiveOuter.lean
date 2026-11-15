import Zeta5S.AtFive
import Zeta5S.OuterScope

-- Codex lane L, L7 stage 3. Original definitions and statement copied unchanged.
-- Source: Firsching/Paul-Lez mo271/Zeta5@be1c0d82, Apache-2.0.
open Finset Polynomial
namespace AperyS.Upstream
variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable (hm : 2 * m + 1 = p) (n : ℕ)

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterBasis.lean:44-45 (Firsching; Paul-Lez), Apache-2.0
/-- Tail poles `N < j ≤ K`. -/
def tailO (n : ℕ) : Finset ℕ := Icc (3 * n + 1) (40 * n)

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterBasis.lean:47-47 (Firsching; Paul-Lez), Apache-2.0
def tailC (c : Fin (m + 1)) : Finset ℕ := (tailO n).filter fun j => jc hm j = c

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterBasis.lean:49-49 (Firsching; Paul-Lez), Apache-2.0
def LoC (c : Fin (m + 1)) : ℕ := (tailC hm n c).card

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterBasis.lean:51-51 (Firsching; Paul-Lez), Apache-2.0
def bigC (c : Fin (m + 1)) : Finset ℕ := (tailC hm n c).filter fun j => p < j

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterBasis.lean:53-53 (Firsching; Paul-Lez), Apache-2.0
def nbC (c : Fin (m + 1)) : ℕ := (bigC hm n c).card

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterEntryMain.lean:83-84 (Firsching; Paul-Lez), Apache-2.0
/-- `ℓ(c) = #{j ≤ K : j ≡ ±c}`. -/
def ellC (c : Fin (m + 1)) : ℕ := ((Icc 1 (40 * n)).filter fun j => jc hm j = c).card

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterEntryMain.lean:86-87 (Firsching; Paul-Lez), Apache-2.0
/-- `δ(c) = [c ≤ N]`. -/
def delC (c : Fin (m + 1)) : ℕ := if (c : ℕ) ≤ 3 * n then 1 else 0

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterEntryMain.lean:89-92 (Firsching; Paul-Lez), Apache-2.0
/-- The outer weights (4.12). -/
noncomputable def wO (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  if c = 0 then (if i < nbC hm n 0 then -2 else if nbC hm n 0 = 0 then -1 / 2 else 0)
  else (if i < nbC hm n c then min 0 ((i : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2) else 0)

-- copied from mo271/Zeta5@be1c0d82 Apery/Arith/OuterEntryMain.lean:482-509 (Firsching; Paul-Lez), Apache-2.0
/-- **The outer-range bound** `v^G(Δ) ≥ 2 ∑ w − r`. -/
theorem outer_bound (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) :
    GV p (Δ n) (2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  have hd : 40 * n - 3 * n = 37 * n := by omega
  have hT : momentCutS 5 p = 2 * p - 3 := by unfold momentCutS; norm_num; omega
  have ha : momentCutS 5 p + 40 * n - 6 * (3 * n) = 2 * p + 22 * n - 3 := by
    rw [hT]; omega
  have hL : ∀ c, LoC hm n c = AperyS.LoC hm (3 * n) (40 * n) c := by intro c; rfl
  have hw : ∀ c i, wO hm n c i = AperyS.wO hm 5 6 (3 * n) (40 * n) c i := by
    intro c i
    dsimp only [wO, AperyS.wO]
    norm_num
    rfl
  have h := outer_boundS_moment hm 5 6 (3 * n) (40 * n) ⟨2, rfl⟩ (by norm_num)
    (by omega) (by norm_num) hp7 hK3 hK hpN
  rw [hd, ha, ← Δ_eq_ΔS] at h
  simpa only [← hL, ← hw] using h

end AperyS.Upstream
