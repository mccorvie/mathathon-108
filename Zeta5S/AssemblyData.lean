import Zeta5S.OuterScope
import Zeta5S.InnerWeights
import Zeta5S.SmallPrimeF

/-!
L7 stage 4 / E303: definitions of the approved assembly statements.
Codex lane L, Sat Nov 14 2026. Corresponding proof declarations are in
AssemblyProof and NormalizationProof; their status is in the claims ledger.

Definitions adapt Firsching/Paul-Lez mo271/Zeta5@be1c0d82, Apache-2.0,
Apery/Norm.lean:27-90,146-155,269-291. Existing AperyS objects come from
the L7 probe. This target uses the upstream raw outer loss, not E13's
sharper min(rank, zero-count) correction. The allocation is supplied as
explicit data and tested by InnerOK; no closed water-filling window or
asymptotic arithmetic exponent is claimed. No sorry or axiom is declared.
-/

open Finset Polynomial

namespace AperyS.AssemblyTarget

noncomputable section

abbrev Allocations := (p : ℕ) → Fin (p / 2 + 1) → ℕ

def degreeBound (s ν K N : ℕ) : ℕ := s + 2 * (ν * N) + 4 * ((K - N) - 1)

def Lsmall (s ν K N p : ℕ) : ℤ :=
  -(((s + 1 : ℕ) : ℤ) * (K - N : ℕ) * Nat.log p (degreeBound s ν K N + 1) +
    (K - N : ℕ) * (padicValNat p (s - 1).factorial : ℤ))

def vSK (ν K N p : ℕ) : ℤ := padicValRat p (SS ν K N (K - N))

def InnerOK (s ν K N p : ℕ) (L : Allocations) : Prop :=
  ∃ hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2,
    s ≤ p ∧ Sep p (PlK K) ∧ K < p ^ 2 ∧
    s + 2 * (ν * N + 2 * (K - N)) - 2 * K + 1 < p ^ 2 ∧
    ∑ c, L p c = K - N ∧
    tminS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) ≤
      2 * (L p 0 : ℚ) + (BseS s ν p K N 0 - ((s : ℚ) - 1)) / 2

def WI (s ν K N p : ℕ) (L : Allocations) : ℚ := by
  classical
  exact if hm1 : 1 ≤ p / 2 then
    ∑ x, wcapS ((s : ℚ) - 1) hm1 (L p) (BseS s ν p K N) x
  else 0

def OuterOK (s K N p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ s ≤ p ∧ 7 ≤ p ∧ K < 3 * p ∧ 2 * K < p ^ 2 ∧ N < p

def WO (s ν K N p : ℕ) : ℚ := by
  classical
  exact if hpp : p.Prime then
    letI : Fact p.Prime := ⟨hpp⟩
    if hm : 2 * (p / 2) + 1 = p then
      2 * ∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i -
        ((min (K - N) (K + (ν - 2) * N - ((s - 1) / 2) * (p - 1)) : ℕ) : ℚ)
    else 0
  else 0

def Lp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WO s ν K N p⌋
  else Lsmall s ν K N p

/-- Prime support is enlarged to cover small finite K and arbitrary s.
For the upstream shape (s=5,K=40n,N=3n,n>=1), this is 2h=74n. -/
def primeBound (s K N : ℕ) : ℕ := max 7 (max s (2 * (K - N)))

def normalizer (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-Lp s ν K N M p L)

/-- Approved local valuation proposition. Its proof is
`local_valuation_statement` in AssemblyProof (LEAN-CHECKED, human comparison pending). -/
def LocalValuationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∀ (p : ℕ) (_ : Fact p.Prime),
      GV p (FS s ν K N (K - N)) (Lp s ν K N M p L)

/-- Approved integrality proposition. Its proof is
`normalization_statement` in NormalizationProof (LEAN-CHECKED, human comparison pending). -/
def NormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizer s ν K N M L) * FS s ν K N (K - N)


end
end AperyS.AssemblyTarget
