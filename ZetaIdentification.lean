import Statement

/-!
B14/E416: identify the actual B8 real zeta sum with Mathlib riemannZeta.
Codex lane B; PROOF-DRAFT until repository gate.
Adapted from mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645,
Apery/Zeta5.lean:13-18, Moritz Firsching and Paul-Lez, Apache-2.0.
Only exponent5 is replaced by arbitrary natural s>=2. No irrationality claim.
-/
namespace BZetaIdentification

/-- Mathlib's standard complex zeta value equals the actual imported B8 real zeta sum. -/
theorem riemannZeta_eq_zetaS (s : ℕ) (hs : 2 ≤ s) :
    riemannZeta (s : ℂ) = (BAnalyticPoles.zetaS s : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := s) (by omega)
  rw [h, BAnalyticPoles.zetaS, Complex.ofReal_tsum]
  push_cast
  rfl

#print axioms BZetaIdentification.riemannZeta_eq_zetaS
end BZetaIdentification
