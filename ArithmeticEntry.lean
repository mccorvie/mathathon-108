import Assembly
import CArithProofs
import LeadingInstance

/-!
E601 / C4, Codex GPT-6.1 sol lane C, 2026-11-14.
PROOF-DRAFT: the current most-specific endpoint, pending receiving gate.
A re-derivation of Fauzan's theorem reusing Firsching's formalisation
(mo271/Zeta5@be1c0d82, Apache-2.0; Comparator metadata Paul-Lez).
CArithInstance supplies actual E311/E432 instances; CLeadingInstance supplies
the fixed-s finite-to-leading link. Only finite analysis and scalar closing
remain caller hypotheses. No arithmetic/normalizer/zeta correspondence premise
or Gaussian-decay premise remains in this endpoint.
-/
namespace CCompactCurrent

/-- PROOF-DRAFT: precisely the two producer leaves not yet imported here. -/
theorem irrational_five
    (hFinite : CCompact.FiniteRealBoundStatement)
    (hClosing : CCompact.ClosingStatement) :
    ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  CCompact.irrational_five CArithInstance.degree_bound CArithInstance.normalization
    CArithInstance.normalizer_growth (CLeadingInstance.analytic_leading_of_finite hFinite)
    hClosing CArithInstance.margin_identity CArithInstance.zeta_identification

#print axioms irrational_five
#check irrational_five
end CCompactCurrent
