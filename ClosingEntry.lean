import SplitEntry

/- PROOF-DRAFT until the receiving final gate. Codex lane L supplement.
Compatibility composition for the E612 receiving request (BOARD Sat22:12).
Fauzan/Firsching/Paul-Lez and lane C credits are retained in the imported proofs.
The CCompact interface now has u=-2650371/2000000 and cutoff1000000. -/
namespace CCompactWithClosing
theorem closing : CCompact.ClosingStatement := CCertificateSplit.closing
theorem irrational_five (hFinite : CCompact.FiniteRealBoundStatement) :
    ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  CCompactCurrent.irrational_five hFinite closing
end CCompactWithClosing
