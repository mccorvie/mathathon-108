import FieldData

/-!
PROOF-DRAFT: small-row kernel certificate, Codex gpt-6.1-sol lane C.
Fauzan re-derivation reusing Moritz Firsching mo271/Zeta5@be1c0d82,
Apache-2.0; Paul-Lez Comparator metadata; original U/B/C credits retained.
Memory split only: unchanged data, predicate, and bound.
-/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert

theorem u_block_064 : ∀ r ∈ (uRows.drop 64).take 4, UOK numeric r := by
  decide +kernel

end CFieldCert
