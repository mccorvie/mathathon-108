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

theorem u_block_100 : ∀ r ∈ (uRows.drop 100).take 2, UOK numeric r := by
  decide +kernel

end CFieldCert
