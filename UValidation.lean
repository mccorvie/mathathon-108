import FieldData
/- PROOF-DRAFT checked rational U data. Codex lane C.
Fauzan re-derivation reusing Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert
theorem all_u_ok : ∀ r ∈ uRows, UOK numeric r := by decide +kernel
#print axioms all_u_ok
end CFieldCert
