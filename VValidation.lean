import FieldData
/- PROOF-DRAFT checked rational V data. Codex lane C.
Fauzan re-derivation reusing Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert
theorem all_v_ok : ∀ r ∈ vRows, VOK numeric r := by decide +kernel
theorem critical_ok : CriticalOK numeric critical := by decide +kernel
#print axioms all_v_ok
#print axioms critical_ok
end CFieldCert
