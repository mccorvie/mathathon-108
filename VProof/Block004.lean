import FieldData
/- PROOF-DRAFT: partitioned rational V checks. Codex gpt-6.1-sol, lane C.
Fauzan re-derivation using Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert
theorem v_block_004 : ∀ r ∈ (vRows.drop 16).take 4, VOK numeric r := by
  decide +kernel
#print axioms v_block_004
end CFieldCert
