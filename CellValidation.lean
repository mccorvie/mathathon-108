import FieldData
/- PROOF-DRAFT checked rational cell/cover data. Codex lane C.
Fauzan re-derivation reusing Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert
theorem all_route_ok : ∀ r ∈ routed, RouteOK uRows vRows critical r := by decide +kernel
theorem all_cell_ok : ∀ r ∈ routed, CellOK tau r.cell := by decide +kernel
theorem chain_ok : Chain 0 2 cells := by decide +kernel
#print axioms all_route_ok
#print axioms all_cell_ok
#print axioms chain_ok
end CFieldCert
