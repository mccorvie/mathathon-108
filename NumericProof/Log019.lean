import NumericData

/- E608 PROOF-DRAFT kernel-checked numerical block; Codex lane C.
Fauzan re-derivation using Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CPrimitive

theorem log_ok_019 : logRows019.all checkLog = true := by
  decide +kernel

#print axioms log_ok_019
end CPrimitive
