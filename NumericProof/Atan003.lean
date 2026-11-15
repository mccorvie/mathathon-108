import NumericData

/- E608 PROOF-DRAFT kernel-checked numerical block; Codex lane C.
Fauzan re-derivation using Firsching; Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CPrimitive

theorem atan_ok_003 : (List.range' 192 64).all (fun i => checkAtan sqrtRows atanRows 2 i) = true := by
  decide +kernel

#print axioms atan_ok_003
end CPrimitive
