import Mathathon.P108.DeltaEq.Bridge

/-!
# #108 L4: the literal Hankel lists are the defining expressions (kernel check)

EVENT WORK (#108, lane L task L4, Claude Opus 5.5, Sat Nov 14 2026). `decide +kernel` (kernel
reduction only; no `native_decide`): the 73 values `g0C m` (division recurrence, Bernoulli
numbers, residues; `DetG0.g0List`) and the 73 values `g1C m` equal the literals of
`HankelData.lean`.
-/

namespace Mathathon.P108.Skip.DeltaEq

set_option profiler true in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem hankel_lits : DetG0.g0List = g0Q ∧ g1List = g1Q := by decide +kernel

end Mathathon.P108.Skip.DeltaEq
