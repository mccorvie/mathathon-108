import BInnerStatement
import BInnerLimitFinish
import Transfer
/- E429 Codex inner_regularity, laneB. CONJECTURE target before proof:
This is only the PNT transfer implication; actual localcost remains a premise. -/
namespace BInnerSum
open Mathathon.P108.RangeBridgeTarget Mathathon.P108.InnerExplicitTarget

def InnerTransferStatement : Prop :=
  InnerExplicitLocalStatement → InnerExplicitLimitStatement
end BInnerSum
