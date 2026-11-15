import UProof.Block000
import UProof.Block004
import UProof.Block008
import UProof.Block012
import UProof.Block016
import UProof.Block020
import UProof.Block024
import UProof.Block028
import UProof.Block032
import UProof.Block036
import UProof.Block040
import UProof.Block044
import UProof.Block048
import UProof.Block052
import UProof.Block056
import UProof.Block060
import UProof.Block064
import UProof.Block068
import UProof.Block072
import UProof.Block074
import UProof.Block076
import UProof.Block078
import UProof.Block080
import UProof.Block082
import UProof.Block084
import UProof.Block086
import UProof.Block088
import UProof.Block090
import UProof.Block092
import UProof.Block094
import UProof.Block096
import UProof.Block098
import UProof.Block100
import UProof.Block102
import UProof.Block104
import UProof.Block106
import UProof.Block108
import UProof.Block110
import UProof.Block111
import UProof.Block112
import UProof.Block113
import UProof.Block114
import UProof.Block115
import UProof.Block116
import UProof.Block117
import UProof.Block118
import UProof.Block119
import UProof.Block120
import UProof.Block121
import UProof.Block122
import UProof.Block123
import UProof.Block124
import UProof.Block125
import UProof.Block126

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

private theorem all_u_append {xs ys : List UPoint}
    (hx : ∀ r ∈ xs, UOK numeric r) (hy : ∀ r ∈ ys, UOK numeric r) :
    ∀ r ∈ xs ++ ys, UOK numeric r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  · exact hy r hr

theorem all_u_ok : ∀ r ∈ uRows, UOK numeric r := by
  change ∀ r ∈
    ((uRows.drop 0).take 4 ++
    ((uRows.drop 4).take 4 ++
    ((uRows.drop 8).take 4 ++
    ((uRows.drop 12).take 4 ++
    ((uRows.drop 16).take 4 ++
    ((uRows.drop 20).take 4 ++
    ((uRows.drop 24).take 4 ++
    ((uRows.drop 28).take 4 ++
    ((uRows.drop 32).take 4 ++
    ((uRows.drop 36).take 4 ++
    ((uRows.drop 40).take 4 ++
    ((uRows.drop 44).take 4 ++
    ((uRows.drop 48).take 4 ++
    ((uRows.drop 52).take 4 ++
    ((uRows.drop 56).take 4 ++
    ((uRows.drop 60).take 4 ++
    ((uRows.drop 64).take 4 ++
    ((uRows.drop 68).take 4 ++
    ((uRows.drop 72).take 2 ++
    ((uRows.drop 74).take 2 ++
    ((uRows.drop 76).take 2 ++
    ((uRows.drop 78).take 2 ++
    ((uRows.drop 80).take 2 ++
    ((uRows.drop 82).take 2 ++
    ((uRows.drop 84).take 2 ++
    ((uRows.drop 86).take 2 ++
    ((uRows.drop 88).take 2 ++
    ((uRows.drop 90).take 2 ++
    ((uRows.drop 92).take 2 ++
    ((uRows.drop 94).take 2 ++
    ((uRows.drop 96).take 2 ++
    ((uRows.drop 98).take 2 ++
    ((uRows.drop 100).take 2 ++
    ((uRows.drop 102).take 2 ++
    ((uRows.drop 104).take 2 ++
    ((uRows.drop 106).take 2 ++
    ((uRows.drop 108).take 2 ++
    ((uRows.drop 110).take 1 ++
    ((uRows.drop 111).take 1 ++
    ((uRows.drop 112).take 1 ++
    ((uRows.drop 113).take 1 ++
    ((uRows.drop 114).take 1 ++
    ((uRows.drop 115).take 1 ++
    ((uRows.drop 116).take 1 ++
    ((uRows.drop 117).take 1 ++
    ((uRows.drop 118).take 1 ++
    ((uRows.drop 119).take 1 ++
    ((uRows.drop 120).take 1 ++
    ((uRows.drop 121).take 1 ++
    ((uRows.drop 122).take 1 ++
    ((uRows.drop 123).take 1 ++
    ((uRows.drop 124).take 1 ++
    ((uRows.drop 125).take 1 ++
    (uRows.drop 126).take 1))))))))))))))))))))))))))))))))))))))))))))))))))))), UOK numeric r
  exact all_u_append u_block_000
    (all_u_append u_block_004
    (all_u_append u_block_008
    (all_u_append u_block_012
    (all_u_append u_block_016
    (all_u_append u_block_020
    (all_u_append u_block_024
    (all_u_append u_block_028
    (all_u_append u_block_032
    (all_u_append u_block_036
    (all_u_append u_block_040
    (all_u_append u_block_044
    (all_u_append u_block_048
    (all_u_append u_block_052
    (all_u_append u_block_056
    (all_u_append u_block_060
    (all_u_append u_block_064
    (all_u_append u_block_068
    (all_u_append u_block_072
    (all_u_append u_block_074
    (all_u_append u_block_076
    (all_u_append u_block_078
    (all_u_append u_block_080
    (all_u_append u_block_082
    (all_u_append u_block_084
    (all_u_append u_block_086
    (all_u_append u_block_088
    (all_u_append u_block_090
    (all_u_append u_block_092
    (all_u_append u_block_094
    (all_u_append u_block_096
    (all_u_append u_block_098
    (all_u_append u_block_100
    (all_u_append u_block_102
    (all_u_append u_block_104
    (all_u_append u_block_106
    (all_u_append u_block_108
    (all_u_append u_block_110
    (all_u_append u_block_111
    (all_u_append u_block_112
    (all_u_append u_block_113
    (all_u_append u_block_114
    (all_u_append u_block_115
    (all_u_append u_block_116
    (all_u_append u_block_117
    (all_u_append u_block_118
    (all_u_append u_block_119
    (all_u_append u_block_120
    (all_u_append u_block_121
    (all_u_append u_block_122
    (all_u_append u_block_123
    (all_u_append u_block_124
    (all_u_append u_block_125
      u_block_126))))))))))))))))))))))))))))))))))))))))))))))))))))

#print axioms all_u_ok
#check all_u_ok
end CFieldCert
