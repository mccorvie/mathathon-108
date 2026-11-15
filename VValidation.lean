import VProof.Block000
import VProof.Block001
import VProof.Block002
import VProof.Block003
import VProof.Block004
import VProof.Block005
import VProof.Block006
import VProof.Block007
import VProof.Block008
import VProof.Block009
import VProof.Block010
import VProof.Block011
import VProof.Block012
import VProof.Block013
import VProof.Block014
import VProof.Block015
import VProof.Block016
import VProof.Block017
import VProof.Block018
import VProof.Block019
import VProof.Block020
import VProof.Block021
import VProof.Block022
import VProof.Block023
import VProof.Block024
import VProof.Block025
import VProof.Block026
import VProof.Block027
import VProof.Block028
import VProof.Block029
import VProof.Block030
import VProof.Block031
import VProof.Critical

/- PROOF-DRAFT: memory-bounded V certificate composition. Codex gpt-6.1-sol, lane C.
Fauzan re-derivation using Firsching; Paul-Lez metadata, Apache-2.0.
The rational data and the public theorem types are unchanged. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CField CFieldData
namespace CFieldCert

private theorem append_v_ok (xs ys : List VPoint)
    (hx : ∀ r ∈ xs, VOK numeric r) (hy : ∀ r ∈ ys, VOK numeric r) :
    ∀ r ∈ xs ++ ys, VOK numeric r := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact hx r h
  · exact hy r h

theorem all_v_ok : ∀ r ∈ vRows, VOK numeric r := by
  change ∀ r ∈
    ((vRows.drop 0).take 4 ++
    ((vRows.drop 4).take 4 ++
    ((vRows.drop 8).take 4 ++
    ((vRows.drop 12).take 4 ++
    ((vRows.drop 16).take 4 ++
    ((vRows.drop 20).take 4 ++
    ((vRows.drop 24).take 4 ++
    ((vRows.drop 28).take 4 ++
    ((vRows.drop 32).take 4 ++
    ((vRows.drop 36).take 4 ++
    ((vRows.drop 40).take 4 ++
    ((vRows.drop 44).take 4 ++
    ((vRows.drop 48).take 4 ++
    ((vRows.drop 52).take 4 ++
    ((vRows.drop 56).take 4 ++
    ((vRows.drop 60).take 4 ++
    ((vRows.drop 64).take 4 ++
    ((vRows.drop 68).take 4 ++
    ((vRows.drop 72).take 4 ++
    ((vRows.drop 76).take 4 ++
    ((vRows.drop 80).take 4 ++
    ((vRows.drop 84).take 4 ++
    ((vRows.drop 88).take 4 ++
    ((vRows.drop 92).take 4 ++
    ((vRows.drop 96).take 4 ++
    ((vRows.drop 100).take 4 ++
    ((vRows.drop 104).take 4 ++
    ((vRows.drop 108).take 4 ++
    ((vRows.drop 112).take 4 ++
    ((vRows.drop 116).take 4 ++
    ((vRows.drop 120).take 4 ++
    (vRows.drop 124).take 4))))))))))))))))))))))))))))))),
    VOK numeric r
  exact
    append_v_ok _ _ v_block_000 (
    append_v_ok _ _ v_block_001 (
    append_v_ok _ _ v_block_002 (
    append_v_ok _ _ v_block_003 (
    append_v_ok _ _ v_block_004 (
    append_v_ok _ _ v_block_005 (
    append_v_ok _ _ v_block_006 (
    append_v_ok _ _ v_block_007 (
    append_v_ok _ _ v_block_008 (
    append_v_ok _ _ v_block_009 (
    append_v_ok _ _ v_block_010 (
    append_v_ok _ _ v_block_011 (
    append_v_ok _ _ v_block_012 (
    append_v_ok _ _ v_block_013 (
    append_v_ok _ _ v_block_014 (
    append_v_ok _ _ v_block_015 (
    append_v_ok _ _ v_block_016 (
    append_v_ok _ _ v_block_017 (
    append_v_ok _ _ v_block_018 (
    append_v_ok _ _ v_block_019 (
    append_v_ok _ _ v_block_020 (
    append_v_ok _ _ v_block_021 (
    append_v_ok _ _ v_block_022 (
    append_v_ok _ _ v_block_023 (
    append_v_ok _ _ v_block_024 (
    append_v_ok _ _ v_block_025 (
    append_v_ok _ _ v_block_026 (
    append_v_ok _ _ v_block_027 (
    append_v_ok _ _ v_block_028 (
    append_v_ok _ _ v_block_029 (
    append_v_ok _ _ v_block_030 (
    v_block_031
    )))))))))))))))))))))))))))))))

#print axioms all_v_ok
#print axioms critical_ok
end CFieldCert
