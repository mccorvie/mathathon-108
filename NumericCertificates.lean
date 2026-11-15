import NumericProof.Sqrt000
import NumericProof.Sqrt001
import NumericProof.Sqrt002
import NumericProof.Sqrt003
import NumericProof.Sqrt004
import NumericProof.Sqrt005
import NumericProof.Sqrt006
import NumericProof.Sqrt007
import NumericProof.Sqrt008
import NumericProof.Sqrt009
import NumericProof.Sqrt010
import NumericProof.Sqrt011
import NumericProof.Sqrt012
import NumericProof.Sqrt013
import NumericProof.Sqrt014
import NumericProof.Sqrt015
import NumericProof.Sqrt016
import NumericProof.Sqrt017
import NumericProof.Sqrt018
import NumericProof.Sqrt019
import NumericProof.Sqrt020
import NumericProof.Sqrt021
import NumericProof.Sqrt022
import NumericProof.Sqrt023
import NumericProof.Sqrt024
import NumericProof.Log000
import NumericProof.Log001
import NumericProof.Log002
import NumericProof.Log003
import NumericProof.Log004
import NumericProof.Log005
import NumericProof.Log006
import NumericProof.Log007
import NumericProof.Log008
import NumericProof.Log009
import NumericProof.Log010
import NumericProof.Log011
import NumericProof.Log012
import NumericProof.Log013
import NumericProof.Log014
import NumericProof.Log015
import NumericProof.Log016
import NumericProof.Log017
import NumericProof.Log018
import NumericProof.Log019
import NumericProof.Log020
import NumericProof.Log021
import NumericProof.Log022
import NumericProof.Log023
import NumericProof.Atan000
import NumericProof.Atan001
import NumericProof.Atan002
import NumericProof.Atan003
import NumericProof.Atan004
import NumericProof.Atan005
import NumericProof.Atan006
import NumericProof.Atan007

/- E608 PROOF-DRAFT full primitive validity from checked numerical blocks.
Codex gpt-6.1-sol lane C; Fauzan re-derivation using Firsching,
Paul-Lez metadata, Apache-2.0. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CPrimitive

theorem sqrt_all : sqrtRows.all checkSqrt = true := by
  simp only [sqrtRows, List.all_append]
  rw [
    sqrt_ok_000,
    sqrt_ok_001,
    sqrt_ok_002,
    sqrt_ok_003,
    sqrt_ok_004,
    sqrt_ok_005,
    sqrt_ok_006,
    sqrt_ok_007,
    sqrt_ok_008,
    sqrt_ok_009,
    sqrt_ok_010,
    sqrt_ok_011,
    sqrt_ok_012,
    sqrt_ok_013,
    sqrt_ok_014,
    sqrt_ok_015,
    sqrt_ok_016,
    sqrt_ok_017,
    sqrt_ok_018,
    sqrt_ok_019,
    sqrt_ok_020,
    sqrt_ok_021,
    sqrt_ok_022,
    sqrt_ok_023,
    sqrt_ok_024]
  all_goals rfl

theorem log_all : logRows.all checkLog = true := by
  simp only [logRows, List.all_append]
  rw [
    log_ok_000,
    log_ok_001,
    log_ok_002,
    log_ok_003,
    log_ok_004,
    log_ok_005,
    log_ok_006,
    log_ok_007,
    log_ok_008,
    log_ok_009,
    log_ok_010,
    log_ok_011,
    log_ok_012,
    log_ok_013,
    log_ok_014,
    log_ok_015,
    log_ok_016,
    log_ok_017,
    log_ok_018,
    log_ok_019,
    log_ok_020,
    log_ok_021,
    log_ok_022,
    log_ok_023]
  all_goals rfl

lemma atan_index_partition : List.range 462 =
    List.range' 0 64 ++ List.range' 64 64 ++ List.range' 128 64 ++
      List.range' 192 64 ++ List.range' 256 64 ++ List.range' 320 64 ++
      List.range' 384 64 ++ List.range' 448 14 := by
  decide +kernel

theorem atan_all : (List.range 462).all
    (fun i => checkAtan sqrtRows atanRows 2 i) = true := by
  rw [atan_index_partition]
  simp only [List.all_append]
  rw [atan_ok_000, atan_ok_001, atan_ok_002, atan_ok_003, atan_ok_004, atan_ok_005, atan_ok_006, atan_ok_007]
  all_goals rfl

lemma atan_length : atanRows.length = 462 := by decide +kernel

theorem all_sqrt_ok {row : SqrtRow} (h : row ∈ sqrtRows) : checkSqrt row = true :=
  List.all_eq_true.mp sqrt_all row h

theorem all_log_ok {row : LogRow} (h : row ∈ logRows) : checkLog row = true :=
  List.all_eq_true.mp log_all row h

theorem all_atan_ok (i : ℕ) (h : i < atanRows.length) :
    checkAtan sqrtRows atanRows 2 i = true := by
  apply List.all_eq_true.mp atan_all i
  apply List.mem_range.mpr
  simpa only [atan_length] using h

#print axioms all_sqrt_ok
#print axioms all_log_ok
#print axioms all_atan_ok
end CPrimitive
