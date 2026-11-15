import Witness.Field
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace U11
noncomputable section
theorem C6_lower : (21224286653:ℝ)/8000000000 ≤ C6 := by
  have ha := logCell2.2
  have hl := logCell3.2
  unfold C6 lam alpha
  norm_num at ha hl ⊢
  linarith

theorem field_sum_upper : (∑ j : Fin 15, mass j*W (width j)) ≤ (33004999675164815400017:ℝ)/17179869184000000000000 := by
  have h := field_sum_le
  norm_num [Fin.sum_univ_succ,mass,fieldCeil] at h ⊢
  exact h

theorem lb6Square15_lower : (-2984595961434780279493517:ℝ)/2147483648000000000000000 ≤ lb6Square15 := by
  have he0 := logCell0.1
  have he1 := logCell1.1
  have hc := C6_lower
  have hf := field_sum_upper
  unfold lb6Square15 lam
  norm_num at he0 he1 ⊢
  linarith

theorem lb6Square15_gt : (-139:ℝ)/100 < lb6Square15 := by
  have h := lb6Square15_lower
  linarith

theorem margin_gt (A U : ℝ) (hA : (229:ℝ)/100 ≤ A) (hU : lb6Square15 ≤ U) : (9:ℝ)/10 < A+U := by
  have h := lb6Square15_gt
  linarith

#print U11.lb6Square15
#check U11.lb6Square15_gt
#print axioms U11.lb6Square15_gt
#check U11.margin_gt
#print axioms U11.margin_gt
end
end U11
