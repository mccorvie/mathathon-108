import RowSoundness
/-!
U66/E261, Codex. All mathematical declarations are PROOF-DRAFT until parent gate.
Complete rational Row certificates, from C schema data for the continuation [21,40].
Generator adapted from C-split-closing/generate_rows.py; kernel decide checks Valid.
Fauzan context via Firsching formalisation; Paul-Lez metadata; Apache-2.0.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set Mathathon.P108 SplitCells
noncomputable section
namespace U66Data

def row193 : Row :=
  ⟨1100/43,590/23,(-1339/2),181/8, ![58,25,1,51,47],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨26,(-1)⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![25,26,1,2]], true⟩
theorem valid193 : row193.Valid := by decide +kernel
theorem piece193 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1100/43:ℝ) (590/23:ℝ) ∧
    (∫ x in (1100/43:ℝ)..(590/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(6378841/16848040000:ℝ)) := by
  have h := row_integral row193 valid193
  norm_num [row193] at h ⊢
  exact h

def row194 : Row :=
  ⟨590/23,960/37,(-640),859/40, ![59,25,1,51,47],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨26,(-1)⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![25,26,1,2]], false⟩
theorem valid194 : row194.Valid := by decide +kernel
theorem piece194 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (590/23:ℝ) (960/37:ℝ) ∧
    (∫ x in (590/23:ℝ)..(960/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(23597/16040448:ℝ)) := by
  have h := row_integral row194 valid194
  norm_num [row194] at h ⊢
  exact h

def row195 : Row :=
  ⟨960/37,26,(-760),261/10, ![59,25,1,51,48],
   ![⟨0,0⟩,⟨26,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,26,1,1],![25,26,1,2]], false⟩
theorem valid195 : row195.Valid := by decide +kernel
theorem piece195 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (960/37:ℝ) (26:ℝ) ∧
    (∫ x in (960/37:ℝ)..(26:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9863/38937600:ℝ)) := by
  have h := row_integral row195 valid195
  norm_num [row195] at h ⊢
  exact h

def row196 : Row :=
  ⟨26,1120/43,(-786),101/4, ![59,26,1,52,48],
   ![⟨0,0⟩,⟨(-26),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![25,26,1,1],![25,26,1,2]], true⟩
theorem valid196 : row196.Valid := by decide +kernel
theorem piece196 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (26:ℝ) (1120/43:ℝ) ∧
    (∫ x in (26:ℝ)..(1120/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(72127/211993600:ℝ)) := by
  have h := row_integral row196 valid196
  norm_num [row196] at h ⊢
  exact h

def row197 : Row :=
  ⟨1120/43,600/23,(-702),881/40, ![59,26,1,52,48],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-26),1⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![25,26,1,2]], true⟩
theorem valid197 : row197.Valid := by decide +kernel
theorem piece197 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1120/43:ℝ) (600/23:ℝ) ∧
    (∫ x in (1120/43:ℝ)..(600/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(27473/94080000:ℝ)) := by
  have h := row_integral row197 valid197
  norm_num [row197] at h ⊢
  exact h

def row198 : Row :=
  ⟨600/23,980/37,(-672),167/8, ![60,26,1,52,48],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-26),1⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![25,26,1,2]], false⟩
theorem valid198 : row198.Valid := by decide +kernel
theorem piece198 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (600/23:ℝ) (980/37:ℝ) ∧
    (∫ x in (600/23:ℝ)..(980/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(37213/13720000:ℝ)) := by
  have h := row_integral row198 valid198
  norm_num [row198] at h ⊢
  exact h

def row199 : Row :=
  ⟨980/37,53/2,(-721),909/40, ![60,26,1,52,49],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-26),1⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![25,26,1,2]], false⟩
theorem valid199 : row199.Valid := by decide +kernel
theorem piece199 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (980/37:ℝ) (53/2:ℝ) ∧
    (∫ x in (980/37:ℝ)..(53/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2082/24087175:ℝ)) := by
  have h := row_integral row199 valid199
  norm_num [row199] at h ⊢
  exact h

def row200 : Row :=
  ⟨53/2,1140/43,(-1495/2),949/40, ![60,26,1,53,49],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨27,(-1)⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![26,27,1,2]], true⟩
theorem valid200 : row200.Valid := by decide +kernel
theorem piece200 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (53/2:ℝ) (1140/43:ℝ) ∧
    (∫ x in (53/2:ℝ)..(1140/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1081847/14602305600:ℝ)) := by
  have h := row_integral row200 valid200
  norm_num [row200] at h ⊢
  exact h

def row201 : Row :=
  ⟨1140/43,610/23,(-1495/2),949/40, ![60,26,1,53,49],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨27,(-1)⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![26,27,1,2]], true⟩
theorem valid201 : row201.Valid := by decide +kernel
theorem piece201 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1140/43:ℝ) (610/23:ℝ) ∧
    (∫ x in (1140/43:ℝ)..(610/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1241929/19343246400:ℝ)) := by
  have h := row_integral row201 valid201
  norm_num [row201] at h ⊢
  exact h

def row202 : Row :=
  ⟨610/23,80/3,(-717),903/40, ![61,26,1,53,49],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨27,(-1)⟩,⟨1/2,0⟩],
   ![![26,26,1,1],![26,26,1,2],![26,27,1,2]], false⟩
theorem valid202 : row202.Valid := by decide +kernel
theorem piece202 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (610/23:ℝ) (80/3:ℝ) ∧
    (∫ x in (610/23:ℝ)..(80/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(42807/47628800:ℝ)) := by
  have h := row_integral row202 valid202
  norm_num [row202] at h ⊢
  exact h

def row203 : Row :=
  ⟨80/3,620/23,(-749),279/8, ![61,26,2,53,49],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨27,(-1)⟩,⟨1/2,0⟩],
   ![![26,26,2,2],![26,26,1,2],![26,27,1,2]], true⟩
theorem valid203 : row203.Valid := by decide +kernel
theorem piece203 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (80/3:ℝ) (620/23:ℝ) ∧
    (∫ x in (80/3:ℝ)..(620/23:ℝ), innerR 7 6 (3/40) x / x^3) = (6883/2460160:ℝ) := by
  have h := row_integral row203 valid203
  norm_num [row203] at h ⊢
  exact h

def row204 : Row :=
  ⟨620/23,1160/43,(-718),1349/40, ![62,26,2,53,49],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨27,(-1)⟩,⟨1/2,0⟩],
   ![![26,26,2,2],![26,26,1,2],![26,27,1,2]], false⟩
theorem valid204 : row204.Valid := by decide +kernel
theorem piece204 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (620/23:ℝ) (1160/43:ℝ) ∧
    (∫ x in (620/23:ℝ)..(1160/43:ℝ), innerR 7 6 (3/40) x / x^3) = (127649/646560800:ℝ) := by
  have h := row_integral row204 valid204
  norm_num [row204] at h ⊢
  exact h

def row205 : Row :=
  ⟨1160/43,27,(-631),61/2, ![62,26,2,53,49],
   ![⟨0,0⟩,⟨27,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![26,26,2,2],![26,27,2,2],![26,27,1,2]], false⟩
theorem valid205 : row205.Valid := by decide +kernel
theorem piece205 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1160/43:ℝ) (27:ℝ) ∧
    (∫ x in (1160/43:ℝ)..(27:ℝ), innerR 7 6 (3/40) x / x^3) = (445969/1961884800:ℝ) := by
  have h := row_integral row205 valid205
  norm_num [row205] at h ⊢
  exact h

def row206 : Row :=
  ⟨27,1000/37,(-658),593/20, ![62,27,2,54,49],
   ![⟨0,0⟩,⟨(-27),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![26,27,2,2],![26,27,1,2]], true⟩
theorem valid206 : row206.Valid := by decide +kernel
theorem piece206 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (27:ℝ) (1000/37:ℝ) ∧
    (∫ x in (27:ℝ)..(1000/37:ℝ), innerR 7 6 (3/40) x / x^3) = (142879/729000000:ℝ) := by
  have h := row_integral row206 valid206
  norm_num [row206] at h ⊢
  exact h

def row207 : Row :=
  ⟨1000/37,630/23,(-783),1371/40, ![62,27,2,54,50],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-27),1⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![26,27,1,2]], true⟩
theorem valid207 : row207.Valid := by decide +kernel
theorem piece207 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1000/37:ℝ) (630/23:ℝ) ∧
    (∫ x in (1000/37:ℝ)..(630/23:ℝ), innerR 7 6 (3/40) x / x^3) = (795181/294000000:ℝ) := by
  have h := row_integral row207 valid207
  norm_num [row207] at h ⊢
  exact h

def row208 : Row :=
  ⟨630/23,1180/43,(-1503/2),265/8, ![63,27,2,54,50],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-27),1⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![26,27,1,2]], false⟩
theorem valid208 : row208.Valid := by decide +kernel
theorem piece208 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (630/23:ℝ) (1180/43:ℝ) ∧
    (∫ x in (630/23:ℝ)..(1180/43:ℝ), innerR 7 6 (3/40) x / x^3) = (188809/491238720:ℝ) := by
  have h := row_integral row208 valid208
  norm_num [row208] at h ⊢
  exact h

def row209 : Row :=
  ⟨1180/43,55/2,(-1503/2),265/8, ![63,27,2,54,50],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-27),1⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![26,27,1,2]], false⟩
theorem valid209 : row209.Valid := by decide +kernel
theorem piece209 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1180/43:ℝ) (55/2:ℝ) ∧
    (∫ x in (1180/43:ℝ)..(55/2:ℝ), innerR 7 6 (3/40) x / x^3) = (59903/134784320:ℝ) := by
  have h := row_integral row209 valid209
  norm_num [row209] at h ⊢
  exact h

def row210 : Row :=
  ⟨55/2,1020/37,(-779),273/8, ![63,27,2,55,50],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨28,(-1)⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![27,28,1,2]], true⟩
theorem valid210 : row210.Valid := by decide +kernel
theorem piece210 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (55/2:ℝ) (1020/37:ℝ) ∧
    (∫ x in (55/2:ℝ)..(1020/37:ℝ), innerR 7 6 (3/40) x / x^3) = (818/1573605:ℝ) := by
  have h := row_integral row210 valid210
  norm_num [row210] at h ⊢
  exact h

def row211 : Row :=
  ⟨1020/37,640/23,(-830),1439/40, ![63,27,2,55,51],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨28,(-1)⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![27,28,1,2]], true⟩
theorem valid211 : row211.Valid := by decide +kernel
theorem piece211 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1020/37:ℝ) (640/23:ℝ) ∧
    (∫ x in (1020/37:ℝ)..(640/23:ℝ), innerR 7 6 (3/40) x / x^3) = (2156759/1065369600:ℝ) := by
  have h := row_integral row211 valid211
  norm_num [row211] at h ⊢
  exact h

def row212 : Row :=
  ⟨640/23,1200/43,(-798),1393/40, ![64,27,2,55,51],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨28,(-1)⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,27,1,2],![27,28,1,2]], false⟩
theorem valid212 : row212.Valid := by decide +kernel
theorem piece212 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (640/23:ℝ) (1200/43:ℝ) ∧
    (∫ x in (640/23:ℝ)..(1200/43:ℝ), innerR 7 6 (3/40) x / x^3) = (6601/10240000:ℝ) := by
  have h := row_integral row212 valid212
  norm_num [row212] at h ⊢
  exact h

theorem block002 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1100/43:ℝ) (1200/43:ℝ) ∧
    (∫ x in (1100/43:ℝ)..(1200/43:ℝ), innerR 7 6 (3/40) x / x^3) = (924038669094175/258847283208818304:ℝ) := by
  have h := piece193
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (590/23:ℝ) (960/37:ℝ)
    (-(6378841/16848040000:ℝ)) (-(23597/16040448:ℝ)) h piece194
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (960/37:ℝ) (26:ℝ)
    (-(38030503/20560320000:ℝ)) (-(9863/38937600:ℝ)) h piece195
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (26:ℝ) (1120/43:ℝ)
    (-(4871536313/2316462720000:ℝ)) (-(72127/211993600:ℝ)) h piece196
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1120/43:ℝ) (600/23:ℝ)
    (-(2666575753/1091410320000:ℝ)) (-(27473/94080000:ℝ)) h piece197
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (600/23:ℝ) (980/37:ℝ)
    (-(227450407/83155072000:ℝ)) (-(37213/13720000:ℝ)) h piece198
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (980/37:ℝ) (53/2:ℝ)
    (-(110983379971/20372992640000:ℝ)) (-(2082/24087175:ℝ)) h piece199
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (53/2:ℝ) (1140/43:ℝ)
    (-(45242693313277/8175390903680000:ℝ)) (-(1081847/14602305600:ℝ)) h piece200
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1140/43:ℝ) (610/23:ℝ)
    (-(2810592620294441/501166887661440000:ℝ)) (-(1241929/19343246400:ℝ)) h piece201
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (610/23:ℝ) (80/3:ℝ)
    (-(3255754669547889/573974142501760000:ℝ)) (-(42807/47628800:ℝ)) h piece202
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (80/3:ℝ) (620/23:ℝ)
    (-(61829858254599/9409412172160000:ℝ)) (6883/2460160:ℝ) h piece203
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (620/23:ℝ) (1160/43:ℝ)
    (-(34119671915100389/9042445097445760000:ℝ)) (127649/646560800:ℝ) h piece204
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1160/43:ℝ) (27:ℝ)
    (-(877202145569172979/245312784740383360000:ℝ)) (445969/1961884800:ℝ) h piece205
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (27:ℝ) (1000/37:ℝ)
    (-(20649263738540732879/6166655864680671360000:ℝ)) (142879/729000000:ℝ) h piece206
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1000/37:ℝ) (630/23:ℝ)
    (-(666688665444822879/211476538569296000000:ℝ)) (795181/294000000:ℝ) h piece207
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (630/23:ℝ) (1180/43:ℝ)
    (-(1623576806105339/3625312089759360000:ℝ)) (188809/491238720:ℝ) h piece208
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1180/43:ℝ) (55/2:ℝ)
    (-(285190278696277021/4491761679211847040000:ℝ)) (59903/134784320:ℝ) h piece209
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (55/2:ℝ) (1020/37:ℝ)
    (29001867461243881/76131553884946560000:ℝ) (818/1573605:ℝ) h piece210
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (1020/37:ℝ) (640/23:ℝ)
    (6606250059641075203/7334006357583185280000:ℝ) (2156759/1065369600:ℝ) h piece211
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1100/43:ℝ) (640/23:ℝ) (1200/43:ℝ)
    (60574258242679237307/20707782656705464320000:ℝ) (6601/10240000:ℝ) h piece212
  norm_num at h
  exact h

end U66Data
