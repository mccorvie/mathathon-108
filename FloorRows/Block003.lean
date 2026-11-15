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

def row213 : Row :=
  ⟨1200/43,28,(-708),158/5, ![64,27,2,55,51],
   ![⟨0,0⟩,⟨28,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![27,27,2,2],![27,28,2,2],![27,28,1,2]], false⟩
theorem valid213 : row213.Valid := by decide +kernel
theorem piece213 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1200/43:ℝ) (28:ℝ) ∧
    (∫ x in (1200/43:ℝ)..(28:ℝ), innerR 7 6 (3/40) x / x^3) = (2927/3920000:ℝ) := by
  have h := row_integral row213 valid213
  norm_num [row213] at h ⊢
  exact h

def row214 : Row :=
  ⟨28,1040/37,(-736),123/4, ![64,28,2,56,51],
   ![⟨0,0⟩,⟨(-28),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![27,28,2,2],![27,28,1,2]], true⟩
theorem valid214 : row214.Valid := by decide +kernel
theorem piece214 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (28:ℝ) (1040/37:ℝ) ∧
    (∫ x in (28:ℝ)..(1040/37:ℝ), innerR 7 6 (3/40) x / x^3) = (8217/13249600:ℝ) := by
  have h := row_integral row214 valid214
  norm_num [row214] at h ⊢
  exact h

def row215 : Row :=
  ⟨1040/37,650/23,(-866),283/8, ![64,28,2,56,52],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-28),1⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![27,28,1,2]], true⟩
theorem valid215 : row215.Valid := by decide +kernel
theorem piece215 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1040/37:ℝ) (650/23:ℝ) ∧
    (∫ x in (1040/37:ℝ)..(650/23:ℝ), innerR 7 6 (3/40) x / x^3) = (24173/27040000:ℝ) := by
  have h := row_integral row215 valid215
  norm_num [row215] at h ⊢
  exact h

def row216 : Row :=
  ⟨650/23,85/3,(-1667/2),1369/40, ![65,28,2,56,52],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-28),1⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![27,28,1,2]], false⟩
theorem valid216 : row216.Valid := by decide +kernel
theorem piece216 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (650/23:ℝ) (85/3:ℝ) ∧
    (∫ x in (650/23:ℝ)..(85/3:ℝ), innerR 7 6 (3/40) x / x^3) = (105409/244205000:ℝ) := by
  have h := row_integral row216 valid216
  norm_num [row216] at h ⊢
  exact h

def row217 : Row :=
  ⟨85/3,1220/43,(-1667/2),1369/40, ![65,28,2,56,52],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-28),1⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![27,28,1,2]], false⟩
theorem valid217 : row217.Valid := by decide +kernel
theorem piece217 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (85/3:ℝ) (1220/43:ℝ) ∧
    (∫ x in (85/3:ℝ)..(1220/43:ℝ), innerR 7 6 (3/40) x / x^3) = (80097/344118080:ℝ) := by
  have h := row_integral row217 valid217
  norm_num [row217] at h ⊢
  exact h

def row218 : Row :=
  ⟨1220/43,57/2,(-1667/2),1369/40, ![65,28,2,56,52],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-28),1⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![27,28,1,2]], false⟩
theorem valid218 : row218.Valid := by decide +kernel
theorem piece218 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1220/43:ℝ) (57/2:ℝ) ∧
    (∫ x in (1220/43:ℝ)..(57/2:ℝ), innerR 7 6 (3/40) x / x^3) = (15034019/19343246400:ℝ) := by
  have h := row_integral row218 valid218
  norm_num [row218] at h ⊢
  exact h

def row219 : Row :=
  ⟨57/2,1060/37,(-862),1409/40, ![65,28,2,57,52],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨29,(-1)⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![28,29,1,2]], true⟩
theorem valid219 : row219.Valid := by decide +kernel
theorem piece219 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (57/2:ℝ) (1060/37:ℝ) ∧
    (∫ x in (57/2:ℝ)..(1060/37:ℝ), innerR 7 6 (3/40) x / x^3) = (6723101/7301152800:ℝ) := by
  have h := row_integral row219 valid219
  norm_num [row219] at h ⊢
  exact h

def row220 : Row :=
  ⟨1060/37,660/23,(-915),1483/40, ![65,28,2,57,53],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨29,(-1)⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![28,29,1,2]], true⟩
theorem valid220 : row220.Valid := by decide +kernel
theorem piece220 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1060/37:ℝ) (660/23:ℝ) ∧
    (∫ x in (1060/37:ℝ)..(660/23:ℝ), innerR 7 6 (3/40) x / x^3) = (120389/407866800:ℝ) := by
  have h := row_integral row220 valid220
  norm_num [row220] at h ⊢
  exact h

def row221 : Row :=
  ⟨660/23,1240/43,(-882),1437/40, ![66,28,2,57,53],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨29,(-1)⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,28,1,2],![28,29,1,2]], false⟩
theorem valid221 : row221.Valid := by decide +kernel
theorem piece221 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (660/23:ℝ) (1240/43:ℝ) ∧
    (∫ x in (660/23:ℝ)..(1240/43:ℝ), innerR 7 6 (3/40) x / x^3) = (83769/93024800:ℝ) := by
  have h := row_integral row221 valid221
  norm_num [row221] at h ⊢
  exact h

def row222 : Row :=
  ⟨1240/43,29,(-789),327/10, ![66,28,2,57,53],
   ![⟨0,0⟩,⟨29,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![28,28,2,2],![28,29,2,2],![28,29,1,2]], false⟩
theorem valid222 : row222.Valid := by decide +kernel
theorem piece222 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1240/43:ℝ) (29:ℝ) ∧
    (∫ x in (1240/43:ℝ)..(29:ℝ), innerR 7 6 (3/40) x / x^3) = (2726787/2586243200:ℝ) := by
  have h := row_integral row222 valid222
  norm_num [row222] at h ⊢
  exact h

def row223 : Row :=
  ⟨29,670/23,(-818),637/20, ![66,29,2,58,53],
   ![⟨0,0⟩,⟨(-29),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![28,29,2,2],![28,29,1,2]], true⟩
theorem valid223 : row223.Valid := by decide +kernel
theorem piece223 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (29:ℝ) (670/23:ℝ) ∧
    (∫ x in (29:ℝ)..(670/23:ℝ), innerR 7 6 (3/40) x / x^3) = (17283/30201992:ℝ) := by
  have h := row_integral row223 valid223
  norm_num [row223] at h ⊢
  exact h

def row224 : Row :=
  ⟨670/23,1080/37,(-1569/2),307/10, ![67,29,2,58,53],
   ![⟨0,0⟩,⟨(-29),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![28,29,2,2],![28,29,1,2]], false⟩
theorem valid224 : row224.Valid := by decide +kernel
theorem piece224 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (670/23:ℝ) (1080/37:ℝ) ∧
    (∫ x in (670/23:ℝ)..(1080/37:ℝ), innerR 7 6 (3/40) x / x^3) = (366287/1396258560:ℝ) := by
  have h := row_integral row224 valid224
  norm_num [row224] at h ⊢
  exact h

def row225 : Row :=
  ⟨1080/37,1260/43,(-1839/2),1413/40, ![67,29,2,58,54],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-29),1⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,29,1,2],![28,29,1,2]], false⟩
theorem valid225 : row225.Valid := by decide +kernel
theorem piece225 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1080/37:ℝ) (1260/43:ℝ) ∧
    (∫ x in (1080/37:ℝ)..(1260/43:ℝ), innerR 7 6 (3/40) x / x^3) = (7831/15240960:ℝ) := by
  have h := row_integral row225 valid225
  norm_num [row225] at h ⊢
  exact h

def row226 : Row :=
  ⟨1260/43,59/2,(-1839/2),1413/40, ![67,29,2,58,54],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-29),1⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,29,1,2],![28,29,1,2]], false⟩
theorem valid226 : row226.Valid := by decide +kernel
theorem piece226 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1260/43:ℝ) (59/2:ℝ) ∧
    (∫ x in (1260/43:ℝ)..(59/2:ℝ), innerR 7 6 (3/40) x / x^3) = (6825041/7368580800:ℝ) := by
  have h := row_integral row226 valid226
  norm_num [row226] at h ⊢
  exact h

def row227 : Row :=
  ⟨59/2,680/23,(-949),1453/40, ![67,29,2,59,54],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨30,(-1)⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,29,1,2],![29,30,1,2]], true⟩
theorem valid227 : row227.Valid := by decide +kernel
theorem piece227 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (59/2:ℝ) (680/23:ℝ) ∧
    (∫ x in (59/2:ℝ)..(680/23:ℝ), innerR 7 6 (3/40) x / x^3) = (201771/643845760:ℝ) := by
  have h := row_integral row227 valid227
  norm_num [row227] at h ⊢
  exact h

def row228 : Row :=
  ⟨680/23,1100/37,(-915),1407/40, ![68,29,2,59,54],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨30,(-1)⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,29,1,2],![29,30,1,2]], false⟩
theorem valid228 : row228.Valid := by decide +kernel
theorem piece228 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (680/23:ℝ) (1100/37:ℝ) ∧
    (∫ x in (680/23:ℝ)..(1100/37:ℝ), innerR 7 6 (3/40) x / x^3) = (451563/559504000:ℝ) := by
  have h := row_integral row228 valid228
  norm_num [row228] at h ⊢
  exact h

def row229 : Row :=
  ⟨1100/37,1280/43,(-970),1481/40, ![68,29,2,59,55],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨30,(-1)⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,29,1,2],![29,30,1,2]], false⟩
theorem valid229 : row229.Valid := by decide +kernel
theorem piece229 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1100/37:ℝ) (1280/43:ℝ) ∧
    (∫ x in (1100/37:ℝ)..(1280/43:ℝ), innerR 7 6 (3/40) x / x^3) = (186633/991232000:ℝ) := by
  have h := row_integral row229 valid229
  norm_num [row229] at h ⊢
  exact h

def row230 : Row :=
  ⟨1280/43,30,(-874),169/5, ![68,29,2,59,55],
   ![⟨0,0⟩,⟨30,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![29,29,2,2],![29,30,2,2],![29,30,1,2]], false⟩
theorem valid230 : row230.Valid := by decide +kernel
theorem piece230 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1280/43:ℝ) (30:ℝ) ∧
    (∫ x in (1280/43:ℝ)..(30:ℝ), innerR 7 6 (3/40) x / x^3) = (17483/14745600:ℝ) := by
  have h := row_integral row230 valid230
  norm_num [row230] at h ⊢
  exact h

def row231 : Row :=
  ⟨30,1300/43,(-865),633/20, ![69,30,2,60,55],
   ![⟨0,0⟩,⟨(-30),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![29,30,2,2],![29,30,1,2]], true⟩
theorem valid231 : row231.Valid := by decide +kernel
theorem piece231 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (30:ℝ) (1300/43:ℝ) ∧
    (∫ x in (30:ℝ)..(1300/43:ℝ), innerR 7 6 (3/40) x / x^3) = (4567/6084000:ℝ) := by
  have h := row_integral row231 valid231
  norm_num [row231] at h ⊢
  exact h

def row232 : Row :=
  ⟨1300/43,1120/37,(-865),633/20, ![69,30,2,60,55],
   ![⟨0,0⟩,⟨(-30),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![29,30,2,2],![29,30,1,2]], true⟩
theorem valid232 : row232.Valid := by decide +kernel
theorem piece232 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1300/43:ℝ) (1120/37:ℝ) ∧
    (∫ x in (1300/43:ℝ)..(1120/37:ℝ), innerR 7 6 (3/40) x / x^3) = (266997/2119936000:ℝ) := by
  have h := row_integral row232 valid232
  norm_num [row232] at h ⊢
  exact h

theorem block003 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1200/43:ℝ) (1120/37:ℝ) ∧
    (∫ x in (1200/43:ℝ)..(1120/37:ℝ), innerR 7 6 (3/40) x / x^3) =
      (368864833759259165087/29464613251102149120000:ℝ) := by
  have h := piece213
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (28:ℝ) (1040/37:ℝ)
    (2927/3920000:ℝ) (8217/13249600:ℝ) h piece214
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1040/37:ℝ) (650/23:ℝ)
    (129359/94640000:ℝ) (24173/27040000:ℝ) h piece215
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (650/23:ℝ) (85/3:ℝ)
    (427929/189280000:ℝ) (105409/244205000:ℝ) h piece216
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (85/3:ℝ) (1220/43:ℝ)
    (11329469/4207840000:ℝ) (80097/344118080:ℝ) h piece217
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1220/43:ℝ) (57/2:ℝ)
    (158482241/54177760000:ℝ) (15034019/19343246400:ℝ) h piece218
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (57/2:ℝ) (1060/37:ℝ)
    (175146029/47305440000:ℝ) (6723101/7301152800:ℝ) h piece219
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1060/37:ℝ) (660/23:ℝ)
    (10777993573/2331245280000:ℝ) (120389/407866800:ℝ) h piece220
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (660/23:ℝ) (1240/43:ℝ)
    (8725775187/1774092320000:ℝ) (83769/93024800:ℝ) h piece221
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1240/43:ℝ) (29:ℝ)
    (901885265937/154991156320000:ℝ) (2726787/2586243200:ℝ) h piece222
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (29:ℝ) (670/23:ℝ)
    (28900533155757/4204760079520000:ℝ) (17283/30201992:ℝ) h piece223
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (670/23:ℝ) (1080/37:ℝ)
    (4846060414634937/650867861964320000:ℝ) (366287/1396258560:ℝ) h piece224
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1080/37:ℝ) (1260/43:ℝ)
    (9097640018841799/1180305152666640000:ℝ) (7831/15240960:ℝ) h piece225
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1260/43:ℝ) (59/2:ℝ)
    (15095260270929229/1836030237481440000:ℝ) (6825041/7368580800:ℝ) h piece226
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (59/2:ℝ) (680/23:ℝ)
    (8352339559133900207/913031608096127520000:ℝ) (201771/643845760:ℝ) h piece227
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (680/23:ℝ) (1100/37:ℝ)
    (42313857184657653247/4472307368470861920000:ℝ) (451563/559504000:ℝ) h piece228
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1100/37:ℝ) (1280/43:ℝ)
    (29715112135791757771/2893845944304675360000:ℝ) (186633/991232000:ℝ) h piece229
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1280/43:ℝ) (30:ℝ)
    (704232184041804801731/67347687431090626560000:ℝ) (17483/14745600:ℝ) h piece230
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (30:ℝ) (1300/43:ℝ)
    (49005151165282331291/4209230464443164160000:ℝ) (4567/6084000:ℝ) h piece231
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1200/43:ℝ) (1300/43:ℝ) (1120/37:ℝ)
    (678142938505747081823/54719996037761134080000:ℝ) (266997/2119936000:ℝ) h piece232
  norm_num at h
  exact h

end U66Data
