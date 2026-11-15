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

def row233 : Row :=
  ⟨1120/37,700/23,(-1005),1451/40, ![69,30,2,60,56],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-30),1⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,30,1,2],![29,30,1,2]], true⟩
theorem valid233 : row233.Valid := by decide +kernel
theorem piece233 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1120/37:ℝ) (700/23:ℝ) ∧
    (∫ x in (1120/37:ℝ)..(700/23:ℝ), innerR 7 6 (3/40) x / x^3) = (7087/12544000:ℝ) := by
  have h := row_integral row233 valid233
  norm_num [row233] at h ⊢
  exact h

def row234 : Row :=
  ⟨700/23,61/2,(-970),281/8, ![70,30,2,60,56],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-30),1⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,30,1,2],![29,30,1,2]], false⟩
theorem valid234 : row234.Valid := by decide +kernel
theorem piece234 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (700/23:ℝ) (61/2:ℝ) ∧
    (∫ x in (700/23:ℝ)..(61/2:ℝ), innerR 7 6 (3/40) x / x^3) = (168459/729316000:ℝ) := by
  have h := row_integral row234 valid234
  norm_num [row234] at h ⊢
  exact h

def row235 : Row :=
  ⟨61/2,1320/43,(-2001/2),289/8, ![70,30,2,61,56],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨31,(-1)⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,30,1,2],![30,31,1,2]], true⟩
theorem valid235 : row235.Valid := by decide +kernel
theorem piece235 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (61/2:ℝ) (1320/43:ℝ) ∧
    (∫ x in (61/2:ℝ)..(1320/43:ℝ), innerR 7 6 (3/40) x / x^3) = (2085101/2881542400:ℝ) := by
  have h := row_integral row235 valid235
  norm_num [row235] at h ⊢
  exact h

def row236 : Row :=
  ⟨1320/43,1140/37,(-1803/2),329/10, ![70,30,2,61,56],
   ![⟨0,0⟩,⟨31,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,31,2,2],![30,31,1,2]], true⟩
theorem valid236 : row236.Valid := by decide +kernel
theorem piece236 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1320/43:ℝ) (1140/37:ℝ) ∧
    (∫ x in (1320/43:ℝ)..(1140/37:ℝ), innerR 7 6 (3/40) x / x^3) = (23989/55911680:ℝ) := by
  have h := row_integral row236 valid236
  norm_num [row236] at h ⊢
  exact h

def row237 : Row :=
  ⟨1140/37,710/23,(-1917/2),139/4, ![70,30,2,61,57],
   ![⟨0,0⟩,⟨31,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,31,2,2],![30,31,1,2]], true⟩
theorem valid237 : row237.Valid := by decide +kernel
theorem piece237 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1140/37:ℝ) (710/23:ℝ) ∧
    (∫ x in (1140/37:ℝ)..(710/23:ℝ), innerR 7 6 (3/40) x / x^3) = (5579/24605760:ℝ) := by
  have h := row_integral row237 valid237
  norm_num [row237] at h ⊢
  exact h

def row238 : Row :=
  ⟨710/23,31,(-923),168/5, ![71,30,2,61,57],
   ![⟨0,0⟩,⟨31,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![30,30,2,2],![30,31,2,2],![30,31,1,2]], false⟩
theorem valid238 : row238.Valid := by decide +kernel
theorem piece238 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (710/23:ℝ) (31:ℝ) ∧
    (∫ x in (710/23:ℝ)..(31:ℝ), innerR 7 6 (3/40) x / x^3) = (6999/13646200:ℝ) := by
  have h := row_integral row238 valid238
  norm_num [row238] at h ⊢
  exact h

def row239 : Row :=
  ⟨31,1340/43,(-954),131/4, ![71,31,2,62,57],
   ![⟨0,0⟩,⟨(-31),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![30,31,2,2],![30,31,1,2]], true⟩
theorem valid239 : row239.Valid := by decide +kernel
theorem piece239 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (31:ℝ) (1340/43:ℝ) ∧
    (∫ x in (31:ℝ)..(1340/43:ℝ), innerR 7 6 (3/40) x / x^3) = (298949/862785800:ℝ) := by
  have h := row_integral row239 valid239
  norm_num [row239] at h ⊢
  exact h

def row240 : Row :=
  ⟨1340/43,720/23,(-954),131/4, ![71,31,2,62,57],
   ![⟨0,0⟩,⟨(-31),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![30,31,2,2],![30,31,1,2]], true⟩
theorem valid240 : row240.Valid := by decide +kernel
theorem piece240 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1340/43:ℝ) (720/23:ℝ) ∧
    (∫ x in (1340/43:ℝ)..(720/23:ℝ), innerR 7 6 (3/40) x / x^3) = (27587/86188800:ℝ) := by
  have h := row_integral row240 valid240
  norm_num [row240] at h ⊢
  exact h

def row241 : Row :=
  ⟨720/23,1160/37,(-918),158/5, ![72,31,2,62,57],
   ![⟨0,0⟩,⟨(-31),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![30,31,2,2],![30,31,1,2]], false⟩
theorem valid241 : row241.Valid := by decide +kernel
theorem piece241 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (720/23:ℝ) (1160/37:ℝ) ∧
    (∫ x in (720/23:ℝ)..(1160/37:ℝ), innerR 7 6 (3/40) x / x^3) = (5329/48441600:ℝ) := by
  have h := row_integral row241 valid241
  norm_num [row241] at h ⊢
  exact h

def row242 : Row :=
  ⟨1160/37,63/2,(-1063),1449/40, ![72,31,2,62,58],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-31),1⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,31,1,2],![30,31,1,2]], false⟩
theorem valid242 : row242.Valid := by decide +kernel
theorem piece242 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1160/37:ℝ) (63/2:ℝ) ∧
    (∫ x in (1160/37:ℝ)..(63/2:ℝ), innerR 7 6 (3/40) x / x^3) = (3856963/10681372800:ℝ) := by
  have h := row_integral row242 valid242
  norm_num [row242] at h ⊢
  exact h

def row243 : Row :=
  ⟨63/2,1360/43,(-2189/2),1489/40, ![72,31,2,63,58],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨32,(-1)⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,31,1,2],![31,32,1,2]], true⟩
theorem valid243 : row243.Valid := by decide +kernel
theorem piece243 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (63/2:ℝ) (1360/43:ℝ) ∧
    (∫ x in (63/2:ℝ)..(1360/43:ℝ), innerR 7 6 (3/40) x / x^3) = (9610381/29364249600:ℝ) := by
  have h := row_integral row243 valid243
  norm_num [row243] at h ⊢
  exact h

def row244 : Row :=
  ⟨1360/43,95/3,(-1985/2),34, ![72,31,2,63,58],
   ![⟨0,0⟩,⟨32,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,32,2,2],![31,32,1,2]], true⟩
theorem valid244 : row244.Valid := by decide +kernel
theorem piece244 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1360/43:ℝ) (95/3:ℝ) ∧
    (∫ x in (1360/43:ℝ)..(95/3:ℝ), innerR 7 6 (3/40) x / x^3) = (54547/534164480:ℝ) := by
  have h := row_integral row244 valid244
  norm_num [row244] at h ⊢
  exact h

def row245 : Row :=
  ⟨95/3,730/23,(-1985/2),34, ![72,31,2,63,58],
   ![⟨0,0⟩,⟨32,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,32,2,2],![31,32,1,2]], true⟩
theorem valid245 : row245.Valid := by decide +kernel
theorem piece245 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (95/3:ℝ) (730/23:ℝ) ∧
    (∫ x in (95/3:ℝ)..(730/23:ℝ), innerR 7 6 (3/40) x / x^3) = (29889/153901520:ℝ) := by
  have h := row_integral row245 valid245
  norm_num [row245] at h ⊢
  exact h

def row246 : Row :=
  ⟨730/23,1180/37,(-956),657/20, ![73,31,2,63,58],
   ![⟨0,0⟩,⟨32,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,32,2,2],![31,32,1,2]], false⟩
theorem valid246 : row246.Valid := by decide +kernel
theorem piece246 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (730/23:ℝ) (1180/37:ℝ) ∧
    (∫ x in (730/23:ℝ)..(1180/37:ℝ), innerR 7 6 (3/40) x / x^3) = (3137277/7420099600:ℝ) := by
  have h := row_integral row246 valid246
  norm_num [row246] at h ⊢
  exact h

def row247 : Row :=
  ⟨1180/37,32,(-1015),347/10, ![73,31,2,63,59],
   ![⟨0,0⟩,⟨32,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![31,31,2,2],![31,32,2,2],![31,32,1,2]], false⟩
theorem valid247 : row247.Valid := by decide +kernel
theorem piece247 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1180/37:ℝ) (32:ℝ) ∧
    (∫ x in (1180/37:ℝ)..(32:ℝ), innerR 7 6 (3/40) x / x^3) = (55271/178227200:ℝ) := by
  have h := row_integral row247 valid247
  norm_num [row247] at h ⊢
  exact h

def row248 : Row :=
  ⟨32,1380/43,(-1047),677/20, ![73,32,2,64,59],
   ![⟨0,0⟩,⟨(-32),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![31,32,2,2],![31,32,1,2]], true⟩
theorem valid248 : row248.Valid := by decide +kernel
theorem piece248 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (32:ℝ) (1380/43:ℝ) ∧
    (∫ x in (32:ℝ)..(1380/43:ℝ), innerR 7 6 (3/40) x / x^3) = (347/3250176:ℝ) := by
  have h := row_integral row248 valid248
  norm_num [row248] at h ⊢
  exact h

def row249 : Row :=
  ⟨1380/43,740/23,(-1047),677/20, ![73,32,2,64,59],
   ![⟨0,0⟩,⟨(-32),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![31,32,2,2],![31,32,1,2]], true⟩
theorem valid249 : row249.Valid := by decide +kernel
theorem piece249 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1380/43:ℝ) (740/23:ℝ) ∧
    (∫ x in (1380/43:ℝ)..(740/23:ℝ), innerR 7 6 (3/40) x / x^3) = (10783/108630150:ℝ) := by
  have h := row_integral row249 valid249
  norm_num [row249] at h ⊢
  exact h

def row250 : Row :=
  ⟨740/23,1200/37,(-1010),327/10, ![74,32,2,64,59],
   ![⟨0,0⟩,⟨(-32),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![31,32,2,2],![31,32,1,2]], false⟩
theorem valid250 : row250.Valid := by decide +kernel
theorem piece250 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (740/23:ℝ) (1200/37:ℝ) ∧
    (∫ x in (740/23:ℝ)..(1200/37:ℝ), innerR 7 6 (3/40) x / x^3) = (139997/394272000:ℝ) := by
  have h := row_integral row250 valid250
  norm_num [row250] at h ⊢
  exact h

def row251 : Row :=
  ⟨1200/37,65/2,(-1160),1493/40, ![74,32,2,64,60],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨(-32),1⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![32,32,1,2],![31,32,1,2]], false⟩
theorem valid251 : row251.Valid := by decide +kernel
theorem piece251 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1200/37:ℝ) (65/2:ℝ) ∧
    (∫ x in (1200/37:ℝ)..(65/2:ℝ), innerR 7 6 (3/40) x / x^3) = (2489/24336000:ℝ) := by
  have h := row_integral row251 valid251
  norm_num [row251] at h ⊢
  exact h

def row252 : Row :=
  ⟨65/2,1400/43,(-2385/2),1533/40, ![74,32,2,65,60],
   ![⟨0,0⟩,⟨(-2),3/40⟩,⟨33,(-1)⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![32,32,1,2],![32,33,1,2]], true⟩
theorem valid252 : row252.Valid := by decide +kernel
theorem piece252 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (65/2:ℝ) (1400/43:ℝ) ∧
    (∫ x in (65/2:ℝ)..(1400/43:ℝ), innerR 7 6 (3/40) x / x^3) = (24249/264992000:ℝ) := by
  have h := row_integral row252 valid252
  norm_num [row252] at h ⊢
  exact h

theorem block004 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1120/37:ℝ) (1400/43:ℝ) ∧
    (∫ x in (1120/37:ℝ)..(1400/43:ℝ), innerR 7 6 (3/40) x / x^3) =
      (19210226232986479165021/3235501353744520084224000:ℝ) := by
  have h := piece233
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (700/23:ℝ) (61/2:ℝ)
    (7087/12544000:ℝ) (168459/729316000:ℝ) h piece234
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (61/2:ℝ) (1320/43:ℝ)
    (37152103/46676224000:ℝ) (2085101/2881542400:ℝ) h piece235
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1320/43:ℝ) (1140/37:ℝ)
    (140691843/92587264000:ℝ) (23989/55911680:ℝ) h piece236
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1140/37:ℝ) (710/23:ℝ)
    (5920943593/3038545664000:ℝ) (5579/24605760:ℝ) h piece237
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (710/23:ℝ) (31:ℝ)
    (74100344111/34063696128000:ℝ) (6999/13646200:ℝ) h piece238
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (31:ℝ) (1340/43:ℝ)
    (87999994718831/32735211979008000:ℝ) (298949/862785800:ℝ) h piece239
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1340/43:ℝ) (720/23:ℝ)
    (14385435992312249/4740269889476352000:ℝ) (27587/86188800:ℝ) h piece240
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (720/23:ℝ) (1160/37:ℝ)
    (3542589545161/1055974579968000:ℝ) (5329/48441600:ℝ) h piece241
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1160/37:ℝ) (63/2:ℝ)
    (9231041367058363/2664223865259264000:ℝ) (3856963/10681372800:ℝ) h piece242
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (63/2:ℝ) (1360/43:ℝ)
    (3163367318749663/826828096114944000:ℝ) (9610381/29364249600:ℝ) h piece243
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1360/43:ℝ) (95/3:ℝ)
    (110268688837423513/26550368864135424000:ℝ) (54547/534164480:ℝ) h piece244
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (95/3:ℝ) (730/23:ℝ)
    (126271674428552141/29673941671680768000:ℝ) (29889/153901520:ℝ) h piece245
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (730/23:ℝ) (1180/37:ℝ)
    (37032233325054986831/8322759745704569088000:ℝ) (3137277/7420099600:ℝ) h piece246
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1180/37:ℝ) (32:ℝ)
    (1933679391961482217727/396870228421884999936000:ℝ) (55271/178227200:ℝ) h piece247
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (32:ℝ) (1380/43:ℝ)
    (17430126804158004899/3363307020524449152000:ℝ) (347/3250176:ℝ) h piece248
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1380/43:ℝ) (740/23:ℝ)
    (18820978955713877469517/3558378827714867202816000:ℝ) (10783/108630150:ℝ) h piece249
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (740/23:ℝ) (1200/37:ℝ)
    (49620933935229678749557/9208734622195941778176000:ℝ) (139997/394272000:ℝ) h piece250
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (1200/37:ℝ) (65/2:ℝ)
    (158831068143673570401/27653857724312137472000:ℝ) (2489/24336000:ℝ) h piece251
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1120/37:ℝ) (65/2:ℝ) (1400/43:ℝ)
    (245883957888765807465409/42061517598678761094912000:ℝ) (24249/264992000:ℝ) h piece252
  norm_num at h
  exact h

end U66Data
