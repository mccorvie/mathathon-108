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

def row253 : Row :=
  ⟨1400/43,750/23,(-2175/2),351/10, ![74,32,2,65,60],
   ![⟨0,0⟩,⟨33,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![32,33,2,2],![32,33,1,2]], true⟩
theorem valid253 : row253.Valid := by decide +kernel
theorem piece253 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1400/43:ℝ) (750/23:ℝ) ∧
    (∫ x in (1400/43:ℝ)..(750/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1931/23520000:ℝ) := by
  have h := row_integral row253 valid253
  norm_num [row253] at h ⊢
  exact h

def row254 : Row :=
  ⟨750/23,1220/37,(-1050),679/20, ![75,32,2,65,60],
   ![⟨0,0⟩,⟨33,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![32,33,2,2],![32,33,1,2]], false⟩
theorem valid254 : row254.Valid := by decide +kernel
theorem piece254 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (750/23:ℝ) (1220/37:ℝ) ∧
    (∫ x in (750/23:ℝ)..(1220/37:ℝ), innerR 7 6 (3/40) x / x^3) = (1519/2325625:ℝ) := by
  have h := row_integral row254 valid254
  norm_num [row254] at h ⊢
  exact h

def row255 : Row :=
  ⟨1220/37,33,(-1111),179/5, ![75,32,2,65,61],
   ![⟨0,0⟩,⟨33,(-1)⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![32,32,2,2],![32,33,2,2],![32,33,1,2]], false⟩
theorem valid255 : row255.Valid := by decide +kernel
theorem piece255 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1220/37:ℝ) (33:ℝ) ∧
    (∫ x in (1220/37:ℝ)..(33:ℝ), innerR 7 6 (3/40) x / x^3) = (3103/58940640:ℝ) := by
  have h := row_integral row255 valid255
  norm_num [row255] at h ⊢
  exact h

def row256 : Row :=
  ⟨33,1420/43,(-1144),699/20, ![75,33,2,66,61],
   ![⟨0,0⟩,⟨(-33),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![32,33,2,2],![32,33,1,2]], true⟩
theorem valid256 : row256.Valid := by decide +kernel
theorem piece256 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (33:ℝ) (1420/43:ℝ) ∧
    (∫ x in (33:ℝ)..(1420/43:ℝ), innerR 7 6 (3/40) x / x^3) = (1259/199623600:ℝ) := by
  have h := row_integral row256 valid256
  norm_num [row256] at h ⊢
  exact h

def row257 : Row :=
  ⟨1420/43,760/23,(-1144),699/20, ![75,33,2,66,61],
   ![⟨0,0⟩,⟨(-33),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![32,33,2,2],![32,33,1,2]], true⟩
theorem valid257 : row257.Valid := by decide +kernel
theorem piece257 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1420/43:ℝ) (760/23:ℝ) ∧
    (∫ x in (1420/43:ℝ)..(760/23:ℝ), innerR 7 6 (3/40) x / x^3) = (8589/1455840800:ℝ) := by
  have h := row_integral row257 valid257
  norm_num [row257] at h ⊢
  exact h

def row258 : Row :=
  ⟨760/23,100/3,(-1106),169/5, ![76,33,2,66,61],
   ![⟨0,0⟩,⟨(-33),1⟩,⟨(-2),3/40⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![32,33,2,2],![32,33,1,2]], false⟩
theorem valid258 : row258.Valid := by decide +kernel
theorem piece258 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (760/23:ℝ) (100/3:ℝ) ∧
    (∫ x in (760/23:ℝ)..(100/3:ℝ), innerR 7 6 (3/40) x / x^3) = (1803/14440000:ℝ) := by
  have h := row_integral row258 valid258
  norm_num [row258] at h ⊢
  exact h

def row259 : Row :=
  ⟨100/3,770/23,(-1146),35, ![76,33,2,66,61],
   ![⟨0,0⟩,⟨(-33),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![32,33,2,2],![32,33,2,3]], true⟩
theorem valid259 : row259.Valid := by decide +kernel
theorem piece259 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (100/3:ℝ) (770/23:ℝ) ∧
    (∫ x in (100/3:ℝ)..(770/23:ℝ), innerR 7 6 (3/40) x / x^3) = (5347/59290000:ℝ) := by
  have h := row_integral row259 valid259
  norm_num [row259] at h ⊢
  exact h

def row260 : Row :=
  ⟨770/23,1440/43,(-2215/2),677/20, ![77,33,2,66,61],
   ![⟨0,0⟩,⟨(-33),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![32,33,2,2],![32,33,2,3]], false⟩
theorem valid260 : row260.Valid := by decide +kernel
theorem piece260 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (770/23:ℝ) (1440/43:ℝ) ∧
    (∫ x in (770/23:ℝ)..(1440/43:ℝ), innerR 7 6 (3/40) x / x^3) = (343207/49177497600:ℝ) := by
  have h := row_integral row260 valid260
  norm_num [row260] at h ⊢
  exact h

def row261 : Row :=
  ⟨1440/43,67/2,(-1999/2),245/8, ![77,33,2,66,61],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-33),1⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![33,33,2,3],![32,33,2,3]], false⟩
theorem valid261 : row261.Valid := by decide +kernel
theorem piece261 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1440/43:ℝ) (67/2:ℝ) ∧
    (∫ x in (1440/43:ℝ)..(67/2:ℝ), innerR 7 6 (3/40) x / x^3) = (302561/37233561600:ℝ) := by
  have h := row_integral row261 valid261
  norm_num [row261] at h ⊢
  exact h

def row262 : Row :=
  ⟨67/2,1240/37,(-1033),253/8, ![77,33,2,67,61],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨34,(-1)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![33,33,2,3],![33,34,2,3]], true⟩
theorem valid262 : row262.Valid := by decide +kernel
theorem piece262 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (67/2:ℝ) (1240/37:ℝ) ∧
    (∫ x in (67/2:ℝ)..(1240/37:ℝ), innerR 7 6 (3/40) x / x^3) = (132163/13804572800:ℝ) := by
  have h := row_integral row262 valid262
  norm_num [row262] at h ⊢
  exact h

def row263 : Row :=
  ⟨1240/37,780/23,(-1188),145/4, ![77,33,2,67,62],
   ![⟨0,0⟩,⟨34,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![33,34,2,2],![33,34,2,3]], true⟩
theorem valid263 : row263.Valid := by decide +kernel
theorem piece263 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1240/37:ℝ) (780/23:ℝ) ∧
    (∫ x in (1240/37:ℝ)..(780/23:ℝ), innerR 7 6 (3/40) x / x^3) = (8653/24361350:ℝ) := by
  have h := row_integral row263 valid263
  norm_num [row263] at h ⊢
  exact h

def row264 : Row :=
  ⟨780/23,1460/43,(-1149),351/10, ![78,33,2,67,62],
   ![⟨0,0⟩,⟨34,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![33,34,2,2],![33,34,2,3]], false⟩
theorem valid264 : row264.Valid := by decide +kernel
theorem piece264 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (780/23:ℝ) (1460/43:ℝ) ∧
    (∫ x in (780/23:ℝ)..(1460/43:ℝ), innerR 7 6 (3/40) x / x^3) = (5881/135090150:ℝ) := by
  have h := row_integral row264 valid264
  norm_num [row264] at h ⊢
  exact h

def row265 : Row :=
  ⟨1460/43,34,(-1149),351/10, ![78,33,2,67,62],
   ![⟨0,0⟩,⟨34,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![33,33,2,2],![33,34,2,2],![33,34,2,3]], false⟩
theorem valid265 : row265.Valid := by decide +kernel
theorem piece265 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1460/43:ℝ) (34:ℝ) ∧
    (∫ x in (1460/43:ℝ)..(34:ℝ), innerR 7 6 (3/40) x / x^3) = (2547/49282592:ℝ) := by
  have h := row_integral row265 valid265
  norm_num [row265] at h ⊢
  exact h

def row266 : Row :=
  ⟨34,1260/37,(-1183),137/4, ![78,34,2,68,62],
   ![⟨0,0⟩,⟨(-34),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![33,34,2,2],![33,34,2,3]], true⟩
theorem valid266 : row266.Valid := by decide +kernel
theorem piece266 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (34:ℝ) (1260/37:ℝ) ∧
    (∫ x in (34:ℝ)..(1260/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3161/131090400:ℝ)) := by
  have h := row_integral row266 valid266
  norm_num [row266] at h ⊢
  exact h

def row267 : Row :=
  ⟨1260/37,790/23,(-1246),361/10, ![78,34,2,68,63],
   ![⟨0,0⟩,⟨(-34),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![33,34,2,2],![33,34,2,3]], true⟩
theorem valid267 : row267.Valid := by decide +kernel
theorem piece267 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1260/37:ℝ) (790/23:ℝ) ∧
    (∫ x in (1260/37:ℝ)..(790/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(4727/56618352:ℝ)) := by
  have h := row_integral row267 valid267
  norm_num [row267] at h ⊢
  exact h

def row268 : Row :=
  ⟨790/23,1480/43,(-2413/2),699/20, ![79,34,2,68,63],
   ![⟨0,0⟩,⟨(-34),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![33,34,2,2],![33,34,2,3]], false⟩
theorem valid268 : row268.Valid := by decide +kernel
theorem piece268 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (790/23:ℝ) (1480/43:ℝ) ∧
    (∫ x in (790/23:ℝ)..(1480/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(457779/54681145600:ℝ)) := by
  have h := row_integral row268 valid268
  norm_num [row268] at h ⊢
  exact h

def row269 : Row :=
  ⟨1480/43,69/2,(-2191/2),1269/40, ![79,34,2,68,63],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-34),1⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![34,34,2,3],![33,34,2,3]], false⟩
theorem valid269 : row269.Valid := by decide +kernel
theorem piece269 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1480/43:ℝ) (69/2:ℝ) ∧
    (∫ x in (1480/43:ℝ)..(69/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(189203/41713977600:ℝ)) := by
  have h := row_integral row269 valid269
  norm_num [row269] at h ⊢
  exact h

def row270 : Row :=
  ⟨69/2,1280/37,(-1130),1309/40, ![79,34,2,69,63],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨35,(-1)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![34,34,2,3],![34,35,2,3]], true⟩
theorem valid270 : row270.Valid := by decide +kernel
theorem piece270 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (69/2:ℝ) (1280/37:ℝ) ∧
    (∫ x in (69/2:ℝ)..(1280/37:ℝ), innerR 7 6 (3/40) x / x^3) = (9989/7800422400:ℝ) := by
  have h := row_integral row270 valid270
  norm_num [row270] at h ⊢
  exact h

def row271 : Row :=
  ⟨1280/37,800/23,(-1290),747/20, ![79,34,2,69,64],
   ![⟨0,0⟩,⟨35,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![34,35,2,2],![34,35,2,3]], true⟩
theorem valid271 : row271.Valid := by decide +kernel
theorem piece271 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1280/37:ℝ) (800/23:ℝ) ∧
    (∫ x in (1280/37:ℝ)..(800/23:ℝ), innerR 7 6 (3/40) x / x^3) = (207/8192000:ℝ) := by
  have h := row_integral row271 valid271
  norm_num [row271] at h ⊢
  exact h

def row272 : Row :=
  ⟨800/23,1500/43,(-1250),181/5, ![80,34,2,69,64],
   ![⟨0,0⟩,⟨35,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![34,35,2,2],![34,35,2,3]], false⟩
theorem valid272 : row272.Valid := by decide +kernel
theorem piece272 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (800/23:ℝ) (1500/43:ℝ) ∧
    (∫ x in (800/23:ℝ)..(1500/43:ℝ), innerR 7 6 (3/40) x / x^3) = (151/5760000:ℝ) := by
  have h := row_integral row272 valid272
  norm_num [row272] at h ⊢
  exact h

theorem block005 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1400/43:ℝ) (1500/43:ℝ) ∧
    (∫ x in (1400/43:ℝ)..(1500/43:ℝ), innerR 7 6 (3/40) x / x^3) =
      (210606056149584935207/148053555964500426240000:ℝ) := by
  have h := piece253
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (750/23:ℝ) (1220/37:ℝ)
    (1931/23520000:ℝ) (1519/2325625:ℝ) h piece254
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1220/37:ℝ) (33:ℝ)
    (64348259/87517920000:ℝ) (3103/58940640:ℝ) h piece255
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (33:ℝ) (1420/43:ℝ)
    (37303927/47345760000:ℝ) (1259/199623600:ℝ) h piece256
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1420/43:ℝ) (760/23:ℝ)
    (63184785469/79556658720000:ℝ) (8589/1455840800:ℝ) h piece257
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (760/23:ℝ) (100/3:ℝ)
    (4558449949/5697273120000:ℝ) (1803/14440000:ℝ) h piece258
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (100/3:ℝ) (770/23:ℝ)
    (277358947/299856480000:ℝ) (5347/59290000:ℝ) h piece259
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (770/23:ℝ) (1440/43:ℝ)
    (3348412721/3298421280000:ℝ) (343207/49177497600:ℝ) h piece260
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1440/43:ℝ) (67/2:ℝ)
    (132405338027/129537999360000:ℝ) (302561/37233561600:ℝ) h piece261
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (67/2:ℝ) (1240/37:ℝ)
    (924525951211/897370492480000:ℝ) (132163/13804572800:ℝ) h piece262
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1240/37:ℝ) (780/23:ℝ)
    (13383965297613/12871239451840000:ℝ) (8653/24361350:ℝ) h piece263
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (780/23:ℝ) (1460/43:ℝ)
    (293663386915361/210507045228480000:ℝ) (5881/135090150:ℝ) h piece264
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1460/43:ℝ) (34:ℝ)
    (124136012504605813/86291695694043840000:ℝ) (2547/49282592:ℝ) h piece265
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (34:ℝ) (1260/37:ℝ)
    (6973945813342933/4679733543925440000:ℝ) (-(3161/131090400:ℝ)) h piece266
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1260/37:ℝ) (790/23:ℝ)
    (10897045599588823/7432517981528640000:ℝ) (-(4727/56618352:ℝ)) h piece267
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (790/23:ℝ) (1480/43:ℝ)
    (7126191101054344927/5154038302524471360000:ℝ) (-(457779/54681145600:ℝ)) h piece268
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1480/43:ℝ) (69/2:ℝ)
    (122742851817403643047/89314916913367104960000:ℝ) (-(189203/41713977600:ℝ)) h piece269
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (69/2:ℝ) (1280/37:ℝ)
    (583033033152598254283/425653973397938725440000:ℝ) (9989/7800422400:ℝ) h piece270
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (1280/37:ℝ) (800/23:ℝ)
    (9743217200564158453789/7106570686296020459520000:ℝ) (207/8192000:ℝ) h piece271
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1400/43:ℝ) (800/23:ℝ) (1500/43:ℝ)
    (620174373161963365849/444160667893501278720000:ℝ) (151/5760000:ℝ) h piece272
  norm_num at h
  exact h

end U66Data
