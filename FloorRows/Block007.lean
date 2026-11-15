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

def row293 : Row :=
  ⟨1600/43,1380/37,(-1333),1321/40, ![85,37,2,74,68],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-37),1⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![36,37,2,3]], true⟩
theorem valid293 : row293.Valid := by decide +kernel
theorem piece293 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1600/43:ℝ) (1380/37:ℝ) ∧
    (∫ x in (1600/43:ℝ)..(1380/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(4261397/24376320000:ℝ)) := by
  have h := row_integral row293 valid293
  norm_num [row293] at h ⊢
  exact h

def row294 : Row :=
  ⟨1380/37,860/23,(-1402),279/8, ![85,37,2,74,69],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-37),1⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![36,37,2,3]], true⟩
theorem valid294 : row294.Valid := by decide +kernel
theorem piece294 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1380/37:ℝ) (860/23:ℝ) ∧
    (∫ x in (1380/37:ℝ)..(860/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(316591/1760617800:ℝ)) := by
  have h := row_integral row294 valid294
  norm_num [row294] at h ⊢
  exact h

def row295 : Row :=
  ⟨860/23,75/2,(-1359),1349/40, ![86,37,2,74,69],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-37),1⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![36,37,2,3]], false⟩
theorem valid295 : row295.Valid := by decide +kernel
theorem piece295 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (860/23:ℝ) (75/2:ℝ) ∧
    (∫ x in (860/23:ℝ)..(75/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(11041/55470000:ℝ)) := by
  have h := row_integral row295 valid295
  norm_num [row295] at h ⊢
  exact h

def row296 : Row :=
  ⟨75/2,1620/43,(-2793/2),1389/40, ![86,37,2,75,69],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨38,(-1)⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![37,38,2,3]], true⟩
theorem valid296 : row296.Valid := by decide +kernel
theorem piece296 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (75/2:ℝ) (1620/43:ℝ) ∧
    (∫ x in (75/2:ℝ)..(1620/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(26231/87480000:ℝ)) := by
  have h := row_integral row296 valid296
  norm_num [row296] at h ⊢
  exact h

def row297 : Row :=
  ⟨1620/43,870/23,(-2793/2),1389/40, ![86,37,2,75,69],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨38,(-1)⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![37,38,2,3]], true⟩
theorem valid297 : row297.Valid := by decide +kernel
theorem piece297 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1620/43:ℝ) (870/23:ℝ) ∧
    (∫ x in (1620/43:ℝ)..(870/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(28417/117713088:ℝ)) := by
  have h := row_integral row297 valid297
  norm_num [row297] at h ⊢
  exact h

def row298 : Row :=
  ⟨870/23,1400/37,(-1353),1343/40, ![87,37,2,75,69],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨38,(-1)⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,37,2,3],![37,38,2,3]], false⟩
theorem valid298 : row298.Valid := by decide +kernel
theorem piece298 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (870/23:ℝ) (1400/37:ℝ) ∧
    (∫ x in (870/23:ℝ)..(1400/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(59233/3296720000:ℝ)) := by
  have h := row_integral row298 valid298
  norm_num [row298] at h ⊢
  exact h

def row299 : Row :=
  ⟨1400/37,38,(-1528),191/5, ![87,37,2,75,70],
   ![⟨0,0⟩,⟨38,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![37,38,2,2],![37,38,2,3]], false⟩
theorem valid299 : row299.Valid := by decide +kernel
theorem piece299 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1400/37:ℝ) (38:ℝ) ∧
    (∫ x in (1400/37:ℝ)..(38:ℝ), innerR 7 6 (3/40) x / x^3) = (-(41829/176890000:ℝ)) := by
  have h := row_integral row299 valid299
  norm_num [row299] at h ⊢
  exact h

def row300 : Row :=
  ⟨38,1640/43,(-1566),747/20, ![87,38,2,76,70],
   ![⟨0,0⟩,⟨(-38),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![37,38,2,2],![37,38,2,3]], true⟩
theorem valid300 : row300.Valid := by decide +kernel
theorem piece300 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (38:ℝ) (1640/43:ℝ) ∧
    (∫ x in (38:ℝ)..(1640/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(70767/194189120:ℝ)) := by
  have h := row_integral row300 valid300
  norm_num [row300] at h ⊢
  exact h

def row301 : Row :=
  ⟨1640/43,880/23,(-1443),273/8, ![87,38,2,76,70],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-38),1⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![37,38,2,3]], true⟩
theorem valid301 : row301.Valid := by decide +kernel
theorem piece301 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1640/43:ℝ) (880/23:ℝ) ∧
    (∫ x in (1640/43:ℝ)..(880/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(790101/2603532800:ℝ)) := by
  have h := row_integral row301 valid301
  norm_num [row301] at h ⊢
  exact h

def row302 : Row :=
  ⟨880/23,115/3,(-1399),1319/40, ![88,38,2,76,70],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-38),1⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![37,38,2,3]], false⟩
theorem valid302 : row302.Valid := by decide +kernel
theorem piece302 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (880/23:ℝ) (115/3:ℝ) ∧
    (∫ x in (880/23:ℝ)..(115/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(28783/163863040:ℝ)) := by
  have h := row_integral row302 valid302
  norm_num [row302] at h ⊢
  exact h

def row303 : Row :=
  ⟨115/3,1420/37,(-1399),1319/40, ![88,38,2,76,70],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-38),1⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![37,38,2,3]], false⟩
theorem valid303 : row303.Valid := by decide +kernel
theorem piece303 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (115/3:ℝ) (1420/37:ℝ) ∧
    (∫ x in (115/3:ℝ)..(1420/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(22857/213335120:ℝ)) := by
  have h := row_integral row303 valid303
  norm_num [row303] at h ⊢
  exact h

def row304 : Row :=
  ⟨1420/37,77/2,(-1470),1393/40, ![88,38,2,76,71],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-38),1⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![37,38,2,3]], false⟩
theorem valid304 : row304.Valid := by decide +kernel
theorem piece304 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1420/37:ℝ) (77/2:ℝ) ∧
    (∫ x in (1420/37:ℝ)..(77/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(137259/487968800:ℝ)) := by
  have h := row_integral row304 valid304
  norm_num [row304] at h ⊢
  exact h

def row305 : Row :=
  ⟨77/2,1660/43,(-3017/2),1433/40, ![88,38,2,77,71],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨39,(-1)⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![38,39,2,3]], true⟩
theorem valid305 : row305.Valid := by decide +kernel
theorem piece305 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (77/2:ℝ) (1660/43:ℝ) ∧
    (∫ x in (77/2:ℝ)..(1660/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2171727/9335972800:ℝ)) := by
  have h := row_integral row305 valid305
  norm_num [row305] at h ⊢
  exact h

def row306 : Row :=
  ⟨1660/43,890/23,(-3017/2),1433/40, ![88,38,2,77,71],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨39,(-1)⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![38,39,2,3]], true⟩
theorem valid306 : row306.Valid := by decide +kernel
theorem piece306 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1660/43:ℝ) (890/23:ℝ) ∧
    (∫ x in (1660/43:ℝ)..(890/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(17044407/87308430400:ℝ)) := by
  have h := row_integral row306 valid306
  norm_num [row306] at h ⊢
  exact h

def row307 : Row :=
  ⟨890/23,1440/37,(-1464),1387/40, ![89,38,2,77,71],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨39,(-1)⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,38,2,3],![38,39,2,3]], false⟩
theorem valid307 : row307.Valid := by decide +kernel
theorem piece307 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (890/23:ℝ) (1440/37:ℝ) ∧
    (∫ x in (890/23:ℝ)..(1440/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9671/21386700:ℝ)) := by
  have h := row_integral row307 valid307
  norm_num [row307] at h ⊢
  exact h

def row308 : Row :=
  ⟨1440/37,39,(-1644),393/10, ![89,38,2,77,72],
   ![⟨0,0⟩,⟨39,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![38,38,2,2],![38,39,2,2],![38,39,2,3]], false⟩
theorem valid308 : row308.Valid := by decide +kernel
theorem piece308 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1440/37:ℝ) (39:ℝ) ∧
    (∫ x in (1440/37:ℝ)..(39:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9041/58406400:ℝ)) := by
  have h := row_integral row308 valid308
  norm_num [row308] at h ⊢
  exact h

def row309 : Row :=
  ⟨39,1680/43,(-1683),769/20, ![89,39,2,78,72],
   ![⟨0,0⟩,⟨(-39),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![38,39,2,2],![38,39,2,3]], true⟩
theorem valid309 : row309.Valid := by decide +kernel
theorem piece309 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (39:ℝ) (1680/43:ℝ) ∧
    (∫ x in (39:ℝ)..(1680/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(67927/317990400:ℝ)) := by
  have h := row_integral row309 valid309
  norm_num [row309] at h ⊢
  exact h

def row310 : Row :=
  ⟨1680/43,900/23,(-1557),1409/40, ![89,39,2,78,72],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-39),1⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![38,39,2,3]], true⟩
theorem valid310 : row310.Valid := by decide +kernel
theorem piece310 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1680/43:ℝ) (900/23:ℝ) ∧
    (∫ x in (1680/43:ℝ)..(900/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(8579/47040000:ℝ)) := by
  have h := row_integral row310 valid310
  norm_num [row310] at h ⊢
  exact h

def row311 : Row :=
  ⟨900/23,1460/37,(-1512),1363/40, ![90,39,2,78,72],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-39),1⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![38,39,2,3]], false⟩
theorem valid311 : row311.Valid := by decide +kernel
theorem piece311 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (900/23:ℝ) (1460/37:ℝ) ∧
    (∫ x in (900/23:ℝ)..(1460/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(450079/479610000:ℝ)) := by
  have h := row_integral row311 valid311
  norm_num [row311] at h ⊢
  exact h

def row312 : Row :=
  ⟨1460/37,79/2,(-1585),1437/40, ![90,39,2,78,73],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-39),1⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![38,39,2,3]], false⟩
theorem valid312 : row312.Valid := by decide +kernel
theorem piece312 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1460/37:ℝ) (79/2:ℝ) ∧
    (∫ x in (1460/37:ℝ)..(79/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(365241/3325828900:ℝ)) := by
  have h := row_integral row312 valid312
  norm_num [row312] at h ⊢
  exact h

theorem block007 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1600/43:ℝ) (79/2:ℝ) ∧
    (∫ x in (1600/43:ℝ)..(79/2:ℝ), innerR 7 6 (3/40) x / x^3) =
      (-(5004596518329758699088043/988968453237774924794880000:ℝ)) := by
  have h := piece293
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1380/37:ℝ) (860/23:ℝ)
    (-(4261397/24376320000:ℝ)) (-(316591/1760617800:ℝ)) h piece294
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (860/23:ℝ) (75/2:ℝ)
    (-(231652937/653214720000:ℝ)) (-(11041/55470000:ℝ)) h piece295
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (75/2:ℝ) (1620/43:ℝ)
    (-(2803657/5063680000:ℝ)) (-(26231/87480000:ℝ)) h piece296
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1620/43:ℝ) (870/23:ℝ)
    (-(9452232611/11074268160000:ℝ)) (-(28417/117713088:ℝ)) h piece297
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (870/23:ℝ) (1400/37:ℝ)
    (-(4662862673/4258554880000:ℝ)) (-(59233/3296720000:ℝ)) h piece298
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1400/37:ℝ) (38:ℝ)
    (-(1601582641/1439097856000:ℝ)) (-(41829/176890000:ℝ)) h piece299
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (38:ℝ) (1640/43:ℝ)
    (-(500728830299/371081661440000:ℝ)) (-(70767/194189120:ℝ)) h piece300
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1640/43:ℝ) (880/23:ℝ)
    (-(56265685071401/32830961730560000:ℝ)) (-(790101/2603532800:ℝ)) h piece301
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (880/23:ℝ) (115/3:ℝ)
    (-(195456270009481/96891374863360000:ℝ)) (-(28783/163863040:ℝ)) h piece302
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (115/3:ℝ) (1420/37:ℝ)
    (-(444266975956733/202591056532480000:ℝ)) (-(22857/213335120:ℝ)) h piece303
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1420/37:ℝ) (77/2:ℝ)
    (-(102129091401875611/44402674607836160000:ℝ)) (-(137259/487968800:ℝ)) h piece304
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (77/2:ℝ) (1660/43:ℝ)
    (-(17757867207991951/6879287615298560000:ℝ)) (-(2171727/9335972800:ℝ)) h piece305
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1660/43:ℝ) (890/23:ℝ)
    (-(12123463822497470549/4308310216526525440000:ℝ)) (-(17044407/87308430400:ℝ)) h piece306
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (890/23:ℝ) (1440/37:ℝ)
    (-(14906674508224998461/4953712472798172160000:ℝ)) (-(9671/21386700:ℝ)) h piece307
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1440/37:ℝ) (39:ℝ)
    (-(5201816378159702023/1502811649051130880000:ℝ)) (-(9041/58406400:ℝ)) h piece308
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (39:ℝ) (1680/43:ℝ)
    (-(306140324294384736229/84658389563213706240000:ℝ)) (-(67927/317990400:ℝ)) h piece309
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1680/43:ℝ) (900/23:ℝ)
    (-(174582416577193903231/45585286687884303360000:ℝ)) (-(8579/47040000:ℝ)) h piece310
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (900/23:ℝ) (1460/37:ℝ)
    (-(26128015823270653081/6512183812554900480000:ℝ)) (-(450079/479610000:ℝ)) h piece311
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1600/43:ℝ) (1460/37:ℝ) (79/2:ℝ)
    (-(57267610545073092508579/11567809179035021552640000:ℝ)) (-(365241/3325828900:ℝ)) h piece312
  norm_num at h
  exact h

end U66Data
