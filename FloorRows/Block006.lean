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

def row273 : Row :=
  ⟨1500/43,35,(-1250),181/5, ![80,34,2,69,64],
   ![⟨0,0⟩,⟨35,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![34,34,2,2],![34,35,2,2],![34,35,2,3]], false⟩
theorem valid273 : row273.Valid := by decide +kernel
theorem piece273 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1500/43:ℝ) (35:ℝ) ∧
    (∫ x in (1500/43:ℝ)..(35:ℝ), innerR 7 6 (3/40) x / x^3) = (179/4410000:ℝ) := by
  have h := row_integral row273 valid273
  norm_num [row273] at h ⊢
  exact h

def row274 : Row :=
  ⟨35,1300/37,(-1285),707/20, ![80,35,2,70,64],
   ![⟨0,0⟩,⟨(-35),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![34,35,2,2],![34,35,2,3]], true⟩
theorem valid274 : row274.Valid := by decide +kernel
theorem piece274 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (35:ℝ) (1300/37:ℝ) ∧
    (∫ x in (35:ℝ)..(1300/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(4709/33124000:ℝ)) := by
  have h := row_integral row274 valid274
  norm_num [row274] at h ⊢
  exact h

def row275 : Row :=
  ⟨1300/37,810/23,(-1350),186/5, ![80,35,2,70,65],
   ![⟨0,0⟩,⟨(-35),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![34,35,2,2],![34,35,2,3]], true⟩
theorem valid275 : row275.Valid := by decide +kernel
theorem piece275 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1300/37:ℝ) (810/23:ℝ) ∧
    (∫ x in (1300/37:ℝ)..(810/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(6433/82134000:ℝ)) := by
  have h := row_integral row275 valid275
  norm_num [row275] at h ⊢
  exact h

def row276 : Row :=
  ⟨810/23,1520/43,(-2619/2),721/20, ![81,35,2,70,65],
   ![⟨0,0⟩,⟨(-35),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![34,35,2,2],![34,35,2,3]], false⟩
theorem valid276 : row276.Valid := by decide +kernel
theorem piece276 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (810/23:ℝ) (1520/43:ℝ) ∧
    (∫ x in (810/23:ℝ)..(1520/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(252343/2245708800:ℝ)) := by
  have h := row_integral row276 valid276
  norm_num [row276] at h ⊢
  exact h

def row277 : Row :=
  ⟨1520/43,71/2,(-2391/2),1313/40, ![81,35,2,70,65],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-35),1⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![35,35,2,3],![34,35,2,3]], false⟩
theorem valid277 : row277.Valid := by decide +kernel
theorem piece277 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1520/43:ℝ) (71/2:ℝ) ∧
    (∫ x in (1520/43:ℝ)..(71/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(5180071/46586905600:ℝ)) := by
  have h := row_integral row277 valid277
  norm_num [row277] at h ⊢
  exact h

def row278 : Row :=
  ⟨71/2,820/23,(-1231),1353/40, ![81,35,2,71,65],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨36,(-1)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![35,35,2,3],![35,36,2,3]], true⟩
theorem valid278 : row278.Valid := by decide +kernel
theorem piece278 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (71/2:ℝ) (820/23:ℝ) ∧
    (∫ x in (71/2:ℝ)..(820/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(7917/84739210:ℝ)) := by
  have h := row_integral row278 valid278
  norm_num [row278] at h ⊢
  exact h

def row279 : Row :=
  ⟨820/23,1320/37,(-1190),1307/40, ![82,35,2,71,65],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨36,(-1)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![35,35,2,3],![35,36,2,3]], false⟩
theorem valid279 : row279.Valid := by decide +kernel
theorem piece279 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/23:ℝ) (1320/37:ℝ) ∧
    (∫ x in (820/23:ℝ)..(1320/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(18727/1464487200:ℝ)) := by
  have h := row_integral row279 valid279
  norm_num [row279] at h ⊢
  exact h

def row280 : Row :=
  ⟨1320/37,1540/43,(-1355),373/10, ![82,35,2,71,66],
   ![⟨0,0⟩,⟨36,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![35,36,2,2],![35,36,2,3]], false⟩
theorem valid280 : row280.Valid := by decide +kernel
theorem piece280 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1320/37:ℝ) (1540/43:ℝ) ∧
    (∫ x in (1320/37:ℝ)..(1540/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1021/15523200:ℝ)) := by
  have h := row_integral row280 valid280
  norm_num [row280] at h ⊢
  exact h

def row281 : Row :=
  ⟨1540/43,36,(-1355),373/10, ![82,35,2,71,66],
   ![⟨0,0⟩,⟨36,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![35,35,2,2],![35,36,2,2],![35,36,2,3]], false⟩
theorem valid281 : row281.Valid := by decide +kernel
theorem piece281 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1540/43:ℝ) (36:ℝ) ∧
    (∫ x in (1540/43:ℝ)..(36:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1513/24012450:ℝ)) := by
  have h := row_integral row281 valid281
  norm_num [row281] at h ⊢
  exact h

def row282 : Row :=
  ⟨36,830/23,(-1391),729/20, ![82,36,2,72,66],
   ![⟨0,0⟩,⟨(-36),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![35,36,2,2],![35,36,2,3]], true⟩
theorem valid282 : row282.Valid := by decide +kernel
theorem piece282 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (36:ℝ) (830/23:ℝ) ∧
    (∫ x in (36:ℝ)..(830/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(64013/446407200:ℝ)) := by
  have h := row_integral row282 valid282
  norm_num [row282] at h ⊢
  exact h

def row283 : Row :=
  ⟨830/23,1340/37,(-2699/2),353/10, ![83,36,2,72,66],
   ![⟨0,0⟩,⟨(-36),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![35,36,2,2],![35,36,2,3]], false⟩
theorem valid283 : row283.Valid := by decide +kernel
theorem piece283 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (830/23:ℝ) (1340/37:ℝ) ∧
    (∫ x in (830/23:ℝ)..(1340/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9929513/49479553600:ℝ)) := by
  have h := row_integral row283 valid283
  norm_num [row283] at h ⊢
  exact h

def row284 : Row :=
  ⟨1340/37,1560/43,(-2833/2),743/20, ![83,36,2,72,67],
   ![⟨0,0⟩,⟨(-36),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![35,36,2,2],![35,36,2,3]], false⟩
theorem valid284 : row284.Valid := by decide +kernel
theorem piece284 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1340/37:ℝ) (1560/43:ℝ) ∧
    (∫ x in (1340/37:ℝ)..(1560/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(806239/8739544320:ℝ)) := by
  have h := row_integral row284 valid284
  norm_num [row284] at h ⊢
  exact h

def row285 : Row :=
  ⟨1560/43,73/2,(-2599/2),1357/40, ![83,36,2,72,67],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨(-36),1⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,36,2,3],![35,36,2,3]], false⟩
theorem valid285 : row285.Valid := by decide +kernel
theorem piece285 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1560/43:ℝ) (73/2:ℝ) ∧
    (∫ x in (1560/43:ℝ)..(73/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(618355/2074984704:ℝ)) := by
  have h := row_integral row285 valid285
  norm_num [row285] at h ⊢
  exact h

def row286 : Row :=
  ⟨73/2,840/23,(-1336),1397/40, ![83,36,2,73,67],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨37,(-1)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,36,2,3],![36,37,2,3]], true⟩
theorem valid286 : row286.Valid := by decide +kernel
theorem piece286 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (73/2:ℝ) (840/23:ℝ) ∧
    (∫ x in (73/2:ℝ)..(840/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(102211/3760142400:ℝ)) := by
  have h := row_integral row286 valid286
  norm_num [row286] at h ⊢
  exact h

def row287 : Row :=
  ⟨840/23,110/3,(-1294),1351/40, ![84,36,2,73,67],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨37,(-1)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,36,2,3],![36,37,2,3]], false⟩
theorem valid287 : row287.Valid := by decide +kernel
theorem piece287 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (840/23:ℝ) (110/3:ℝ) ∧
    (∫ x in (840/23:ℝ)..(110/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(7327/42688800:ℝ)) := by
  have h := row_integral row287 valid287
  norm_num [row287] at h ⊢
  exact h

def row288 : Row :=
  ⟨110/3,1580/43,(-2577/2),269/8, ![84,36,2,73,67],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨37,(-1)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,36,2,3],![36,37,2,3]], true⟩
theorem valid288 : row288.Valid := by decide +kernel
theorem piece288 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (110/3:ℝ) (1580/43:ℝ) ∧
    (∫ x in (110/3:ℝ)..(1580/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(102809/1208257600:ℝ)) := by
  have h := row_integral row288 valid288
  norm_num [row288] at h ⊢
  exact h

def row289 : Row :=
  ⟨1580/43,1360/37,(-2577/2),269/8, ![84,36,2,73,67],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨37,(-1)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,36,2,3],![36,37,2,3]], true⟩
theorem valid289 : row289.Valid := by decide +kernel
theorem piece289 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1580/43:ℝ) (1360/37:ℝ) ∧
    (∫ x in (1580/43:ℝ)..(1360/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(617039/46173414400:ℝ)) := by
  have h := row_integral row289 valid289
  norm_num [row289] at h ⊢
  exact h

def row290 : Row :=
  ⟨1360/37,850/23,(-2917/2),153/4, ![84,36,2,73,68],
   ![⟨0,0⟩,⟨37,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,37,2,2],![36,37,2,3]], true⟩
theorem valid290 : row290.Valid := by decide +kernel
theorem piece290 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1360/37:ℝ) (850/23:ℝ) ∧
    (∫ x in (1360/37:ℝ)..(850/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(35973/184960000:ℝ)) := by
  have h := row_integral row290 valid290
  norm_num [row290] at h ⊢
  exact h

def row291 : Row :=
  ⟨850/23,37,(-1416),371/10, ![85,36,2,73,68],
   ![⟨0,0⟩,⟨37,(-1)⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![36,36,2,2],![36,37,2,2],![36,37,2,3]], false⟩
theorem valid291 : row291.Valid := by decide +kernel
theorem piece291 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (850/23:ℝ) (37:ℝ) ∧
    (∫ x in (850/23:ℝ)..(37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(37513/989102500:ℝ)) := by
  have h := row_integral row291 valid291
  norm_num [row291] at h ⊢
  exact h

def row292 : Row :=
  ⟨37,1600/43,(-1453),145/4, ![85,37,2,74,68],
   ![⟨0,0⟩,⟨(-37),1⟩,⟨3,(-3/40)⟩,⟨1/2,0⟩],
   ![![37,37,2,2],![36,37,2,2],![36,37,2,3]], true⟩
theorem valid292 : row292.Valid := by decide +kernel
theorem piece292 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (37:ℝ) (1600/43:ℝ) ∧
    (∫ x in (37:ℝ)..(1600/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3100707/7009280000:ℝ)) := by
  have h := row_integral row292 valid292
  norm_num [row292] at h ⊢
  exact h

theorem block006 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1500/43:ℝ) (1600/43:ℝ) ∧
    (∫ x in (1500/43:ℝ)..(1600/43:ℝ), innerR 7 6 (3/40) x / x^3) =
      (-(2749509615197511216503/1172576699628975793152000:ℝ)) := by
  have h := piece273
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (35:ℝ) (1300/37:ℝ)
    (179/4410000:ℝ) (-(4709/33124000:ℝ)) h piece274
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1300/37:ℝ) (810/23:ℝ)
    (-(21629/212940000:ℝ)) (-(6433/82134000:ℝ)) h piece275
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (810/23:ℝ) (1520/43:ℝ)
    (-(79561/442260000:ℝ)) (-(252343/2245708800:ℝ)) h piece276
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1520/43:ℝ) (71/2:ℝ)
    (-(497722999/1702995840000:ℝ)) (-(5180071/46586905600:ℝ)) h piece277
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (71/2:ℝ) (820/23:ℝ)
    (-(45573410809/112957921440000:ℝ)) (-(7917/84739210:ℝ)) h piece278
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (820/23:ℝ) (1320/37:ℝ)
    (-(1328861837999/2674398111840000:ℝ)) (-(18727/1464487200:ℝ)) h piece279
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1320/37:ℝ) (1540/43:ℝ)
    (-(4022690644519/7892735891040000:ℝ)) (-(1021/15523200:ℝ)) h piece280
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1540/43:ℝ) (36:ℝ)
    (-(31792710478783/55249151237280000:ℝ)) (-(1513/24012450:ℝ)) h piece281
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (36:ℝ) (830/23:ℝ)
    (-(152700879593/239173814880000:ℝ)) (-(64013/446407200:ℝ)) h piece282
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (830/23:ℝ) (1340/37:ℝ)
    (-(3864676180951931/4943005232124960000:ℝ)) (-(9929513/49479553600:ℝ)) h piece283
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1340/37:ℝ) (1560/43:ℝ)
    (-(262667836704825373/267339162494083680000:ℝ)) (-(806239/8739544320:ℝ)) h piece284
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1560/43:ℝ) (73/2:ℝ)
    (-(27875333917368011/25935888898679760000:ℝ)) (-(618355/2074984704:ℝ)) h piece285
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (73/2:ℝ) (840/23:ℝ)
    (-(29190087997748723701/21263438760163760160000:ℝ)) (-(102211/3760142400:ℝ)) h piece286
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (840/23:ℝ) (110/3:ℝ)
    (-(2854474064869823359/2038959881111593440000:ℝ)) (-(7327/42688800:ℝ)) h piece287
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (110/3:ℝ) (1580/43:ℝ)
    (-(5035542432683966507/3204079813175361120000:ℝ)) (-(102809/1208257600:ℝ)) h piece288
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1580/43:ℝ) (1360/37:ℝ)
    (-(3011664470288146427317/1817878374002493522720000:ℝ)) (-(617039/46173414400:ℝ)) h piece289
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (1360/37:ℝ) (850/23:ℝ)
    (-(562340508492729438247/336719660366428859520000:ℝ)) (-(35973/184960000:ℝ)) h piece290
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (850/23:ℝ) (37:ℝ)
    (-(19619667224193200939/10522489386450901860000:ℝ)) (-(37513/989102500:ℝ)) h piece291
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1500/43:ℝ) (37:ℝ) (1600/43:ℝ)
    (-(1612097866474373149867/847369880591252038020000:ℝ)) (-(3100707/7009280000:ℝ)) h piece292
  norm_num at h
  exact h

end U66Data
