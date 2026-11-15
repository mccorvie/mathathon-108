import RowSoundness

/-!
E609, Codex lane C. PROOF-DRAFT until final gate. Fauzan re-derivation using
Firsching formalisation, Paul-Lez Comparator metadata, Apache-2.0.
Actual five-floor, four-node, twelve-gamma-floor and maximum-branch data.
Each Valid certificate is checked with kernel decide; no native evaluator.
Field order: l,r,a,b; five global floors; four affine nodes; 3x4 z floors; max bit.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set Mathathon.P108 SplitCells
noncomputable section
namespace SplitData

def row120 : Row :=
  ⟨620/37,390/23,(-545/2),409/20, ![38,16,1,33,31],
   ![⟨0,0⟩,⟨17,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,17,1,1],![16,17,0,1]], true⟩
theorem valid120 : row120.Valid := by decide +kernel
theorem piece120 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (620/37:ℝ) (390/23:ℝ) ∧
    (∫ x in (620/37:ℝ)..(390/23:ℝ), innerR 7 6 (3/40) x / x^3) = (7043423/2338689600:ℝ) := by
  have h := row_integral row120 valid120
  norm_num [row120] at h ⊢
  exact h

def row121 : Row :=
  ⟨390/23,17,(-253),193/10, ![39,16,1,33,31],
   ![⟨0,0⟩,⟨17,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,17,1,1],![16,17,0,1]], false⟩
theorem valid121 : row121.Valid := by decide +kernel
theorem piece121 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (390/23:ℝ) (17:ℝ) ∧
    (∫ x in (390/23:ℝ)..(17:ℝ), innerR 7 6 (3/40) x / x^3) = (2333/3516552:ℝ) := by
  have h := row_integral row121 valid121
  norm_num [row121] at h ⊢
  exact h

def row122 : Row :=
  ⟨17,740/43,(-270),369/20, ![39,17,1,34,31],
   ![⟨0,0⟩,⟨(-17),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![16,17,1,1],![16,17,0,1]], true⟩
theorem valid122 : row122.Valid := by decide +kernel
theorem piece122 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (17:ℝ) (740/43:ℝ) ∧
    (∫ x in (17:ℝ)..(740/43:ℝ), innerR 7 6 (3/40) x / x^3) = (75411/39564100:ℝ) := by
  have h := row_integral row122 valid122
  norm_num [row122] at h ⊢
  exact h

def row123 : Row :=
  ⟨740/43,640/37,(-270),369/20, ![39,17,1,34,31],
   ![⟨0,0⟩,⟨(-17),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![16,17,1,1],![16,17,0,1]], true⟩
theorem valid123 : row123.Valid := by decide +kernel
theorem piece123 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (740/43:ℝ) (640/37:ℝ) ∧
    (∫ x in (740/43:ℝ)..(640/37:ℝ), innerR 7 6 (3/40) x / x^3) = (464247/560742400:ℝ) := by
  have h := row_integral row123 valid123
  norm_num [row123] at h ⊢
  exact h

def row124 : Row :=
  ⟨640/37,400/23,(-350),923/40, ![39,17,1,34,32],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-17),1⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,17,0,1],![16,17,0,1]], true⟩
theorem valid124 : row124.Valid := by decide +kernel
theorem piece124 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (640/37:ℝ) (400/23:ℝ) ∧
    (∫ x in (640/37:ℝ)..(400/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1853/2048000:ℝ) := by
  have h := row_integral row124 valid124
  norm_num [row124] at h ⊢
  exact h

def row125 : Row :=
  ⟨400/23,35/2,(-330),877/40, ![40,17,1,34,32],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-17),1⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,17,0,1],![16,17,0,1]], false⟩
theorem valid125 : row125.Valid := by decide +kernel
theorem piece125 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (400/23:ℝ) (35/2:ℝ) ∧
    (∫ x in (400/23:ℝ)..(35/2:ℝ), innerR 7 6 (3/40) x / x^3) = (337/313600:ℝ) := by
  have h := row_integral row125 valid125
  norm_num [row125] at h ⊢
  exact h

def row126 : Row :=
  ⟨35/2,760/43,(-695/2),917/40, ![40,17,1,35,32],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨18,(-1)⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,17,0,1],![17,18,0,1]], true⟩
theorem valid126 : row126.Valid := by decide +kernel
theorem piece126 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (35/2:ℝ) (760/43:ℝ) ∧
    (∫ x in (35/2:ℝ)..(760/43:ℝ), innerR 7 6 (3/40) x / x^3) = (202107/113209600:ℝ) := by
  have h := row_integral row126 valid126
  norm_num [row126] at h ⊢
  exact h

def row127 : Row :=
  ⟨760/43,410/23,(-581/2),197/10, ![40,17,1,35,32],
   ![⟨0,0⟩,⟨18,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,18,1,1],![17,18,0,1]], true⟩
theorem valid127 : row127.Valid := by decide +kernel
theorem piece127 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (760/43:ℝ) (410/23:ℝ) ∧
    (∫ x in (760/43:ℝ)..(410/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1246551/776756480:ℝ) := by
  have h := row_integral row127 valid127
  norm_num [row127] at h ⊢
  exact h

def row128 : Row :=
  ⟨410/23,660/37,(-270),371/20, ![41,17,1,35,32],
   ![⟨0,0⟩,⟨18,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,18,1,1],![17,18,0,1]], false⟩
theorem valid128 : row128.Valid := by decide +kernel
theorem piece128 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (410/23:ℝ) (660/37:ℝ) ∧
    (∫ x in (410/23:ℝ)..(660/37:ℝ), innerR 7 6 (3/40) x / x^3) = (15373/122040600:ℝ) := by
  have h := row_integral row128 valid128
  norm_num [row128] at h ⊢
  exact h

def row129 : Row :=
  ⟨660/37,18,(-303),102/5, ![41,17,1,35,33],
   ![⟨0,0⟩,⟨18,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![17,17,1,1],![17,18,1,1],![17,18,0,1]], false⟩
theorem valid129 : row129.Valid := by decide +kernel
theorem piece129 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (660/37:ℝ) (18:ℝ) ∧
    (∫ x in (660/37:ℝ)..(18:ℝ), innerR 7 6 (3/40) x / x^3) = (4607/2613600:ℝ) := by
  have h := row_integral row129 valid129
  norm_num [row129] at h ⊢
  exact h

def row130 : Row :=
  ⟨18,780/43,(-321),391/20, ![41,18,1,36,33],
   ![⟨0,0⟩,⟨(-18),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![17,18,1,1],![17,18,0,1]], true⟩
theorem valid130 : row130.Valid := by decide +kernel
theorem piece130 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (18:ℝ) (780/43:ℝ) ∧
    (∫ x in (18:ℝ)..(780/43:ℝ), innerR 7 6 (3/40) x / x^3) = (557/730080:ℝ) := by
  have h := row_integral row130 valid130
  norm_num [row130] at h ⊢
  exact h

def row131 : Row :=
  ⟨780/43,420/23,(-321),391/20, ![41,18,1,36,33],
   ![⟨0,0⟩,⟨(-18),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![17,18,1,1],![17,18,0,1]], true⟩
theorem valid131 : row131.Valid := by decide +kernel
theorem piece131 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (780/43:ℝ) (420/23:ℝ) ∧
    (∫ x in (780/43:ℝ)..(420/23:ℝ), innerR 7 6 (3/40) x / x^3) = (3481/4968600:ℝ) := by
  have h := row_integral row131 valid131
  norm_num [row131] at h ⊢
  exact h

def row132 : Row :=
  ⟨420/23,55/3,(-300),92/5, ![42,18,1,36,33],
   ![⟨0,0⟩,⟨(-18),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![17,18,1,1],![17,18,0,1]], false⟩
theorem valid132 : row132.Valid := by decide +kernel
theorem piece132 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (420/23:ℝ) (55/3:ℝ) ∧
    (∫ x in (420/23:ℝ)..(55/3:ℝ), innerR 7 6 (3/40) x / x^3) = (1543/3557400:ℝ) := by
  have h := row_integral row132 valid132
  norm_num [row132] at h ⊢
  exact h

def row133 : Row :=
  ⟨55/3,680/37,(-300),92/5, ![42,18,1,36,33],
   ![⟨0,0⟩,⟨(-18),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![17,18,1,1],![17,18,0,1]], false⟩
theorem valid133 : row133.Valid := by decide +kernel
theorem piece133 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (55/3:ℝ) (680/37:ℝ) ∧
    (∫ x in (55/3:ℝ)..(680/37:ℝ), innerR 7 6 (3/40) x / x^3) = (7691/27975200:ℝ) := by
  have h := row_integral row133 valid133
  norm_num [row133] at h ⊢
  exact h

def row134 : Row :=
  ⟨680/37,37/2,(-385),921/40, ![42,18,1,36,34],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-18),1⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![18,18,0,1],![17,18,0,1]], false⟩
theorem valid134 : row134.Valid := by decide +kernel
theorem piece134 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (680/37:ℝ) (37/2:ℝ) ∧
    (∫ x in (680/37:ℝ)..(37/2:ℝ), innerR 7 6 (3/40) x / x^3) = (971577/1266051200:ℝ) := by
  have h := row_integral row134 valid134
  norm_num [row134] at h ⊢
  exact h

def row135 : Row :=
  ⟨37/2,800/43,(-807/2),961/40, ![42,18,1,37,34],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨19,(-1)⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![18,18,0,1],![18,19,0,1]], true⟩
theorem valid135 : row135.Valid := by decide +kernel
theorem piece135 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (37/2:ℝ) (800/43:ℝ) ∧
    (∫ x in (37/2:ℝ)..(800/43:ℝ), innerR 7 6 (3/40) x / x^3) = (2424807/3504640000:ℝ) := by
  have h := row_integral row135 valid135
  norm_num [row135] at h ⊢
  exact h

def row136 : Row :=
  ⟨800/43,430/23,(-687/2),104/5, ![42,18,1,37,34],
   ![⟨0,0⟩,⟨19,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![18,19,1,1],![18,19,0,1]], true⟩
theorem valid136 : row136.Valid := by decide +kernel
theorem piece136 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (800/43:ℝ) (430/23:ℝ) ∧
    (∫ x in (800/43:ℝ)..(430/23:ℝ), innerR 7 6 (3/40) x / x^3) = (2949633/4733440000:ℝ) := by
  have h := row_integral row136 valid136
  norm_num [row136] at h ⊢
  exact h

def row137 : Row :=
  ⟨430/23,700/37,(-322),393/20, ![43,18,1,37,34],
   ![⟨0,0⟩,⟨19,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![18,19,1,1],![18,19,0,1]], false⟩
theorem valid137 : row137.Valid := by decide +kernel
theorem piece137 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (430/23:ℝ) (700/37:ℝ) ∧
    (∫ x in (430/23:ℝ)..(700/37:ℝ), innerR 7 6 (3/40) x / x^3) = (25821/16178750:ℝ) := by
  have h := row_integral row137 valid137
  norm_num [row137] at h ⊢
  exact h

def row138 : Row :=
  ⟨700/37,19,(-357),43/2, ![43,18,1,37,35],
   ![⟨0,0⟩,⟨19,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![18,18,1,1],![18,19,1,1],![18,19,0,1]], false⟩
theorem valid138 : row138.Valid := by decide +kernel
theorem piece138 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (700/37:ℝ) (19:ℝ) ∧
    (∫ x in (700/37:ℝ)..(19:ℝ), innerR 7 6 (3/40) x / x^3) = (30441/50540000:ℝ) := by
  have h := row_integral row138 valid138
  norm_num [row138] at h ⊢
  exact h

def row139 : Row :=
  ⟨19,820/43,(-376),413/20, ![43,19,1,38,35],
   ![⟨0,0⟩,⟨(-19),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![18,19,1,1],![18,19,0,1]], true⟩
theorem valid139 : row139.Valid := by decide +kernel
theorem piece139 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (19:ℝ) (820/43:ℝ) ∧
    (∫ x in (19:ℝ)..(820/43:ℝ), innerR 7 6 (3/40) x / x^3) = (41913/242736400:ℝ) := by
  have h := row_integral row139 valid139
  norm_num [row139] at h ⊢
  exact h

theorem block006 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (620/37:ℝ) (820/43:ℝ) ∧
    (∫ x in (620/37:ℝ)..(820/43:ℝ), innerR 7 6 (3/40) x / x^3) = (12950950551423942019/638203380967536384000:ℝ)
      := by
  have h := piece120
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (390/23:ℝ) (17:ℝ)
    (7043423/2338689600:ℝ) (2333/3516552:ℝ) h piece121
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (17:ℝ) (740/43:ℝ)
    (63691073/17330289600:ℝ) (75411/39564100:ℝ) h piece122
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (740/43:ℝ) (640/37:ℝ)
    (7789078873/1395598027200:ℝ) (464247/560742400:ℝ) h piece123
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (640/37:ℝ) (400/23:ℝ)
    (1672604761/260973772800:ℝ) (1853/2048000:ℝ) h piece124
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (400/23:ℝ) (35/2:ℝ)
    (1192956223/163108608000:ℝ) (337/313600:ℝ) h piece125
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (35/2:ℝ) (760/43:ℝ)
    (67043542567/7992321792000:ℝ) (202107/113209600:ℝ) h piece126
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (760/43:ℝ) (410/23:ℝ)
    (4193365896961/412175452416000:ℝ) (1246551/776756480:ℝ) h piece127
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (410/23:ℝ) (660/37:ℝ)
    (429524832321139/36466680816384000:ℝ) (15373/122040600:ℝ) h piece128
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (660/37:ℝ) (18:ℝ)
    (1281178705463779/107621179970304000:ℝ) (4607/2613600:ℝ) h piece129
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (18:ℝ) (780/43:ℝ)
    (1203449612047121/88053692702976000:ℝ) (557/730080:ℝ) h piece130
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (780/43:ℝ) (420/23:ℝ)
    (611784055871399/42396222412544000:ℝ) (3481/4968600:ℝ) h piece131
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (420/23:ℝ) (55/3:ℝ)
    (1036247971331263/68486205435648000:ℝ) (1543/3557400:ℝ) h piece132
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (55/3:ℝ) (680/37:ℝ)
    (239295668988997/15374454281472000:ℝ) (7691/27975200:ℝ) h piece133
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (680/37:ℝ) (37/2:ℝ)
    (376352870850079/23760520253184000:ℝ) (971577/1266051200:ℝ) h piece134
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (37/2:ℝ) (800/43:ℝ)
    (31775848434587783/1913420719212288000:ℝ) (2424807/3504640000:ℝ) h piece135
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (800/43:ℝ) (430/23:ℝ)
    (8945868936971027/517140734922240000:ℝ) (2949633/4733440000:ℝ) h piece136
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (430/23:ℝ) (700/37:ℝ)
    (1713676142124493343/95619321887122176000:ℝ) (25821/16178750:ℝ) h piece137
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (700/37:ℝ) (19:ℝ)
    (1519067473044840247/77829680605797120000:ℝ) (30441/50540000:ℝ) h piece138
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (620/37:ℝ) (19:ℝ) (820/43:ℝ)
    (5950592736466714001/295752786302029056000:ℝ) (41913/242736400:ℝ) h piece139
  norm_num at h
  exact h

end SplitData
