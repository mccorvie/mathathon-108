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

def row153 : Row :=
  ⟨21,780/37,(-459),421/20, ![48,21,1,42,38],
   ![⟨0,0⟩,⟨(-21),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![20,21,1,1],![20,21,1,2]], true⟩
theorem valid153 : row153.Valid := by decide +kernel
theorem piece153 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (21:ℝ) (780/37:ℝ) ∧
    (∫ x in (21:ℝ)..(780/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(557/3974880:ℝ)) := by
  have h := row_integral row153 valid153
  norm_num [row153] at h ⊢
  exact h

def row154 : Row :=
  ⟨780/37,490/23,(-498),229/10, ![48,21,1,42,39],
   ![⟨0,0⟩,⟨(-21),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![20,21,1,1],![20,21,1,2]], true⟩
theorem valid154 : row154.Valid := by decide +kernel
theorem piece154 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (780/37:ℝ) (490/23:ℝ) ∧
    (∫ x in (780/37:ℝ)..(490/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9671/32461520:ℝ)) := by
  have h := row_integral row154 valid154
  norm_num [row154] at h ⊢
  exact h

def row155 : Row :=
  ⟨490/23,920/43,(-947/2),87/4, ![49,21,1,42,39],
   ![⟨0,0⟩,⟨(-21),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![20,21,1,1],![20,21,1,2]], false⟩
theorem valid155 : row155.Valid := by decide +kernel
theorem piece155 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (490/23:ℝ) (920/43:ℝ) ∧
    (∫ x in (490/23:ℝ)..(920/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(694989/8128825600:ℝ)) := by
  have h := row_integral row155 valid155
  norm_num [row155] at h ⊢
  exact h

def row156 : Row :=
  ⟨920/43,43/2,(-809/2),741/40, ![49,21,1,42,39],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-21),1⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,21,1,2],![20,21,1,2]], false⟩
theorem valid156 : row156.Valid := by decide +kernel
theorem piece156 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (920/43:ℝ) (43/2:ℝ) ∧
    (∫ x in (920/43:ℝ)..(43/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(95409/1251994880:ℝ)) := by
  have h := row_integral row156 valid156
  norm_num [row156] at h ⊢
  exact h

def row157 : Row :=
  ⟨43/2,800/37,(-426),781/40, ![49,21,1,43,39],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨22,(-1)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,21,1,2],![21,22,1,2]], true⟩
theorem valid157 : row157.Valid := by decide +kernel
theorem piece157 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (43/2:ℝ) (800/37:ℝ) ∧
    (∫ x in (43/2:ℝ)..(800/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(72207/1183360000:ℝ)) := by
  have h := row_integral row157 valid157
  norm_num [row157] at h ⊢
  exact h

def row158 : Row :=
  ⟨800/37,65/3,(-526),483/20, ![49,21,1,43,40],
   ![⟨0,0⟩,⟨22,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,22,1,1],![21,22,1,2]], true⟩
theorem valid158 : row158.Valid := by decide +kernel
theorem piece158 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (800/37:ℝ) (65/3:ℝ) ∧
    (∫ x in (800/37:ℝ)..(65/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1583/108160000:ℝ)) := by
  have h := row_integral row158 valid158
  norm_num [row158] at h ⊢
  exact h

def row159 : Row :=
  ⟨65/3,500/23,(-526),483/20, ![49,21,1,43,40],
   ![⟨0,0⟩,⟨22,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,22,1,1],![21,22,1,2]], true⟩
theorem valid159 : row159.Valid := by decide +kernel
theorem piece159 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (65/3:ℝ) (500/23:ℝ) ∧
    (∫ x in (65/3:ℝ)..(500/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(281/21125000:ℝ)) := by
  have h := row_integral row159 valid159
  norm_num [row159] at h ⊢
  exact h

def row160 : Row :=
  ⟨500/23,940/43,(-501),23, ![50,21,1,43,40],
   ![⟨0,0⟩,⟨22,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,22,1,1],![21,22,1,2]], false⟩
theorem valid160 : row160.Valid := by decide +kernel
theorem piece160 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (500/23:ℝ) (940/43:ℝ) ∧
    (∫ x in (500/23:ℝ)..(940/43:ℝ), innerR 7 6 (3/40) x / x^3) = (633/138062500:ℝ) := by
  have h := row_integral row160 valid160
  norm_num [row160] at h ⊢
  exact h

def row161 : Row :=
  ⟨940/43,22,(-501),23, ![50,21,1,43,40],
   ![⟨0,0⟩,⟨22,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![21,21,1,1],![21,22,1,1],![21,22,1,2]], false⟩
theorem valid161 : row161.Valid := by decide +kernel
theorem piece161 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (940/43:ℝ) (22:ℝ) ∧
    (∫ x in (940/43:ℝ)..(22:ℝ), innerR 7 6 (3/40) x / x^3) = (9591/213831200:ℝ) := by
  have h := row_integral row161 valid161
  norm_num [row161] at h ⊢
  exact h

def row162 : Row :=
  ⟨22,820/37,(-523),443/20, ![50,22,1,44,40],
   ![⟨0,0⟩,⟨(-22),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![21,22,1,1],![21,22,1,2]], true⟩
theorem valid162 : row162.Valid := by decide +kernel
theorem piece162 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (22:ℝ) (820/37:ℝ) ∧
    (∫ x in (22:ℝ)..(820/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(16623/32544160:ℝ)) := by
  have h := row_integral row162 valid162
  norm_num [row162] at h ⊢
  exact h

def row163 : Row :=
  ⟨820/37,510/23,(-564),24, ![50,22,1,44,41],
   ![⟨0,0⟩,⟨(-22),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![21,22,1,1],![21,22,1,2]], true⟩
theorem valid163 : row163.Valid := by decide +kernel
theorem piece163 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/37:ℝ) (510/23:ℝ) ∧
    (∫ x in (820/37:ℝ)..(510/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(10051/291485400:ℝ)) := by
  have h := row_integral row163 valid163
  norm_num [row163] at h ⊢
  exact h

def row164 : Row :=
  ⟨510/23,960/43,(-1077/2),457/20, ![51,22,1,44,41],
   ![⟨0,0⟩,⟨(-22),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![21,22,1,1],![21,22,1,2]], false⟩
theorem valid164 : row164.Valid := by decide +kernel
theorem piece164 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (510/23:ℝ) (960/43:ℝ) ∧
    (∫ x in (510/23:ℝ)..(960/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(29437/71024640:ℝ)) := by
  have h := row_integral row164 valid164
  norm_num [row164] at h ⊢
  exact h

def row165 : Row :=
  ⟨960/43,45/2,(-933/2),157/8, ![51,22,1,44,41],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-22),1⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![22,22,1,2],![21,22,1,2]], false⟩
theorem valid165 : row165.Valid := by decide +kernel
theorem piece165 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (960/43:ℝ) (45/2:ℝ) ∧
    (∫ x in (960/43:ℝ)..(45/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(4567/11059200:ℝ)) := by
  have h := row_integral row165 valid165
  norm_num [row165] at h ⊢
  exact h

def row166 : Row :=
  ⟨45/2,520/23,(-489),165/8, ![51,22,1,45,41],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨23,(-1)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![22,22,1,2],![22,23,1,2]], true⟩
theorem valid166 : row166.Valid := by decide +kernel
theorem piece166 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (45/2:ℝ) (520/23:ℝ) ∧
    (∫ x in (45/2:ℝ)..(520/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(659/2920320:ℝ)) := by
  have h := row_integral row166 valid166
  norm_num [row166] at h ⊢
  exact h

def row167 : Row :=
  ⟨520/23,840/37,(-463),779/40, ![52,22,1,45,41],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨23,(-1)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![22,22,1,2],![22,23,1,2]], false⟩
theorem valid167 : row167.Valid := by decide +kernel
theorem piece167 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (520/23:ℝ) (840/37:ℝ) ∧
    (∫ x in (520/23:ℝ)..(840/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(10499/59623200:ℝ)) := by
  have h := row_integral row167 valid167
  norm_num [row167] at h ⊢
  exact h

def row168 : Row :=
  ⟨840/37,980/43,(-568),241/10, ![52,22,1,45,42],
   ![⟨0,0⟩,⟨23,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![22,23,1,1],![22,23,1,2]], false⟩
theorem valid168 : row168.Valid := by decide +kernel
theorem piece168 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (840/37:ℝ) (980/43:ℝ) ∧
    (∫ x in (840/37:ℝ)..(980/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(16/108045:ℝ)) := by
  have h := row_integral row168 valid168
  norm_num [row168] at h ⊢
  exact h

def row169 : Row :=
  ⟨980/43,23,(-568),241/10, ![52,22,1,45,42],
   ![⟨0,0⟩,⟨23,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![22,22,1,1],![22,23,1,1],![22,23,1,2]], false⟩
theorem valid169 : row169.Valid := by decide +kernel
theorem piece169 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (980/43:ℝ) (23:ℝ) ∧
    (∫ x in (980/43:ℝ)..(23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(71919/254025800:ℝ)) := by
  have h := row_integral row169 valid169
  norm_num [row169] at h ⊢
  exact h

def row170 : Row :=
  ⟨23,530/23,(-591),93/4, ![52,23,1,46,42],
   ![⟨0,0⟩,⟨(-23),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![22,23,1,1],![22,23,1,2]], true⟩
theorem valid170 : row170.Valid := by decide +kernel
theorem piece170 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (23:ℝ) (530/23:ℝ) ∧
    (∫ x in (23:ℝ)..(530/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(29517/148596100:ℝ)) := by
  have h := row_integral row170 valid170
  norm_num [row170] at h ⊢
  exact h

def row171 : Row :=
  ⟨530/23,860/37,(-1129/2),221/10, ![53,23,1,46,42],
   ![⟨0,0⟩,⟨(-23),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![22,23,1,1],![22,23,1,2]], false⟩
theorem valid171 : row171.Valid := by decide +kernel
theorem piece171 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (530/23:ℝ) (860/37:ℝ) ∧
    (∫ x in (530/23:ℝ)..(860/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(7103603/8310145600:ℝ)) := by
  have h := row_integral row171 valid171
  norm_num [row171] at h ⊢
  exact h

def row172 : Row :=
  ⟨860/37,1000/43,(-1215/2),479/20, ![53,23,1,46,43],
   ![⟨0,0⟩,⟨(-23),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![22,23,1,1],![22,23,1,2]], false⟩
theorem valid172 : row172.Valid := by decide +kernel
theorem piece172 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (860/37:ℝ) (1000/43:ℝ) ∧
    (∫ x in (860/37:ℝ)..(1000/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(74977/1479200000:ℝ)) := by
  have h := row_integral row172 valid172
  norm_num [row172] at h ⊢
  exact h

theorem block000 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (21:ℝ) (1000/43:ℝ) ∧
    (∫ x in (21:ℝ)..(1000/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1265884887087383/320554374940800000:ℝ)) := by
  have h := piece153
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (780/37:ℝ) (490/23:ℝ)
    (-(557/3974880:ℝ)) (-(9671/32461520:ℝ)) h piece154
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (490/23:ℝ) (920/43:ℝ)
    (-(6563/14982240:ℝ)) (-(694989/8128825600:ℝ)) h piece155
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (920/43:ℝ) (43/2:ℝ)
    (-(3387299/6469881600:ℝ)) (-(95409/1251994880:ℝ)) h piece156
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (43/2:ℝ) (800/37:ℝ)
    (-(155972801/260061110400:ℝ)) (-(72207/1183360000:ℝ)) h piece157
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (800/37:ℝ) (65/3:ℝ)
    (-(799262197/1209586560000:ℝ)) (-(1583/108160000:ℝ)) h piece158
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (65/3:ℝ) (500/23:ℝ)
    (-(212410997/314492505600:ℝ)) (-(281/21125000:ℝ)) h piece159
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (500/23:ℝ) (940/43:ℝ)
    (-(10413187769/15119832000000:ℝ)) (633/138062500:ℝ) h piece160
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (940/43:ℝ) (22:ℝ)
    (-(913983924929/1335988355520000:ℝ)) (9591/213831200:ℝ) h piece161
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (22:ℝ) (820/37:ℝ)
    (-(46781955401/73179986880000:ℝ)) (-(16623/32544160:ℝ)) h piece162
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (820/37:ℝ) (510/23:ℝ)
    (-(12861337169371/11183232540480000:ℝ)) (-(10051/291485400:ℝ)) h piece163
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (510/23:ℝ) (960/43:ℝ)
    (-(93374894918659/78828151321920000:ℝ)) (-(29437/71024640:ℝ)) h piece164
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (960/43:ℝ) (45/2:ℝ)
    (-(79087781805313/49460800829440000:ℝ)) (-(4567/11059200:ℝ)) h piece165
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (45/2:ℝ) (520/23:ℝ)
    (-(167928325489711/83465101399680000:ℝ)) (-(659/2920320:ℝ)) h piece166
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (520/23:ℝ) (840/37:ℝ)
    (-(809306667433081/361682106065280000:ℝ)) (-(10499/59623200:ℝ)) h piece167
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (840/37:ℝ) (980/43:ℝ)
    (-(67153459269437/27821700466560000:ℝ)) (-(16/108045:ℝ)) h piece168
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (980/43:ℝ) (23:ℝ)
    (-(3492400323914413/1363263322861440000:ℝ)) (-(71919/254025800:ℝ)) h piece169
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (23:ℝ) (530/23:ℝ)
    (-(1820456208019451/639899110730880000:ℝ)) (-(29517/148596100:ℝ)) h piece170
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (530/23:ℝ) (860/37:ℝ)
    (-(10341608084016371/3397876374372480000:ℝ)) (-(7103603/8310145600:ℝ)) h piece171
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (21:ℝ) (860/37:ℝ) (1000/43:ℝ)
    (-(10746876276800701/2756767624490880000:ℝ)) (-(74977/1479200000:ℝ)) h piece172
  norm_num at h
  exact h

end U66Data
