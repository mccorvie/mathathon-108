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

def row100 : Row :=
  ⟨29/2,540/37,(-223),837/40, ![33,14,1,29,26],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨15,(-1)⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![14,15,0,1]], true⟩
theorem valid100 : row100.Valid := by decide +kernel
theorem piece100 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (29/2:ℝ) (540/37:ℝ) ∧
    (∫ x in (29/2:ℝ)..(540/37:ℝ), innerR 7 6 (3/40) x / x^3) = (306691/122617800:ℝ) := by
  have h := row_integral row100 valid100
  norm_num [row100] at h ⊢
  exact h

def row101 : Row :=
  ⟨540/37,340/23,(-250),911/40, ![33,14,1,29,27],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨15,(-1)⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![14,15,0,1]], true⟩
theorem valid101 : row101.Valid := by decide +kernel
theorem piece101 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (540/37:ℝ) (340/23:ℝ) ∧
    (∫ x in (540/37:ℝ)..(340/23:ℝ), innerR 7 6 (3/40) x / x^3) = (105649/21068100:ℝ) := by
  have h := row_integral row101 valid101
  norm_num [row101] at h ⊢
  exact h

def row102 : Row :=
  ⟨340/23,640/43,(-233),173/8, ![34,14,1,29,27],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨15,(-1)⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![14,15,0,1]], false⟩
theorem valid102 : row102.Valid := by decide +kernel
theorem piece102 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (340/23:ℝ) (640/43:ℝ) ∧
    (∫ x in (340/23:ℝ)..(640/43:ℝ), innerR 7 6 (3/40) x / x^3) = (128749/47349760:ℝ) := by
  have h := row_integral row102 valid102
  norm_num [row102] at h ⊢
  exact h

def row103 : Row :=
  ⟨640/43,15,(-185),92/5, ![34,14,1,29,27],
   ![⟨0,0⟩,⟨15,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,15,1,1],![14,15,0,1]], false⟩
theorem valid103 : row103.Valid := by decide +kernel
theorem piece103 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (640/43:ℝ) (15:ℝ) ∧
    (∫ x in (640/43:ℝ)..(15:ℝ), innerR 7 6 (3/40) x / x^3) = (23111/7372800:ℝ) := by
  have h := row_integral row103 valid103
  norm_num [row103] at h ⊢
  exact h

def row104 : Row :=
  ⟨15,560/37,(-200),351/20, ![34,15,1,30,27],
   ![⟨0,0⟩,⟨(-15),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![14,15,1,1],![14,15,0,1]], true⟩
theorem valid104 : row104.Valid := by decide +kernel
theorem piece104 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (15:ℝ) (560/37:ℝ) ∧
    (∫ x in (15:ℝ)..(560/37:ℝ), innerR 7 6 (3/40) x / x^3) = (449/176400:ℝ) := by
  have h := row_integral row104 valid104
  norm_num [row104] at h ⊢
  exact h

def row105 : Row :=
  ⟨560/37,350/23,(-270),887/40, ![34,15,1,30,28],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-15),1⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![14,15,0,1]], true⟩
theorem valid105 : row105.Valid := by decide +kernel
theorem piece105 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (560/37:ℝ) (350/23:ℝ) ∧
    (∫ x in (560/37:ℝ)..(350/23:ℝ), innerR 7 6 (3/40) x / x^3) = (491/313600:ℝ) := by
  have h := row_integral row105 valid105
  norm_num [row105] at h ⊢
  exact h

def row106 : Row :=
  ⟨350/23,660/43,(-505/2),841/40, ![35,15,1,30,28],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-15),1⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![14,15,0,1]], false⟩
theorem valid106 : row106.Valid := by decide +kernel
theorem piece106 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (350/23:ℝ) (660/43:ℝ) ∧
    (∫ x in (350/23:ℝ)..(660/43:ℝ), innerR 7 6 (3/40) x / x^3) = (1081847/426888000:ℝ) := by
  have h := row_integral row106 valid106
  norm_num [row106] at h ⊢
  exact h

def row107 : Row :=
  ⟨660/43,31/2,(-505/2),841/40, ![35,15,1,30,28],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-15),1⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![14,15,0,1]], false⟩
theorem valid107 : row107.Valid := by decide +kernel
theorem piece107 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (660/43:ℝ) (31/2:ℝ) ∧
    (∫ x in (660/43:ℝ)..(31/2:ℝ), innerR 7 6 (3/40) x / x^3) = (4951973/1674446400:ℝ) := by
  have h := row_integral row107 valid107
  norm_num [row107] at h ⊢
  exact h

def row108 : Row :=
  ⟨31/2,360/23,(-268),881/40, ![35,15,1,31,28],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨16,(-1)⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![15,16,0,1]], true⟩
theorem valid108 : row108.Valid := by decide +kernel
theorem piece108 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (31/2:ℝ) (360/23:ℝ) ∧
    (∫ x in (31/2:ℝ)..(360/23:ℝ), innerR 7 6 (3/40) x / x^3) = (376439/124545600:ℝ) := by
  have h := row_integral row108 valid108
  norm_num [row108] at h ⊢
  exact h

def row109 : Row :=
  ⟨360/23,580/37,(-250),167/8, ![36,15,1,31,28],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨16,(-1)⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![15,16,0,1]], false⟩
theorem valid109 : row109.Valid := by decide +kernel
theorem piece109 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (360/23:ℝ) (580/37:ℝ) ∧
    (∫ x in (360/23:ℝ)..(580/37:ℝ), innerR 7 6 (3/40) x / x^3) = (5131/10899360:ℝ) := by
  have h := row_integral row109 valid109
  norm_num [row109] at h ⊢
  exact h

def row110 : Row :=
  ⟨580/37,680/43,(-279),909/40, ![36,15,1,31,29],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨16,(-1)⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,15,0,1],![15,16,0,1]], false⟩
theorem valid110 : row110.Valid := by decide +kernel
theorem piece110 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (580/37:ℝ) (680/43:ℝ) ∧
    (∫ x in (580/37:ℝ)..(680/43:ℝ), innerR 7 6 (3/40) x / x^3) = (2171169/777756800:ℝ) := by
  have h := row_integral row110 valid110
  norm_num [row110] at h ⊢
  exact h

def row111 : Row :=
  ⟨680/43,16,(-228),39/2, ![36,15,1,31,29],
   ![⟨0,0⟩,⟨16,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![15,15,1,1],![15,16,1,1],![15,16,0,1]], false⟩
theorem valid111 : row111.Valid := by decide +kernel
theorem piece111 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (680/43:ℝ) (16:ℝ) ∧
    (∫ x in (680/43:ℝ)..(16:ℝ), innerR 7 6 (3/40) x / x^3) = (3513/924800:ℝ) := by
  have h := row_integral row111 valid111
  norm_num [row111] at h ⊢
  exact h

def row112 : Row :=
  ⟨16,370/23,(-244),373/20, ![36,16,1,32,29],
   ![⟨0,0⟩,⟨(-16),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![15,16,1,1],![15,16,0,1]], true⟩
theorem valid112 : row112.Valid := by decide +kernel
theorem piece112 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (16:ℝ) (370/23:ℝ) ∧
    (∫ x in (16:ℝ)..(370/23:ℝ), innerR 7 6 (3/40) x / x^3) = (5093/4380800:ℝ) := by
  have h := row_integral row112 valid112
  norm_num [row112] at h ⊢
  exact h

def row113 : Row :=
  ⟨370/23,600/37,(-451/2),35/2, ![37,16,1,32,29],
   ![⟨0,0⟩,⟨(-16),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![15,16,1,1],![15,16,0,1]], false⟩
theorem valid113 : row113.Valid := by decide +kernel
theorem piece113 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (370/23:ℝ) (600/37:ℝ) ∧
    (∫ x in (370/23:ℝ)..(600/37:ℝ), innerR 7 6 (3/40) x / x^3) = (3456211/1971360000:ℝ) := by
  have h := row_integral row113 valid113
  norm_num [row113] at h ⊢
  exact h

def row114 : Row :=
  ⟨600/37,700/43,(-601/2),177/8, ![37,16,1,32,30],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-16),1⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,16,0,1],![15,16,0,1]], false⟩
theorem valid114 : row114.Valid := by decide +kernel
theorem piece114 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (600/37:ℝ) (700/43:ℝ) ∧
    (∫ x in (600/37:ℝ)..(700/43:ℝ), innerR 7 6 (3/40) x / x^3) = (60983/70560000:ℝ) := by
  have h := row_integral row114 valid114
  norm_num [row114] at h ⊢
  exact h

def row115 : Row :=
  ⟨700/43,33/2,(-601/2),177/8, ![37,16,1,32,30],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-16),1⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,16,0,1],![15,16,0,1]], false⟩
theorem valid115 : row115.Valid := by decide +kernel
theorem piece115 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (700/43:ℝ) (33/2:ℝ) ∧
    (∫ x in (700/43:ℝ)..(33/2:ℝ), innerR 7 6 (3/40) x / x^3) = (6652489/2134440000:ℝ) := by
  have h := row_integral row115 valid115
  norm_num [row115] at h ⊢
  exact h

def row116 : Row :=
  ⟨33/2,380/23,(-317),185/8, ![37,16,1,33,30],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨17,(-1)⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,16,0,1],![16,17,0,1]], true⟩
theorem valid116 : row116.Valid := by decide +kernel
theorem piece116 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (33/2:ℝ) (380/23:ℝ) ∧
    (∫ x in (33/2:ℝ)..(380/23:ℝ), innerR 7 6 (3/40) x / x^3) = (24613/78625800:ℝ) := by
  have h := row_integral row116 valid116
  norm_num [row116] at h ⊢
  exact h

def row117 : Row :=
  ⟨380/23,50/3,(-298),879/40, ![38,16,1,33,30],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨17,(-1)⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,16,0,1],![16,17,0,1]], false⟩
theorem valid117 : row117.Valid := by decide +kernel
theorem piece117 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (380/23:ℝ) (50/3:ℝ) ∧
    (∫ x in (380/23:ℝ)..(50/3:ℝ), innerR 7 6 (3/40) x / x^3) = (15263/7220000:ℝ) := by
  have h := row_integral row117 valid117
  norm_num [row117] at h ⊢
  exact h

def row118 : Row :=
  ⟨50/3,720/43,(-591/2),873/40, ![38,16,1,33,30],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨17,(-1)⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,16,0,1],![16,17,0,1]], true⟩
theorem valid118 : row118.Valid := by decide +kernel
theorem piece118 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (50/3:ℝ) (720/43:ℝ) ∧
    (∫ x in (50/3:ℝ)..(720/43:ℝ), innerR 7 6 (3/40) x / x^3) = (19853/17280000:ℝ) := by
  have h := row_integral row118 valid118
  norm_num [row118] at h ⊢
  exact h

def row119 : Row :=
  ⟨720/43,620/37,(-483/2),93/5, ![38,16,1,33,30],
   ![⟨0,0⟩,⟨17,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![16,16,1,1],![16,17,1,1],![16,17,0,1]], true⟩
theorem valid119 : row119.Valid := by decide +kernel
theorem piece119 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (720/43:ℝ) (620/37:ℝ) ∧
    (∫ x in (720/43:ℝ)..(620/37:ℝ), innerR 7 6 (3/40) x / x^3) = (124471/664243200:ℝ) := by
  have h := row_integral row119 valid119
  norm_num [row119] at h ⊢
  exact h

theorem block005 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (29/2:ℝ) (620/37:ℝ) ∧
    (∫ x in (29/2:ℝ)..(620/37:ℝ), innerR 7 6 (3/40) x / x^3) = (224727991002371393/5140650573805824000:ℝ) := by
  have h := piece100
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (540/37:ℝ) (340/23:ℝ)
    (306691/122617800:ℝ) (105649/21068100:ℝ) h piece101
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (340/23:ℝ) (640/43:ℝ)
    (9864271/1312464600:ℝ) (128749/47349760:ℝ) h piece102
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (640/43:ℝ) (15:ℝ)
    (3236563043/316226764800:ℝ) (23111/7372800:ℝ) h piece103
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (15:ℝ) (560/37:ℝ)
    (264238559/19764172800:ℝ) (449/176400:ℝ) h piece104
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (560/37:ℝ) (350/23:ℝ)
    (15412720943/968444467200:ℝ) (491/313600:ℝ) h piece105
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (350/23:ℝ) (660/43:ℝ)
    (677160143/38737778688:ℝ) (1081847/426888000:ℝ) h piece106
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (660/43:ℝ) (31/2:ℝ)
    (1675270736077/83701271808000:ℝ) (4951973/1674446400:ℝ) h piece107
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (31/2:ℝ) (360/23:ℝ)
    (15271220332117/664767952128000:ℝ) (376439/124545600:ℝ) h piece108
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (360/23:ℝ) (580/37:ℝ)
    (1672304618881/64332382464000:ℝ) (5131/10899360:ℝ) h piece109
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (580/37:ℝ) (680/43:ℝ)
    (567529944427/21444127488000:ℝ) (2171169/777756800:ℝ) h piece110
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (680/43:ℝ) (16:ℝ)
    (10665679388939/364550167296000:ℝ) (3513/924800:ℝ) h piece111
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (16:ℝ) (370/23:ℝ)
    (708851836747/21444127488000:ℝ) (5093/4380800:ℝ) h piece112
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (370/23:ℝ) (600/37:ℝ)
    (1004547833661763/29357010531072000:ℝ) (3456211/1971360000:ℝ) h piece113
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (600/37:ℝ) (700/43:ℝ)
    (142704984026123/3967163585280000:ℝ) (60983/70560000:ℝ) h piece114
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (700/43:ℝ) (33/2:ℝ)
    (1022935834305989/27770145096960000:ℝ) (6652489/2134440000:ℝ) h piece115
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (33/2:ℝ) (380/23:ℝ)
    (3835658806222879/96005358763776000:ℝ) (24613/78625800:ℝ) h piece116
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (380/23:ℝ) (50/3:ℝ)
    (126865649078208389/3150721319429376000:ℝ) (15263/7220000:ℝ) h piece117
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (50/3:ℝ) (720/43:ℝ)
    (35138483956958563/829137189323520000:ℝ) (19853/17280000:ℝ) h piece118
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (29/2:ℝ) (720/43:ℝ) (620/37:ℝ)
    (7218216011526433/165827437864704000:ℝ) (124471/664243200:ℝ) h piece119
  norm_num at h
  exact h

end SplitData
