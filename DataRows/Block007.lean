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

def row140 : Row :=
  ⟨820/43,440/23,(-376),413/20, ![43,19,1,38,35],
   ![⟨0,0⟩,⟨(-19),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![18,19,1,1],![18,19,0,1]], true⟩
theorem valid140 : row140.Valid := by decide +kernel
theorem piece140 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/43:ℝ) (440/23:ℝ) ∧
    (∫ x in (820/43:ℝ)..(440/23:ℝ), innerR 7 6 (3/40) x / x^3) = (26091/162720800:ℝ) := by
  have h := row_integral row140 valid140
  norm_num [row140] at h ⊢
  exact h

def row141 : Row :=
  ⟨440/23,720/37,(-354),39/2, ![44,19,1,38,35],
   ![⟨0,0⟩,⟨(-19),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![18,19,1,1],![18,19,0,1]], false⟩
theorem valid141 : row141.Valid := by decide +kernel
theorem piece141 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (440/23:ℝ) (720/37:ℝ) ∧
    (∫ x in (440/23:ℝ)..(720/37:ℝ), innerR 7 6 (3/40) x / x^3) = (21287/20908800:ℝ) := by
  have h := row_integral row141 valid141
  norm_num [row141] at h ⊢
  exact h

def row142 : Row :=
  ⟨720/37,39/2,(-444),193/8, ![44,19,1,38,36],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-19),1⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![19,19,0,1],![18,19,0,1]], false⟩
theorem valid142 : row142.Valid := by decide +kernel
theorem piece142 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (720/37:ℝ) (39/2:ℝ) ∧
    (∫ x in (720/37:ℝ)..(39/2:ℝ), innerR 7 6 (3/40) x / x^3) = (1039/7300800:ℝ) := by
  have h := row_integral row142 valid142
  norm_num [row142] at h ⊢
  exact h

def row143 : Row :=
  ⟨39/2,840/43,(-927/2),201/8, ![44,19,1,39,36],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨20,(-1)⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![19,19,0,1],![19,20,0,1]], true⟩
theorem valid143 : row143.Valid := by decide +kernel
theorem piece143 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (39/2:ℝ) (840/43:ℝ) ∧
    (∫ x in (39/2:ℝ)..(840/43:ℝ), innerR 7 6 (3/40) x / x^3) = (6683/52998400:ℝ) := by
  have h := row_integral row143 valid143
  norm_num [row143] at h ⊢
  exact h

def row144 : Row :=
  ⟨840/43,450/23,(-801/2),219/10, ![44,19,1,39,36],
   ![⟨0,0⟩,⟨20,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![19,20,1,1],![19,20,0,1]], true⟩
theorem valid144 : row144.Valid := by decide +kernel
theorem piece144 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (840/43:ℝ) (450/23:ℝ) ∧
    (∫ x in (840/43:ℝ)..(450/23:ℝ), innerR 7 6 (3/40) x / x^3) = (7919/70560000:ℝ) := by
  have h := row_integral row144 valid144
  norm_num [row144] at h ⊢
  exact h

def row145 : Row :=
  ⟨450/23,20,(-378),83/4, ![45,19,1,39,36],
   ![⟨0,0⟩,⟨20,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![19,19,1,1],![19,20,1,1],![19,20,0,1]], false⟩
theorem valid145 : row145.Valid := by decide +kernel
theorem piece145 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (450/23:ℝ) (20:ℝ) ∧
    (∫ x in (450/23:ℝ)..(20:ℝ), innerR 7 6 (3/40) x / x^3) = (41/22500:ℝ) := by
  have h := row_integral row145 valid145
  norm_num [row145] at h ⊢
  exact h

def row146 : Row :=
  ⟨20,470/23,(-436),109/5, ![46,20,1,40,37],
   ![⟨0,0⟩,⟨(-20),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![19,20,1,1],![19,20,1,2]], true⟩
theorem valid146 : row146.Valid := by decide +kernel
theorem piece146 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (20:ℝ) (470/23:ℝ) ∧
    (∫ x in (20:ℝ)..(470/23:ℝ), innerR 7 6 (3/40) x / x^3) = (109/441800:ℝ) := by
  have h := row_integral row146 valid146
  norm_num [row146] at h ⊢
  exact h

def row147 : Row :=
  ⟨470/23,880/43,(-825/2),413/20, ![47,20,1,40,37],
   ![⟨0,0⟩,⟨(-20),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![19,20,1,1],![19,20,1,2]], false⟩
theorem valid147 : row147.Valid := by decide +kernel
theorem piece147 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (470/23:ℝ) (880/43:ℝ) ∧
    (∫ x in (470/23:ℝ)..(880/43:ℝ), innerR 7 6 (3/40) x / x^3) = (21603/622054400:ℝ) := by
  have h := row_integral row147 valid147
  norm_num [row147] at h ⊢
  exact h

def row148 : Row :=
  ⟨880/43,41/2,(-693/2),697/40, ![47,20,1,40,37],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-20),1⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![20,20,1,2],![19,20,1,2]], false⟩
theorem valid148 : row148.Valid := by decide +kernel
theorem piece148 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (880/43:ℝ) (41/2:ℝ) ∧
    (∫ x in (880/43:ℝ)..(41/2:ℝ), innerR 7 6 (3/40) x / x^3) = (20001/473369600:ℝ) := by
  have h := row_integral row148 valid148
  norm_num [row148] at h ⊢
  exact h

def row149 : Row :=
  ⟨41/2,760/37,(-367),737/40, ![47,20,1,41,37],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨21,(-1)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![20,20,1,2],![20,21,1,2]], true⟩
theorem valid149 : row149.Valid := by decide +kernel
theorem piece149 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (41/2:ℝ) (760/37:ℝ) ∧
    (∫ x in (41/2:ℝ)..(760/37:ℝ), innerR 7 6 (3/40) x / x^3) = (101001/1941891200:ℝ) := by
  have h := row_integral row149 valid149
  norm_num [row149] at h ⊢
  exact h

def row150 : Row :=
  ⟨760/37,480/23,(-462),461/20, ![47,20,1,41,38],
   ![⟨0,0⟩,⟨21,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![20,21,1,1],![20,21,1,2]], true⟩
theorem valid150 : row150.Valid := by decide +kernel
theorem piece150 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (760/37:ℝ) (480/23:ℝ) ∧
    (∫ x in (760/37:ℝ)..(480/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1043/1848320:ℝ) := by
  have h := row_integral row150 valid150
  norm_num [row150] at h ⊢
  exact h

def row151 : Row :=
  ⟨480/23,900/43,(-438),219/10, ![48,20,1,41,38],
   ![⟨0,0⟩,⟨21,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![20,21,1,1],![20,21,1,2]], false⟩
theorem valid151 : row151.Valid := by decide +kernel
theorem piece151 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (480/23:ℝ) (900/43:ℝ) ∧
    (∫ x in (480/23:ℝ)..(900/43:ℝ), innerR 7 6 (3/40) x / x^3) = (2263/17280000:ℝ) := by
  have h := row_integral row151 valid151
  norm_num [row151] at h ⊢
  exact h

def row152 : Row :=
  ⟨900/43,21,(-438),219/10, ![48,20,1,41,38],
   ![⟨0,0⟩,⟨21,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![20,20,1,1],![20,21,1,1],![20,21,1,2]], false⟩
theorem valid152 : row152.Valid := by decide +kernel
theorem piece152 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (900/43:ℝ) (21:ℝ) ∧
    (∫ x in (900/43:ℝ)..(21:ℝ), innerR 7 6 (3/40) x / x^3) = (2117/13230000:ℝ) := by
  have h := row_integral row152 valid152
  norm_num [row152] at h ⊢
  exact h

theorem block007 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (820/43:ℝ) (21:ℝ) ∧
    (∫ x in (820/43:ℝ)..(21:ℝ), innerR 7 6 (3/40) x / x^3) = (1552446518659/336590045792000:ℝ) := by
  have h := piece140
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (440/23:ℝ) (720/37:ℝ)
    (26091/162720800:ℝ) (21287/20908800:ℝ) h piece141
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (720/37:ℝ) (39/2:ℝ)
    (3765373/3195244800:ℝ) (1039/7300800:ℝ) h piece142
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (39/2:ℝ) (840/43:ℝ)
    (237732211/179998790400:ℝ) (6683/52998400:ℝ) h piece143
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (840/43:ℝ) (450/23:ℝ)
    (245404933/169614244800:ℝ) (7919/70560000:ℝ) h piece144
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (450/23:ℝ) (20:ℝ)
    (3777726611/2423060640000:ℝ) (41/22500:ℝ) h piece145
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (20:ℝ) (470/23:ℝ)
    (182068479/53845792000:ℝ) (109/441800:ℝ) h piece146
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (470/23:ℝ) (880/43:ℝ)
    (431535226751/118945354528000:ℝ) (21603/622054400:ℝ) h piece147
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (880/43:ℝ) (41/2:ℝ)
    (37077958927/10123008896000:ℝ) (20001/473369600:ℝ) h piece148
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (41/2:ℝ) (760/37:ℝ)
    (4688210039/1265376112000:ℝ) (101001/1941891200:ℝ) h piece149
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (760/37:ℝ) (480/23:ℝ)
    (858101397157/228400388216000:ℝ) (1043/1848320:ℝ) h piece150
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (480/23:ℝ) (900/43:ℝ)
    (831146841423/192337169024000:ℝ) (2263/17280000:ℝ) h piece151
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (820/43:ℝ) (900/43:ℝ) (21:ℝ)
    (28901321158771/6491379454560000:ℝ) (2117/13230000:ℝ) h piece152
  norm_num at h
  exact h

end SplitData
