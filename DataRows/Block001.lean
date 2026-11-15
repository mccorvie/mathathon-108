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

def row020 : Row :=
  ⟨120/23,200/37,(-18),26/5, ![12,5,0,10,9],
   ![⟨0,0⟩,⟨(-5),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![4,5,0,0],![4,5,-1,0]], false⟩
theorem valid020 : row020.Valid := by decide +kernel
theorem piece020 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (120/23:ℝ) (200/37:ℝ) ∧
    (∫ x in (120/23:ℝ)..(200/37:ℝ), innerR 7 6 (3/40) x / x^3) = (181/15000:ℝ) := by
  have h := row_integral row020 valid020
  norm_num [row020] at h ⊢
  exact h

def row021 : Row :=
  ⟨200/37,11/2,(-43),393/40, ![12,5,0,10,10],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-5),1⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![5,5,-1,0],![4,5,-1,0]], false⟩
theorem valid021 : row021.Valid := by decide +kernel
theorem piece021 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (200/37:ℝ) (11/2:ℝ) ∧
    (∫ x in (200/37:ℝ)..(11/2:ℝ), innerR 7 6 (3/40) x / x^3) = (59703/9680000:ℝ) := by
  have h := row_integral row021 valid021
  norm_num [row021] at h ⊢
  exact h

def row022 : Row :=
  ⟨11/2,240/43,(-97/2),433/40, ![12,5,0,11,10],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨6,(-1)⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![5,5,-1,0],![5,6,-1,0]], true⟩
theorem valid022 : row022.Valid := by decide +kernel
theorem piece022 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (11/2:ℝ) (240/43:ℝ) ∧
    (∫ x in (11/2:ℝ)..(240/43:ℝ), innerR 7 6 (3/40) x / x^3) = (153097/27878400:ℝ) := by
  have h := row_integral row022 valid022
  norm_num [row022] at h ⊢
  exact h

def row023 : Row :=
  ⟨240/43,130/23,(-61/2),38/5, ![12,5,0,11,10],
   ![⟨0,0⟩,⟨6,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![5,6,0,0],![5,6,-1,0]], true⟩
theorem valid023 : row023.Valid := by decide +kernel
theorem piece023 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (240/43:ℝ) (130/23:ℝ) ∧
    (∫ x in (240/43:ℝ)..(130/23:ℝ), innerR 7 6 (3/40) x / x^3) = (189539/38937600:ℝ) := by
  have h := row_integral row023 valid023
  norm_num [row023] at h ⊢
  exact h

def row024 : Row :=
  ⟨130/23,220/37,(-24),129/20, ![13,5,0,11,10],
   ![⟨0,0⟩,⟨6,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![5,6,0,0],![5,6,-1,0]], false⟩
theorem valid024 : row024.Valid := by decide +kernel
theorem piece024 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (130/23:ℝ) (220/37:ℝ) ∧
    (∫ x in (130/23:ℝ)..(220/37:ℝ), innerR 7 6 (3/40) x / x^3) = (6603/327184:ℝ) := by
  have h := row_integral row024 valid024
  norm_num [row024] at h ⊢
  exact h

def row025 : Row :=
  ⟨220/37,6,(-35),83/10, ![13,5,0,11,11],
   ![⟨0,0⟩,⟨6,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![5,6,0,0],![5,6,-1,0]], false⟩
theorem valid025 : row025.Valid := by decide +kernel
theorem piece025 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (220/37:ℝ) (6:ℝ) ∧
    (∫ x in (220/37:ℝ)..(6:ℝ), innerR 7 6 (3/40) x / x^3) = (3221/871200:ℝ) := by
  have h := row_integral row025 valid025
  norm_num [row025] at h ⊢
  exact h

def row026 : Row :=
  ⟨6,260/43,(-41),149/20, ![13,6,0,12,11],
   ![⟨0,0⟩,⟨(-6),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![5,6,0,0],![5,6,-1,0]], true⟩
theorem valid026 : row026.Valid := by decide +kernel
theorem piece026 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (6:ℝ) (260/43:ℝ) ∧
    (∫ x in (6:ℝ)..(260/43:ℝ), innerR 7 6 (3/40) x / x^3) = (1003/1216800:ℝ) := by
  have h := row_integral row026 valid026
  norm_num [row026] at h ⊢
  exact h

def row027 : Row :=
  ⟨260/43,140/23,(-41),149/20, ![13,6,0,12,11],
   ![⟨0,0⟩,⟨(-6),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![5,6,0,0],![5,6,-1,0]], true⟩
theorem valid027 : row027.Valid := by decide +kernel
theorem piece027 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (260/43:ℝ) (140/23:ℝ) ∧
    (∫ x in (260/43:ℝ)..(140/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1259/1656200:ℝ) := by
  have h := row_integral row027 valid027
  norm_num [row027] at h ⊢
  exact h

def row028 : Row :=
  ⟨140/23,240/37,(-34),63/10, ![14,6,0,12,11],
   ![⟨0,0⟩,⟨(-6),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![5,6,0,0],![5,6,-1,0]], false⟩
theorem valid028 : row028.Valid := by decide +kernel
theorem piece028 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (140/23:ℝ) (240/37:ℝ) ∧
    (∫ x in (140/23:ℝ)..(240/37:ℝ), innerR 7 6 (3/40) x / x^3) = (25313/2822400:ℝ) := by
  have h := row_integral row028 valid028
  norm_num [row028] at h ⊢
  exact h

def row029 : Row :=
  ⟨240/37,13/2,(-64),437/40, ![14,6,0,12,12],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-6),1⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,6,-1,0],![5,6,-1,0]], false⟩
theorem valid029 : row029.Valid := by decide +kernel
theorem piece029 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (240/37:ℝ) (13/2:ℝ) ∧
    (∫ x in (240/37:ℝ)..(13/2:ℝ), innerR 7 6 (3/40) x / x^3) = (1667/4867200:ℝ) := by
  have h := row_integral row029 valid029
  norm_num [row029] at h ⊢
  exact h

def row030 : Row :=
  ⟨13/2,280/43,(-141/2),477/40, ![14,6,0,13,12],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨7,(-1)⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,6,-1,0],![6,7,-1,0]], true⟩
theorem valid030 : row030.Valid := by decide +kernel
theorem piece030 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (13/2:ℝ) (280/43:ℝ) ∧
    (∫ x in (13/2:ℝ)..(280/43:ℝ), innerR 7 6 (3/40) x / x^3) = (15849/52998400:ℝ) := by
  have h := row_integral row030 valid030
  norm_num [row030] at h ⊢
  exact h

def row031 : Row :=
  ⟨280/43,150/23,(-99/2),87/10, ![14,6,0,13,12],
   ![⟨0,0⟩,⟨7,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,7,0,0],![6,7,-1,0]], true⟩
theorem valid031 : row031.Valid := by decide +kernel
theorem piece031 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (280/43:ℝ) (150/23:ℝ) ∧
    (∫ x in (280/43:ℝ)..(150/23:ℝ), innerR 7 6 (3/40) x / x^3) = (2061/7840000:ℝ) := by
  have h := row_integral row031 valid031
  norm_num [row031] at h ⊢
  exact h

def row032 : Row :=
  ⟨150/23,20/3,(-42),151/20, ![15,6,0,13,12],
   ![⟨0,0⟩,⟨7,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,7,0,0],![6,7,-1,0]], false⟩
theorem valid032 : row032.Valid := by decide +kernel
theorem piece032 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (150/23:ℝ) (20/3:ℝ) ∧
    (∫ x in (150/23:ℝ)..(20/3:ℝ), innerR 7 6 (3/40) x / x^3) = (59/15000:ℝ) := by
  have h := row_integral row032 valid032
  norm_num [row032] at h ⊢
  exact h

def row033 : Row :=
  ⟨20/3,160/23,(-50),35/4, ![15,6,0,13,12],
   ![⟨0,0⟩,⟨7,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,7,0,0],![6,7,0,1]], true⟩
theorem valid033 : row033.Valid := by decide +kernel
theorem piece033 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (20/3:ℝ) (160/23:ℝ) ∧
    (∫ x in (20/3:ℝ)..(160/23:ℝ), innerR 7 6 (3/40) x / x^3) = (9/1024:ℝ) := by
  have h := row_integral row033 valid033
  norm_num [row033] at h ⊢
  exact h

def row034 : Row :=
  ⟨160/23,300/43,(-42),38/5, ![16,6,0,13,12],
   ![⟨0,0⟩,⟨7,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,7,0,0],![6,7,0,1]], false⟩
theorem valid034 : row034.Valid := by decide +kernel
theorem piece034 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (160/23:ℝ) (300/43:ℝ) ∧
    (∫ x in (160/23:ℝ)..(300/43:ℝ), innerR 7 6 (3/40) x / x^3) = (419/640000:ℝ) := by
  have h := row_integral row034 valid034
  norm_num [row034] at h ⊢
  exact h

def row035 : Row :=
  ⟨300/43,7,(-42),38/5, ![16,6,0,13,12],
   ![⟨0,0⟩,⟨7,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![6,6,0,0],![6,7,0,0],![6,7,0,1]], false⟩
theorem valid035 : row035.Valid := by decide +kernel
theorem piece035 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (300/43:ℝ) (7:ℝ) ∧
    (∫ x in (300/43:ℝ)..(7:ℝ), innerR 7 6 (3/40) x / x^3) = (53/70000:ℝ) := by
  have h := row_integral row035 valid035
  norm_num [row035] at h ⊢
  exact h

def row036 : Row :=
  ⟨7,260/37,(-49),27/4, ![16,7,0,14,12],
   ![⟨0,0⟩,⟨(-7),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![6,7,0,0],![6,7,0,1]], true⟩
theorem valid036 : row036.Valid := by decide +kernel
theorem piece036 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (7:ℝ) (260/37:ℝ) ∧
    (∫ x in (7:ℝ)..(260/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(123/946400:ℝ)) := by
  have h := row_integral row036 valid036
  norm_num [row036] at h ⊢
  exact h

def row037 : Row :=
  ⟨260/37,170/23,(-62),43/5, ![16,7,0,14,13],
   ![⟨0,0⟩,⟨(-7),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![6,7,0,0],![6,7,0,1]], true⟩
theorem valid037 : row037.Valid := by decide +kernel
theorem piece037 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (260/37:ℝ) (170/23:ℝ) ∧
    (∫ x in (260/37:ℝ)..(170/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(31/781456:ℝ)) := by
  have h := row_integral row037 valid037
  norm_num [row037] at h ⊢
  exact h

def row038 : Row :=
  ⟨170/23,320/43,(-107/2),149/20, ![17,7,0,14,13],
   ![⟨0,0⟩,⟨(-7),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![6,7,0,0],![6,7,0,1]], false⟩
theorem valid038 : row038.Valid := by decide +kernel
theorem piece038 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (170/23:ℝ) (320/43:ℝ) ∧
    (∫ x in (170/23:ℝ)..(320/43:ℝ), innerR 7 6 (3/40) x / x^3) = (5143/23674880:ℝ) := by
  have h := row_integral row038 valid038
  norm_num [row038] at h ⊢
  exact h

def row039 : Row :=
  ⟨320/43,15/2,(-59/2),169/40, ![17,7,0,14,13],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-7),1⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![7,7,0,1],![6,7,0,1]], false⟩
theorem valid039 : row039.Valid := by decide +kernel
theorem piece039 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (320/43:ℝ) (15/2:ℝ) ∧
    (∫ x in (320/43:ℝ)..(15/2:ℝ), innerR 7 6 (3/40) x / x^3) = (1061/3686400:ℝ) := by
  have h := row_integral row039 valid039
  norm_num [row039] at h ⊢
  exact h

theorem block001 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (120/23:ℝ) (15/2:ℝ) ∧
    (∫ x in (120/23:ℝ)..(15/2:ℝ), innerR 7 6 (3/40) x / x^3) = (1536908029/19603584000:ℝ) := by
  have h := piece020
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (200/37:ℝ) (11/2:ℝ)
    (181/15000:ℝ) (59703/9680000:ℝ) h piece021
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (11/2:ℝ) (240/43:ℝ)
    (21181/1161600:ℝ) (153097/27878400:ℝ) h piece022
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (240/43:ℝ) (130/23:ℝ)
    (60131/2534400:ℝ) (189539/38937600:ℝ) h piece023
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (130/23:ℝ) (220/37:ℝ)
    (1020589/35692800:ℝ) (6603/327184:ℝ) h piece024
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (220/37:ℝ) (6:ℝ)
    (1473083/30201600:ℝ) (3221/871200:ℝ) h piece025
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (6:ℝ) (260/43:ℝ)
    (432203/8236800:ℝ) (1003/1216800:ℝ) h piece026
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (260/43:ℝ) (140/23:ℝ)
    (1902301/35692800:ℝ) (1259/1656200:ℝ) h piece027
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (140/23:ℝ) (240/37:ℝ)
    (7272481/134534400:ℝ) (25313/2822400:ℝ) h piece028
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (240/37:ℝ) (13/2:ℝ)
    (1816943/28828800:ℝ) (1667/4867200:ℝ) h piece029
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (13/2:ℝ) (280/43:ℝ)
    (3958103/62462400:ℝ) (15849/52998400:ℝ) h piece030
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (280/43:ℝ) (150/23:ℝ)
    (8565377/134534400:ℝ) (2061/7840000:ℝ) h piece031
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (150/23:ℝ) (20/3:ℝ)
    (15358471/240240000:ℝ) (59/15000:ℝ) h piece032
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (20/3:ℝ) (160/23:ℝ)
    (3260683/48048000:ℝ) (9/1024:ℝ) h piece033
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (160/23:ℝ) (300/43:ℝ)
    (29463839/384384000:ℝ) (419/640000:ℝ) h piece034
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (300/43:ℝ) (7:ℝ)
    (37144363/480480000:ℝ) (53/70000:ℝ) h piece035
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (7:ℝ) (260/37:ℝ)
    (7501631/96096000:ℝ) (-(123/946400:ℝ)) h piece036
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (260/37:ℝ) (170/23:ℝ)
    (97358843/1249248000:ℝ) (-(31/781456:ℝ)) h piece037
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (170/23:ℝ) (320/43:ℝ)
    (2163260279/27771744000:ℝ) (5143/23674880:ℝ) h piece038
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (120/23:ℝ) (320/43:ℝ) (15/2:ℝ)
    (8166751093/104552448000:ℝ) (1061/3686400:ℝ) h piece039
  norm_num at h
  exact h

end SplitData
