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

def row000 : Row :=
  ⟨3,70/23,(-6),109/20, ![6,3,0,6,5],
   ![⟨0,0⟩,⟨(-3),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![2,3,0,0],![2,3,-1,0]], true⟩
theorem valid000 : row000.Valid := by decide +kernel
theorem piece000 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (3:ℝ) (70/23:ℝ) ∧
    (∫ x in (3:ℝ)..(70/23:ℝ), innerR 7 6 (3/40) x / x^3) = (97/5880:ℝ) := by
  have h := row_integral row000 valid000
  norm_num [row000] at h ⊢
  exact h

def row001 : Row :=
  ⟨70/23,120/37,(-5/2),43/10, ![7,3,0,6,5],
   ![⟨0,0⟩,⟨(-3),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![2,3,0,0],![2,3,-1,0]], false⟩
theorem valid001 : row001.Valid := by decide +kernel
theorem piece001 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (70/23:ℝ) (120/37:ℝ) ∧
    (∫ x in (70/23:ℝ)..(120/37:ℝ), innerR 7 6 (3/40) x / x^3) = (200141/2822400:ℝ) := by
  have h := row_integral row001 valid001
  norm_num [row001] at h ⊢
  exact h

def row002 : Row :=
  ⟨120/37,140/43,(-35/2),357/40, ![7,3,0,6,6],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-3),1⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,3,-1,0],![2,3,-1,0]], false⟩
theorem valid002 : row002.Valid := by decide +kernel
theorem piece002 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (120/37:ℝ) (140/43:ℝ) ∧
    (∫ x in (120/37:ℝ)..(140/43:ℝ), innerR 7 6 (3/40) x / x^3) = (1699/403200:ℝ) := by
  have h := row_integral row002 valid002
  norm_num [row002] at h ⊢
  exact h

def row003 : Row :=
  ⟨140/43,10/3,(-35/2),357/40, ![7,3,0,6,6],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-3),1⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,3,-1,0],![2,3,-1,0]], false⟩
theorem valid003 : row003.Valid := by decide +kernel
theorem piece003 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (140/43:ℝ) (10/3:ℝ) ∧
    (∫ x in (140/43:ℝ)..(10/3:ℝ), innerR 7 6 (3/40) x / x^3) = (289/11200:ℝ) := by
  have h := row_integral row003 valid003
  norm_num [row003] at h ⊢
  exact h

def row004 : Row :=
  ⟨10/3,80/23,(-17),351/40, ![7,3,0,6,6],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-3),1⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,3,-1,0],![2,3,-1,0]], true⟩
theorem valid004 : row004.Valid := by decide +kernel
theorem piece004 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (10/3:ℝ) (80/23:ℝ) ∧
    (∫ x in (10/3:ℝ)..(80/23:ℝ), innerR 7 6 (3/40) x / x^3) = (121/2560:ℝ) := by
  have h := row_integral row004 valid004
  norm_num [row004] at h ⊢
  exact h

def row005 : Row :=
  ⟨80/23,7/2,(-13),61/8, ![8,3,0,6,6],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-3),1⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,3,-1,0],![2,3,-1,0]], false⟩
theorem valid005 : row005.Valid := by decide +kernel
theorem piece005 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (80/23:ℝ) (7/2:ℝ) ∧
    (∫ x in (80/23:ℝ)..(7/2:ℝ), innerR 7 6 (3/40) x / x^3) = (4367/627200:ℝ) := by
  have h := row_integral row005 valid005
  norm_num [row005] at h ⊢
  exact h

def row006 : Row :=
  ⟨7/2,160/43,(-33/2),69/8, ![8,3,0,7,6],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨4,(-1)⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,3,-1,0],![3,4,-1,0]], true⟩
theorem valid006 : row006.Valid := by decide +kernel
theorem piece006 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (7/2:ℝ) (160/43:ℝ) ∧
    (∫ x in (7/2:ℝ)..(160/43:ℝ), innerR 7 6 (3/40) x / x^3) = (344793/5017600:ℝ) := by
  have h := row_integral row006 valid006
  norm_num [row006] at h ⊢
  exact h

def row007 : Row :=
  ⟨160/43,140/37,(-9/2),27/5, ![8,3,0,7,6],
   ![⟨0,0⟩,⟨4,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,4,0,0],![3,4,-1,0]], true⟩
theorem valid007 : row007.Valid := by decide +kernel
theorem piece007 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (160/43:ℝ) (140/37:ℝ) ∧
    (∫ x in (160/43:ℝ)..(140/37:ℝ), innerR 7 6 (3/40) x / x^3) = (18819/1003520:ℝ) := by
  have h := row_integral row007 valid007
  norm_num [row007] at h ⊢
  exact h

def row008 : Row :=
  ⟨140/37,90/23,(-23/2),29/4, ![8,3,0,7,7],
   ![⟨0,0⟩,⟨4,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,4,0,0],![3,4,-1,0]], true⟩
theorem valid008 : row008.Valid := by decide +kernel
theorem piece008 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (140/37:ℝ) (90/23:ℝ) ∧
    (∫ x in (140/37:ℝ)..(90/23:ℝ), innerR 7 6 (3/40) x / x^3) = (9449/254016:ℝ) := by
  have h := row_integral row008 valid008
  norm_num [row008] at h ⊢
  exact h

def row009 : Row :=
  ⟨90/23,4,(-7),61/10, ![9,3,0,7,7],
   ![⟨0,0⟩,⟨4,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![3,3,0,0],![3,4,0,0],![3,4,-1,0]], false⟩
theorem valid009 : row009.Valid := by decide +kernel
theorem piece009 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (90/23:ℝ) (4:ℝ) ∧
    (∫ x in (90/23:ℝ)..(4:ℝ), innerR 7 6 (3/40) x / x^3) = (1559/64800:ℝ) := by
  have h := row_integral row009 valid009
  norm_num [row009] at h ⊢
  exact h

def row010 : Row :=
  ⟨4,180/43,(-11),21/4, ![9,4,0,8,7],
   ![⟨0,0⟩,⟨(-4),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![3,4,0,0],![3,4,-1,0]], true⟩
theorem valid010 : row010.Valid := by decide +kernel
theorem piece010 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (4:ℝ) (180/43:ℝ) ∧
    (∫ x in (4:ℝ)..(180/43:ℝ), innerR 7 6 (3/40) x / x^3) = (461/16200:ℝ) := by
  have h := row_integral row010 valid010
  norm_num [row010] at h ⊢
  exact h

def row011 : Row :=
  ⟨180/43,160/37,(-11),21/4, ![9,4,0,8,7],
   ![⟨0,0⟩,⟨(-4),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![3,4,0,0],![3,4,-1,0]], true⟩
theorem valid011 : row011.Valid := by decide +kernel
theorem piece011 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (180/43:ℝ) (160/37:ℝ) ∧
    (∫ x in (180/43:ℝ)..(160/37:ℝ), innerR 7 6 (3/40) x / x^3) = (84403/4147200:ℝ) := by
  have h := row_integral row011 valid011
  norm_num [row011] at h ⊢
  exact h

def row012 : Row :=
  ⟨160/37,100/23,(-31),79/8, ![9,4,0,8,8],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-4),1⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,4,-1,0],![3,4,-1,0]], true⟩
theorem valid012 : row012.Valid := by decide +kernel
theorem piece012 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (160/37:ℝ) (100/23:ℝ) ∧
    (∫ x in (160/37:ℝ)..(100/23:ℝ), innerR 7 6 (3/40) x / x^3) = (4361/1280000:ℝ) := by
  have h := row_integral row012 valid012
  norm_num [row012] at h ⊢
  exact h

def row013 : Row :=
  ⟨100/23,9/2,(-26),349/40, ![10,4,0,8,8],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨(-4),1⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,4,-1,0],![3,4,-1,0]], false⟩
theorem valid013 : row013.Valid := by decide +kernel
theorem piece013 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (100/23:ℝ) (9/2:ℝ) ∧
    (∫ x in (100/23:ℝ)..(9/2:ℝ), innerR 7 6 (3/40) x / x^3) = (35861/1620000:ℝ) := by
  have h := row_integral row013 valid013
  norm_num [row013] at h ⊢
  exact h

def row014 : Row :=
  ⟨9/2,200/43,(-61/2),389/40, ![10,4,0,9,8],
   ![⟨0,0⟩,⟨0,3/40⟩,⟨5,(-1)⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,4,-1,0],![4,5,-1,0]], true⟩
theorem valid014 : row014.Valid := by decide +kernel
theorem piece014 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (9/2:ℝ) (200/43:ℝ) ∧
    (∫ x in (9/2:ℝ)..(200/43:ℝ), innerR 7 6 (3/40) x / x^3) = (286169/12960000:ℝ) := by
  have h := row_integral row014 valid014
  norm_num [row014] at h ⊢
  exact h

def row015 : Row :=
  ⟨200/43,110/23,(-31/2),13/2, ![10,4,0,9,8],
   ![⟨0,0⟩,⟨5,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,5,0,0],![4,5,-1,0]], true⟩
theorem valid015 : row015.Valid := by decide +kernel
theorem piece015 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (200/43:ℝ) (110/23:ℝ) ∧
    (∫ x in (200/43:ℝ)..(110/23:ℝ), innerR 7 6 (3/40) x / x^3) = (367601/19360000:ℝ) := by
  have h := row_integral row015 valid015
  norm_num [row015] at h ⊢
  exact h

def row016 : Row :=
  ⟨110/23,180/37,(-10),107/20, ![11,4,0,9,8],
   ![⟨0,0⟩,⟨5,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,5,0,0],![4,5,-1,0]], false⟩
theorem valid016 : row016.Valid := by decide +kernel
theorem piece016 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (110/23:ℝ) (180/37:ℝ) ∧
    (∫ x in (110/23:ℝ)..(180/37:ℝ), innerR 7 6 (3/40) x / x^3) = (5677/490050:ℝ) := by
  have h := row_integral row016 valid016
  norm_num [row016] at h ⊢
  exact h

def row017 : Row :=
  ⟨180/37,5,(-19),36/5, ![11,4,0,9,9],
   ![⟨0,0⟩,⟨5,(-1)⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![4,4,0,0],![4,5,0,0],![4,5,-1,0]], false⟩
theorem valid017 : row017.Valid := by decide +kernel
theorem piece017 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (180/37:ℝ) (5:ℝ) ∧
    (∫ x in (180/37:ℝ)..(5:ℝ), innerR 7 6 (3/40) x / x^3) = (241/12960:ℝ) := by
  have h := row_integral row017 valid017
  norm_num [row017] at h ⊢
  exact h

def row018 : Row :=
  ⟨5,220/43,(-24),127/20, ![11,5,0,10,9],
   ![⟨0,0⟩,⟨(-5),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![4,5,0,0],![4,5,-1,0]], true⟩
theorem valid018 : row018.Valid := by decide +kernel
theorem piece018 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (5:ℝ) (220/43:ℝ) ∧
    (∫ x in (5:ℝ)..(220/43:ℝ), innerR 7 6 (3/40) x / x^3) = (353/48400:ℝ) := by
  have h := row_integral row018 valid018
  norm_num [row018] at h ⊢
  exact h

def row019 : Row :=
  ⟨220/43,120/23,(-24),127/20, ![11,5,0,10,9],
   ![⟨0,0⟩,⟨(-5),1⟩,⟨0,3/40⟩,⟨1/2,0⟩],
   ![![5,5,0,0],![4,5,0,0],![4,5,-1,0]], true⟩
theorem valid019 : row019.Valid := by decide +kernel
theorem piece019 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (220/43:ℝ) (120/23:ℝ) ∧
    (∫ x in (220/43:ℝ)..(120/23:ℝ), innerR 7 6 (3/40) x / x^3) = (25/3872:ℝ) := by
  have h := row_integral row019 valid019
  norm_num [row019] at h ⊢
  exact h

theorem block000 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (3:ℝ) (120/23:ℝ) ∧
    (∫ x in (3:ℝ)..(120/23:ℝ), innerR 7 6 (3/40) x / x^3) = (10638527/22176000:ℝ) := by
  have h := piece000
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (70/23:ℝ) (120/37:ℝ)
    (97/5880:ℝ) (200141/2822400:ℝ) h piece001
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (120/37:ℝ) (140/43:ℝ)
    (35243/403200:ℝ) (1699/403200:ℝ) h piece002
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (140/43:ℝ) (10/3:ℝ)
    (6157/67200:ℝ) (289/11200:ℝ) h piece003
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (10/3:ℝ) (80/23:ℝ)
    (7891/67200:ℝ) (121/2560:ℝ) h piece004
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (80/23:ℝ) (7/2:ℝ)
    (44269/268800:ℝ) (4367/627200:ℝ) h piece005
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (7/2:ℝ) (160/43:ℝ)
    (40373/235200:ℝ) (344793/5017600:ℝ) h piece006
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (160/43:ℝ) (140/37:ℝ)
    (516893/2150400:ℝ) (18819/1003520:ℝ) h piece007
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (140/37:ℝ) (90/23:ℝ)
    (487567/1881600:ℝ) (9449/254016:ℝ) h piece008
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (90/23:ℝ) (4:ℝ)
    (2150587/7257600:ℝ) (1559/64800:ℝ) h piece009
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (4:ℝ) (180/43:ℝ)
    (51671/161280:ℝ) (461/16200:ℝ) h piece010
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (180/43:ℝ) (160/37:ℝ)
    (2531723/7257600:ℝ) (84403/4147200:ℝ) h piece011
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (160/37:ℝ) (100/23:ℝ)
    (1190857/3225600:ℝ) (4361/1280000:ℝ) h piece012
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (100/23:ℝ) (9/2:ℝ)
    (3755771/10080000:ℝ) (35861/1620000:ℝ) h piece013
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (9/2:ℝ) (200/43:ℝ)
    (7162031/18144000:ℝ) (286169/12960000:ℝ) h piece014
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (200/43:ℝ) (110/23:ℝ)
    (700247/1680000:ℝ) (367601/19360000:ℝ) h piece015
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (110/23:ℝ) (180/37:ℝ)
    (35435879/81312000:ℝ) (5677/490050:ℝ) h piece016
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (180/37:ℝ) (5:ℝ)
    (89291063/199584000:ℝ) (241/12960:ℝ) h piece017
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (5:ℝ) (220/43:ℝ)
    (10333607/22176000:ℝ) (353/48400:ℝ) h piece018
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (220/43:ℝ) (120/23:ℝ)
    (115448797/243936000:ℝ) (25/3872:ℝ) h piece019
  norm_num at h
  exact h

end SplitData
