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

def row040 : Row :=
  ⟨15/2,280/37,(-37),209/40, ![17,7,0,15,13],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨8,(-1)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![7,7,0,1],![7,8,0,1]], true⟩
theorem valid040 : row040.Valid := by decide +kernel
theorem piece040 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (15/2:ℝ) (280/37:ℝ) ∧
    (∫ x in (15/2:ℝ)..(280/37:ℝ), innerR 7 6 (3/40) x / x^3) = (527/1411200:ℝ) := by
  have h := row_integral row040 valid040
  norm_num [row040] at h ⊢
  exact h

def row041 : Row :=
  ⟨280/37,180/23,(-72),197/20, ![17,7,0,15,14],
   ![⟨0,0⟩,⟨8,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![7,8,0,0],![7,8,0,1]], true⟩
theorem valid041 : row041.Valid := by decide +kernel
theorem piece041 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (280/37:ℝ) (180/23:ℝ) ∧
    (∫ x in (280/37:ℝ)..(180/23:ℝ), innerR 7 6 (3/40) x / x^3) = (253/117600:ℝ) := by
  have h := row_integral row041 valid041
  norm_num [row041] at h ⊢
  exact h

def row042 : Row :=
  ⟨180/23,340/43,(-63),87/10, ![18,7,0,15,14],
   ![⟨0,0⟩,⟨8,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![7,8,0,0],![7,8,0,1]], false⟩
theorem valid042 : row042.Valid := by decide +kernel
theorem piece042 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (180/23:ℝ) (340/43:ℝ) ∧
    (∫ x in (180/23:ℝ)..(340/43:ℝ), innerR 7 6 (3/40) x / x^3) = (47/52020:ℝ) := by
  have h := row_integral row042 valid042
  norm_num [row042] at h ⊢
  exact h

def row043 : Row :=
  ⟨340/43,8,(-63),87/10, ![18,7,0,15,14],
   ![⟨0,0⟩,⟨8,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![7,7,0,0],![7,8,0,0],![7,8,0,1]], false⟩
theorem valid043 : row043.Valid := by decide +kernel
theorem piece043 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (340/43:ℝ) (8:ℝ) ∧
    (∫ x in (340/43:ℝ)..(8:ℝ), innerR 7 6 (3/40) x / x^3) = (1059/924800:ℝ) := by
  have h := row_integral row043 valid043
  norm_num [row043] at h ⊢
  exact h

def row044 : Row :=
  ⟨8,300/37,(-71),157/20, ![18,8,0,16,14],
   ![⟨0,0⟩,⟨(-8),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![7,8,0,0],![7,8,0,1]], true⟩
theorem valid044 : row044.Valid := by decide +kernel
theorem piece044 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (8:ℝ) (300/37:ℝ) ∧
    (∫ x in (8:ℝ)..(300/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1159/720000:ℝ)) := by
  have h := row_integral row044 valid044
  norm_num [row044] at h ⊢
  exact h

def row045 : Row :=
  ⟨300/37,190/23,(-86),97/10, ![18,8,0,16,15],
   ![⟨0,0⟩,⟨(-8),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![7,8,0,0],![7,8,0,1]], true⟩
theorem valid045 : row045.Valid := by decide +kernel
theorem piece045 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (300/37:ℝ) (190/23:ℝ) ∧
    (∫ x in (300/37:ℝ)..(190/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(59917/32490000:ℝ)) := by
  have h := row_integral row045 valid045
  norm_num [row045] at h ⊢
  exact h

def row046 : Row :=
  ⟨190/23,25/3,(-153/2),171/20, ![19,8,0,16,15],
   ![⟨0,0⟩,⟨(-8),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![7,8,0,0],![7,8,0,1]], false⟩
theorem valid046 : row046.Valid := by decide +kernel
theorem piece046 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (190/23:ℝ) (25/3:ℝ) ∧
    (∫ x in (190/23:ℝ)..(25/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2547/3610000:ℝ)) := by
  have h := row_integral row046 valid046
  norm_num [row046] at h ⊢
  exact h

def row047 : Row :=
  ⟨25/3,360/43,(-153/2),171/20, ![19,8,0,16,15],
   ![⟨0,0⟩,⟨(-8),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![7,8,0,0],![7,8,0,1]], false⟩
theorem valid047 : row047.Valid := by decide +kernel
theorem piece047 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (25/3:ℝ) (360/43:ℝ) ∧
    (∫ x in (25/3:ℝ)..(360/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(487/1440000:ℝ)) := by
  have h := row_integral row047 valid047
  norm_num [row047] at h ⊢
  exact h

def row048 : Row :=
  ⟨360/43,17/2,(-99/2),213/40, ![19,8,0,16,15],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-8),1⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![8,8,0,1],![7,8,0,1]], false⟩
theorem valid048 : row048.Valid := by decide +kernel
theorem piece048 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (360/43:ℝ) (17/2:ℝ) ∧
    (∫ x in (360/43:ℝ)..(17/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(16247/16646400:ℝ)) := by
  have h := row_integral row048 valid048
  norm_num [row048] at h ⊢
  exact h

def row049 : Row :=
  ⟨17/2,320/37,(-58),253/40, ![19,8,0,17,15],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨9,(-1)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![8,8,0,1],![8,9,0,1]], true⟩
theorem valid049 : row049.Valid := by decide +kernel
theorem piece049 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (17/2:ℝ) (320/37:ℝ) ∧
    (∫ x in (17/2:ℝ)..(320/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(26323/29593600:ℝ)) := by
  have h := row_integral row049 valid049
  norm_num [row049] at h ⊢
  exact h

def row050 : Row :=
  ⟨320/37,200/23,(-98),219/20, ![19,8,0,17,16],
   ![⟨0,0⟩,⟨9,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![8,9,0,0],![8,9,0,1]], true⟩
theorem valid050 : row050.Valid := by decide +kernel
theorem piece050 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (320/37:ℝ) (200/23:ℝ) ∧
    (∫ x in (320/37:ℝ)..(200/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(561/2560000:ℝ)) := by
  have h := row_integral row050 valid050
  norm_num [row050] at h ⊢
  exact h

def row051 : Row :=
  ⟨200/23,380/43,(-88),49/5, ![20,8,0,17,16],
   ![⟨0,0⟩,⟨9,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![8,9,0,0],![8,9,0,1]], false⟩
theorem valid051 : row051.Valid := by decide +kernel
theorem piece051 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (200/23:ℝ) (380/43:ℝ) ∧
    (∫ x in (200/23:ℝ)..(380/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1589/3610000:ℝ)) := by
  have h := row_integral row051 valid051
  norm_num [row051] at h ⊢
  exact h

def row052 : Row :=
  ⟨380/43,9,(-88),49/5, ![20,8,0,17,16],
   ![⟨0,0⟩,⟨9,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![8,8,0,0],![8,9,0,0],![8,9,0,1]], false⟩
theorem valid052 : row052.Valid := by decide +kernel
theorem piece052 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (380/43:ℝ) (9:ℝ) ∧
    (∫ x in (380/43:ℝ)..(9:ℝ), innerR 7 6 (3/40) x / x^3) = (-(203/1462050:ℝ)) := by
  have h := row_integral row052 valid052
  norm_num [row052] at h ⊢
  exact h

def row053 : Row :=
  ⟨9,210/23,(-97),179/20, ![20,9,0,18,16],
   ![⟨0,0⟩,⟨(-9),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![8,9,0,0],![8,9,0,1]], true⟩
theorem valid053 : row053.Valid := by decide +kernel
theorem piece053 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (9:ℝ) (210/23:ℝ) ∧
    (∫ x in (9:ℝ)..(210/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1103/396900:ℝ)) := by
  have h := row_integral row053 valid053
  norm_num [row053] at h ⊢
  exact h

def row054 : Row :=
  ⟨210/23,340/37,(-173/2),39/5, ![21,9,0,18,16],
   ![⟨0,0⟩,⟨(-9),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![8,9,0,0],![8,9,0,1]], false⟩
theorem valid054 : row054.Valid := by decide +kernel
theorem piece054 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (210/23:ℝ) (340/37:ℝ) ∧
    (∫ x in (210/23:ℝ)..(340/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(46939/40783680:ℝ)) := by
  have h := row_integral row054 valid054
  norm_num [row054] at h ⊢
  exact h

def row055 : Row :=
  ⟨340/37,400/43,(-207/2),193/20, ![21,9,0,18,17],
   ![⟨0,0⟩,⟨(-9),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![8,9,0,0],![8,9,0,1]], false⟩
theorem valid055 : row055.Valid := by decide +kernel
theorem piece055 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (340/37:ℝ) (400/43:ℝ) ∧
    (∫ x in (340/37:ℝ)..(400/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(378153/184960000:ℝ)) := by
  have h := row_integral row055 valid055
  norm_num [row055] at h ⊢
  exact h

def row056 : Row :=
  ⟨400/43,19/2,(-147/2),257/40, ![21,9,0,18,17],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-9),1⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![9,9,0,1],![8,9,0,1]], false⟩
theorem valid056 : row056.Valid := by decide +kernel
theorem piece056 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (400/43:ℝ) (19/2:ℝ) ∧
    (∫ x in (400/43:ℝ)..(19/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(720443/231040000:ℝ)) := by
  have h := row_integral row056 valid056
  norm_num [row056] at h ⊢
  exact h

def row057 : Row :=
  ⟨19/2,220/23,(-83),297/40, ![21,9,0,19,17],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨10,(-1)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![9,9,0,1],![9,10,0,1]], true⟩
theorem valid057 : row057.Valid := by decide +kernel
theorem piece057 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (19/2:ℝ) (220/23:ℝ) ∧
    (∫ x in (19/2:ℝ)..(220/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(16077/17472400:ℝ)) := by
  have h := row_integral row057 valid057
  norm_num [row057] at h ⊢
  exact h

def row058 : Row :=
  ⟨220/23,360/37,(-72),251/40, ![22,9,0,19,17],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨10,(-1)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![9,9,0,1],![9,10,0,1]], false⟩
theorem valid058 : row058.Valid := by decide +kernel
theorem piece058 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (220/23:ℝ) (360/37:ℝ) ∧
    (∫ x in (220/23:ℝ)..(360/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3661/1742400:ℝ)) := by
  have h := row_integral row058 valid058
  norm_num [row058] at h ⊢
  exact h

def row059 : Row :=
  ⟨360/37,420/43,(-117),109/10, ![22,9,0,19,18],
   ![⟨0,0⟩,⟨10,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![9,10,0,0],![9,10,0,1]], false⟩
theorem valid059 : row059.Valid := by decide +kernel
theorem piece059 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (360/37:ℝ) (420/43:ℝ) ∧
    (∫ x in (360/37:ℝ)..(420/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(617/1411200:ℝ)) := by
  have h := row_integral row059 valid059
  norm_num [row059] at h ⊢
  exact h

theorem block002 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (15/2:ℝ) (420/43:ℝ) ∧
    (∫ x in (15/2:ℝ)..(420/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1012095961/66853248000:ℝ)) := by
  have h := piece040
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (280/37:ℝ) (180/23:ℝ)
    (527/1411200:ℝ) (253/117600:ℝ) h piece041
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (180/23:ℝ) (340/43:ℝ)
    (509/201600:ℝ) (47/52020:ℝ) h piece042
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (340/43:ℝ) (8:ℝ)
    (199741/58262400:ℝ) (1059/924800:ℝ) h piece043
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (8:ℝ) (300/37:ℝ)
    (461/100800:ℝ) (-(1159/720000:ℝ)) h piece044
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (300/37:ℝ) (190/23:ℝ)
    (4979/1680000:ℝ) (-(59917/32490000:ℝ)) h piece045
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (190/23:ℝ) (25/3:ℝ)
    (407381/363888000:ℝ) (-(2547/3610000:ℝ)) h piece046
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (25/3:ℝ) (360/43:ℝ)
    (39643/95760000:ℝ) (-(487/1440000:ℝ)) h piece047
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (360/43:ℝ) (17/2:ℝ)
    (2903/38304000:ℝ) (-(16247/16646400:ℝ)) h piece048
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (17/2:ℝ) (320/37:ℝ)
    (-(1245661/1383732000:ℝ)) (-(26323/29593600:ℝ)) h piece049
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (320/37:ℝ) (200/23:ℝ)
    (-(18646339/10418688000:ℝ)) (-(561/2560000:ℝ)) h piece050
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (200/23:ℝ) (380/43:ℝ)
    (-(26161871/13023360000:ℝ)) (-(1589/3610000:ℝ)) h piece051
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (380/43:ℝ) (9:ℝ)
    (-(121198393/49488768000:ℝ)) (-(203/1462050:ℝ)) h piece052
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (9:ℝ) (210/23:ℝ)
    (-(60664603/23442048000:ℝ)) (-(1103/396900:ℝ)) h piece053
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (210/23:ℝ) (340/37:ℝ)
    (-(97852949/18232704000:ℝ)) (-(46939/40783680:ℝ)) h piece054
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (340/37:ℝ) (400/43:ℝ)
    (-(41229317/6325632000:ℝ)) (-(378153/184960000:ℝ)) h piece055
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (400/43:ℝ) (19/2:ℝ)
    (-(3982511/465120000:ℝ)) (-(720443/231040000:ℝ)) h piece056
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (19/2:ℝ) (220/23:ℝ)
    (-(82579723/7069824000:ℝ)) (-(16077/17472400:ℝ)) h piece057
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (220/23:ℝ) (360/37:ℝ)
    (-(567330337/45023616000:ℝ)) (-(3661/1742400:ℝ)) h piece058
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (15/2:ℝ) (360/37:ℝ) (420/43:ℝ)
    (-(60175507/4093056000:ℝ)) (-(617/1411200:ℝ)) h piece059
  norm_num at h
  exact h

end SplitData
