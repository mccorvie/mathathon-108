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

def row060 : Row :=
  ⟨420/43,10,(-117),109/10, ![22,9,0,19,18],
   ![⟨0,0⟩,⟨10,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![9,9,0,0],![9,10,0,0],![9,10,0,1]], false⟩
theorem valid060 : row060.Valid := by decide +kernel
theorem piece060 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (420/43:ℝ) (10:ℝ) ∧
    (∫ x in (420/43:ℝ)..(10:ℝ), innerR 7 6 (3/40) x / x^3) = (-(263/117600:ℝ)) := by
  have h := row_integral row060 valid060
  norm_num [row060] at h ⊢
  exact h

def row061 : Row :=
  ⟨10,440/43,(-114),35/4, ![23,10,0,20,18],
   ![⟨0,0⟩,⟨(-10),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![9,10,0,0],![9,10,0,1]], true⟩
theorem valid061 : row061.Valid := by decide +kernel
theorem piece061 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (10:ℝ) (440/43:ℝ) ∧
    (∫ x in (10:ℝ)..(440/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1109/193600:ℝ)) := by
  have h := row_integral row061 valid061
  norm_num [row061] at h ⊢
  exact h

def row062 : Row :=
  ⟨440/43,380/37,(-81),221/40, ![23,10,0,20,18],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-10),1⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,10,0,1],![9,10,0,1]], true⟩
theorem valid062 : row062.Valid := by decide +kernel
theorem piece062 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (440/43:ℝ) (380/37:ℝ) ∧
    (∫ x in (440/43:ℝ)..(380/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(119199/139779200:ℝ)) := by
  have h := row_integral row062 valid062
  norm_num [row062] at h ⊢
  exact h

def row063 : Row :=
  ⟨380/37,240/23,(-100),59/8, ![23,10,0,20,19],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-10),1⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,10,0,1],![9,10,0,1]], true⟩
theorem valid063 : row063.Valid := by decide +kernel
theorem piece063 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (380/37:ℝ) (240/23:ℝ) ∧
    (∫ x in (380/37:ℝ)..(240/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3647/1039680:ℝ)) := by
  have h := row_integral row063 valid063
  norm_num [row063] at h ⊢
  exact h

def row064 : Row :=
  ⟨240/23,21/2,(-88),249/40, ![24,10,0,20,19],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-10),1⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,10,0,1],![9,10,0,1]], false⟩
theorem valid064 : row064.Valid := by decide +kernel
theorem piece064 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (240/23:ℝ) (21/2:ℝ) ∧
    (∫ x in (240/23:ℝ)..(21/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(611/470400:ℝ)) := by
  have h := row_integral row064 valid064
  norm_num [row064] at h ⊢
  exact h

def row065 : Row :=
  ⟨21/2,460/43,(-197/2),289/40, ![24,10,0,21,19],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨11,(-1)⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,10,0,1],![10,11,0,1]], true⟩
theorem valid065 : row065.Valid := by decide +kernel
theorem piece065 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (21/2:ℝ) (460/43:ℝ) ∧
    (∫ x in (21/2:ℝ)..(460/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1359269/373262400:ℝ)) := by
  have h := row_integral row065 valid065
  norm_num [row065] at h ⊢
  exact h

def row066 : Row :=
  ⟨460/43,400/37,(-197/2),289/40, ![24,10,0,21,19],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨11,(-1)⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,10,0,1],![10,11,0,1]], true⟩
theorem valid066 : row066.Valid := by decide +kernel
theorem piece066 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (460/43:ℝ) (400/37:ℝ) ∧
    (∫ x in (460/43:ℝ)..(400/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(640683/338560000:ℝ)) := by
  have h := row_integral row066 valid066
  norm_num [row066] at h ⊢
  exact h

def row067 : Row :=
  ⟨400/37,250/23,(-297/2),237/20, ![24,10,0,21,20],
   ![⟨0,0⟩,⟨11,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,11,0,0],![10,11,0,1]], true⟩
theorem valid067 : row067.Valid := by decide +kernel
theorem piece067 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (400/37:ℝ) (250/23:ℝ) ∧
    (∫ x in (400/37:ℝ)..(250/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(14793/16000000:ℝ)) := by
  have h := row_integral row067 valid067
  norm_num [row067] at h ⊢
  exact h

def row068 : Row :=
  ⟨250/23,11,(-136),107/10, ![25,10,0,21,20],
   ![⟨0,0⟩,⟨11,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![10,10,0,0],![10,11,0,0],![10,11,0,1]], false⟩
theorem valid068 : row068.Valid := by decide +kernel
theorem piece068 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (250/23:ℝ) (11:ℝ) ∧
    (∫ x in (250/23:ℝ)..(11:ℝ), innerR 7 6 (3/40) x / x^3) = (-(14337/7562500:ℝ)) := by
  have h := row_integral row068 valid068
  norm_num [row068] at h ⊢
  exact h

def row069 : Row :=
  ⟨11,480/43,(-147),197/20, ![25,11,0,22,20],
   ![⟨0,0⟩,⟨(-11),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![10,11,0,0],![10,11,0,1]], true⟩
theorem valid069 : row069.Valid := by decide +kernel
theorem piece069 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (11:ℝ) (480/43:ℝ) ∧
    (∫ x in (11:ℝ)..(480/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3367/743424:ℝ)) := by
  have h := row_integral row069 valid069
  norm_num [row069] at h ⊢
  exact h

def row070 : Row :=
  ⟨480/43,260/23,(-111),53/8, ![25,11,0,22,20],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-11),1⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![10,11,0,1]], true⟩
theorem valid070 : row070.Valid := by decide +kernel
theorem piece070 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (480/43:ℝ) (260/23:ℝ) ∧
    (∫ x in (480/43:ℝ)..(260/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(94829/25958400:ℝ)) := by
  have h := row_integral row070 valid070
  norm_num [row070] at h ⊢
  exact h

def row071 : Row :=
  ⟨260/23,420/37,(-98),219/40, ![26,11,0,22,20],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-11),1⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![10,11,0,1]], false⟩
theorem valid071 : row071.Valid := by decide +kernel
theorem piece071 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (260/23:ℝ) (420/37:ℝ) ∧
    (∫ x in (260/23:ℝ)..(420/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(991/851760:ℝ)) := by
  have h := row_integral row071 valid071
  norm_num [row071] at h ⊢
  exact h

def row072 : Row :=
  ⟨420/37,23/2,(-119),293/40, ![26,11,0,22,21],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-11),1⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![10,11,0,1]], false⟩
theorem valid072 : row072.Valid := by decide +kernel
theorem piece072 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (420/37:ℝ) (23/2:ℝ) ∧
    (∫ x in (420/37:ℝ)..(23/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(9383/2666160:ℝ)) := by
  have h := row_integral row072 valid072
  norm_num [row072] at h ⊢
  exact h

def row073 : Row :=
  ⟨23/2,500/43,(-261/2),333/40, ![26,11,0,23,21],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨12,(-1)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![11,12,0,1]], true⟩
theorem valid073 : row073.Valid := by decide +kernel
theorem piece073 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (23/2:ℝ) (500/43:ℝ) ∧
    (∫ x in (23/2:ℝ)..(500/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1497969/529000000:ℝ)) := by
  have h := row_integral row073 valid073
  norm_num [row073] at h ⊢
  exact h

def row074 : Row :=
  ⟨500/43,35/3,(-261/2),333/40, ![26,11,0,23,21],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨12,(-1)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![11,12,0,1]], true⟩
theorem valid074 : row074.Valid := by decide +kernel
theorem piece074 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (500/43:ℝ) (35/3:ℝ) ∧
    (∫ x in (500/43:ℝ)..(35/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(40311/49000000:ℝ)) := by
  have h := row_integral row074 valid074
  norm_num [row074] at h ⊢
  exact h

def row075 : Row :=
  ⟨35/3,270/23,(-261/2),333/40, ![26,11,0,23,21],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨12,(-1)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![11,12,0,1]], true⟩
theorem valid075 : row075.Valid := by decide +kernel
theorem piece075 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (35/3:ℝ) (270/23:ℝ) ∧
    (∫ x in (35/3:ℝ)..(270/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1187/793800:ℝ)) := by
  have h := row_integral row075 valid075
  norm_num [row075] at h ⊢
  exact h

def row076 : Row :=
  ⟨270/23,440/37,(-117),287/40, ![27,11,0,23,21],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨12,(-1)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,11,0,1],![11,12,0,1]], false⟩
theorem valid076 : row076.Valid := by decide +kernel
theorem piece076 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (270/23:ℝ) (440/37:ℝ) ∧
    (∫ x in (270/23:ℝ)..(440/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(93613/31363200:ℝ)) := by
  have h := row_integral row076 valid076
  norm_num [row076] at h ⊢
  exact h

def row077 : Row :=
  ⟨440/37,12,(-172),59/5, ![27,11,0,23,22],
   ![⟨0,0⟩,⟨12,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![11,11,0,0],![11,12,0,0],![11,12,0,1]], false⟩
theorem valid077 : row077.Valid := by decide +kernel
theorem piece077 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (440/37:ℝ) (12:ℝ) ∧
    (∫ x in (440/37:ℝ)..(12:ℝ), innerR 7 6 (3/40) x / x^3) = (-(343/174240:ℝ)) := by
  have h := row_integral row077 valid077
  norm_num [row077] at h ⊢
  exact h

def row078 : Row :=
  ⟨12,520/43,(-184),219/20, ![27,12,0,24,22],
   ![⟨0,0⟩,⟨(-12),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![11,12,0,0],![11,12,0,1]], true⟩
theorem valid078 : row078.Valid := by decide +kernel
theorem piece078 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (12:ℝ) (520/43:ℝ) ∧
    (∫ x in (12:ℝ)..(520/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(3373/1216800:ℝ)) := by
  have h := row_integral row078 valid078
  norm_num [row078] at h ⊢
  exact h

def row079 : Row :=
  ⟨520/43,280/23,(-145),309/40, ![27,12,0,24,22],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-12),1⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![11,12,0,1]], true⟩
theorem valid079 : row079.Valid := by decide +kernel
theorem piece079 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (520/43:ℝ) (280/23:ℝ) ∧
    (∫ x in (520/43:ℝ)..(280/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(15381/6624800:ℝ)) := by
  have h := row_integral row079 valid079
  norm_num [row079] at h ⊢
  exact h

theorem block003 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (420/43:ℝ) (280/23:ℝ) ∧
    (∫ x in (420/43:ℝ)..(280/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1323874307579/26456189760000:ℝ)) := by
  have h := piece060
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (10:ℝ) (440/43:ℝ)
    (-(263/117600:ℝ)) (-(1109/193600:ℝ)) h piece061
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (440/43:ℝ) (380/37:ℝ)
    (-(226669/28459200:ℝ)) (-(119199/139779200:ℝ)) h piece062
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (380/37:ℝ) (240/23:ℝ)
    (-(16470661/1867958400:ℝ)) (-(3647/1039680:ℝ)) h piece063
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (240/23:ℝ) (21/2:ℝ)
    (-(3635227/294940800:ℝ)) (-(611/470400:ℝ)) h piece064
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (21/2:ℝ) (460/43:ℝ)
    (-(1004581/73735200:ℝ)) (-(1359269/373262400:ℝ)) h piece065
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (460/43:ℝ) (400/37:ℝ)
    (-(448977973/26003947200:ℝ)) (-(640683/338560000:ℝ)) h piece066
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (400/37:ℝ) (250/23:ℝ)
    (-(376701121/19662720000:ℝ)) (-(14793/16000000:ℝ)) h piece067
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (250/23:ℝ) (11:ℝ)
    (-(2468003341/122892000000:ℝ)) (-(14337/7562500:ℝ)) h piece068
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (11:ℝ) (480/43:ℝ)
    (-(1188432167/54072480000:ℝ)) (-(3367/743424:ℝ)) h piece069
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (480/43:ℝ) (260/23:ℝ)
    (-(94765541/3575040000:ℝ)) (-(94829/25958400:ℝ)) h piece070
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (260/23:ℝ) (420/37:ℝ)
    (-(4555630351/151045440000:ℝ)) (-(991/851760:ℝ)) h piece071
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (420/37:ℝ) (23/2:ℝ)
    (-(1091854081/34856640000:ℝ)) (-(9383/2666160:ℝ)) h piece072
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (23/2:ℝ) (500/43:ℝ)
    (-(71387070761/2048795840000:ℝ)) (-(1497969/529000000:ℝ)) h piece073
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (500/43:ℝ) (35/3:ℝ)
    (-(83900700847/2226952000000:ℝ)) (-(40311/49000000:ℝ)) h piece074
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (35/3:ℝ) (270/23:ℝ)
    (-(3429310207/89078080000:ℝ)) (-(1187/793800:ℝ)) h piece075
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (270/23:ℝ) (440/37:ℝ)
    (-(288563481967/7215324480000:ℝ)) (-(93613/31363200:ℝ)) h piece076
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (440/37:ℝ) (12:ℝ)
    (-(12507359012569/291018087360000:ℝ)) (-(343/174240:ℝ)) h piece077
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (12:ℝ) (520/43:ℝ)
    (-(1189112946779/26456189760000:ℝ)) (-(3373/1216800:ℝ)) h piece078
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (420/43:ℝ) (520/43:ℝ) (280/23:ℝ)
    (-(16411852154927/343930466880000:ℝ)) (-(15381/6624800:ℝ)) h piece079
  norm_num at h
  exact h

end SplitData
