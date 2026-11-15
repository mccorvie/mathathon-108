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

def row080 : Row :=
  ⟨280/23,460/37,(-131),263/40, ![28,12,0,24,22],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-12),1⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![11,12,0,1]], false⟩
theorem valid080 : row080.Valid := by decide +kernel
theorem piece080 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (280/23:ℝ) (460/37:ℝ) ∧
    (∫ x in (280/23:ℝ)..(460/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(577181/82947200:ℝ)) := by
  have h := row_integral row080 valid080
  norm_num [row080] at h ⊢
  exact h

def row081 : Row :=
  ⟨460/37,25/2,(-154),337/40, ![28,12,0,24,23],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-12),1⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![11,12,0,1]], false⟩
theorem valid081 : row081.Valid := by decide +kernel
theorem piece081 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (460/37:ℝ) (25/2:ℝ) ∧
    (∫ x in (460/37:ℝ)..(25/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(18071/10580000:ℝ)) := by
  have h := row_integral row081 valid081
  norm_num [row081] at h ⊢
  exact h

def row082 : Row :=
  ⟨25/2,540/43,(-333/2),377/40, ![28,12,0,25,23],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨13,(-1)⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![12,13,0,1]], true⟩
theorem valid082 : row082.Valid := by decide +kernel
theorem piece082 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (25/2:ℝ) (540/43:ℝ) ∧
    (∫ x in (25/2:ℝ)..(540/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(4637/3240000:ℝ)) := by
  have h := row_integral row082 valid082
  norm_num [row082] at h ⊢
  exact h

def row083 : Row :=
  ⟨540/43,290/23,(-333/2),377/40, ![28,12,0,25,23],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨13,(-1)⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![12,13,0,1]], true⟩
theorem valid083 : row083.Valid := by decide +kernel
theorem piece083 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (540/43:ℝ) (290/23:ℝ) ∧
    (∫ x in (540/43:ℝ)..(290/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(5299/4359744:ℝ)) := by
  have h := row_integral row083 valid083
  norm_num [row083] at h ⊢
  exact h

def row084 : Row :=
  ⟨290/23,480/37,(-152),331/40, ![29,12,0,25,23],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨13,(-1)⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,12,0,1],![12,13,0,1]], false⟩
theorem valid084 : row084.Valid := by decide +kernel
theorem piece084 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (290/23:ℝ) (480/37:ℝ) ∧
    (∫ x in (290/23:ℝ)..(480/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(194773/24220800:ℝ)) := by
  have h := row_integral row084 valid084
  norm_num [row084] at h ⊢
  exact h

def row085 : Row :=
  ⟨480/37,13,(-212),129/10, ![29,12,0,25,24],
   ![⟨0,0⟩,⟨13,(-1)⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![12,12,0,0],![12,13,0,0],![12,13,0,1]], false⟩
theorem valid085 : row085.Valid := by decide +kernel
theorem piece085 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (480/37:ℝ) (13:ℝ) ∧
    (∫ x in (480/37:ℝ)..(13:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2137/3893760:ℝ)) := by
  have h := row_integral row085 valid085
  norm_num [row085] at h ⊢
  exact h

def row086 : Row :=
  ⟨13,560/43,(-225),241/20, ![29,13,0,26,24],
   ![⟨0,0⟩,⟨(-13),1⟩,⟨1,(-3/40)⟩,⟨1/2,0⟩],
   ![![13,13,0,0],![12,13,0,0],![12,13,0,1]], true⟩
theorem valid086 : row086.Valid := by decide +kernel
theorem piece086 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (13:ℝ) (560/43:ℝ) ∧
    (∫ x in (13:ℝ)..(560/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(76327/105996800:ℝ)) := by
  have h := row_integral row086 valid086
  norm_num [row086] at h ⊢
  exact h

def row087 : Row :=
  ⟨560/43,300/23,(-183),353/40, ![29,13,0,26,24],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-13),1⟩,⟨1/2,0⟩],
   ![![13,13,0,0],![13,13,0,1],![12,13,0,1]], true⟩
theorem valid087 : row087.Valid := by decide +kernel
theorem piece087 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (560/43:ℝ) (300/23:ℝ) ∧
    (∫ x in (560/43:ℝ)..(300/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(29209/47040000:ℝ)) := by
  have h := row_integral row087 valid087
  norm_num [row087] at h ⊢
  exact h

def row088 : Row :=
  ⟨300/23,40/3,(-168),307/40, ![30,13,0,26,24],
   ![⟨0,0⟩,⟨1,(-3/40)⟩,⟨(-13),1⟩,⟨1/2,0⟩],
   ![![13,13,0,0],![13,13,0,1],![12,13,0,1]], false⟩
theorem valid088 : row088.Valid := by decide +kernel
theorem piece088 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (300/23:ℝ) (40/3:ℝ) ∧
    (∫ x in (300/23:ℝ)..(40/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1013/120000:ℝ)) := by
  have h := row_integral row088 valid088
  norm_num [row088] at h ⊢
  exact h

def row089 : Row :=
  ⟨40/3,310/23,(-184),799/40, ![30,13,1,26,24],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-13),1⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![12,13,0,1]], true⟩
theorem valid089 : row089.Valid := by decide +kernel
theorem piece089 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (40/3:ℝ) (310/23:ℝ) ∧
    (∫ x in (40/3:ℝ)..(310/23:ℝ), innerR 7 6 (3/40) x / x^3) = (7749/1537600:ℝ) := by
  have h := row_integral row089 valid089
  norm_num [row089] at h ⊢
  exact h

def row090 : Row :=
  ⟨310/23,580/43,(-337/2),753/40, ![31,13,1,26,24],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-13),1⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![12,13,0,1]], false⟩
theorem valid090 : row090.Valid := by decide +kernel
theorem piece090 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (310/23:ℝ) (580/43:ℝ) ∧
    (∫ x in (310/23:ℝ)..(580/43:ℝ), innerR 7 6 (3/40) x / x^3) = (91023/258624320:ℝ) := by
  have h := row_integral row090 valid090
  norm_num [row090] at h ⊢
  exact h

def row091 : Row :=
  ⟨580/43,27/2,(-337/2),753/40, ![31,13,1,26,24],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-13),1⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![12,13,0,1]], false⟩
theorem valid091 : row091.Valid := by decide +kernel
theorem piece091 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (580/43:ℝ) (27/2:ℝ) ∧
    (∫ x in (580/43:ℝ)..(27/2:ℝ), innerR 7 6 (3/40) x / x^3) = (397021/980942400:ℝ) := by
  have h := row_integral row091 valid091
  norm_num [row091] at h ⊢
  exact h

def row092 : Row :=
  ⟨27/2,500/37,(-182),793/40, ![31,13,1,27,24],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨14,(-1)⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![13,14,0,1]], true⟩
theorem valid092 : row092.Valid := by decide +kernel
theorem piece092 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (27/2:ℝ) (500/37:ℝ) ∧
    (∫ x in (27/2:ℝ)..(500/37:ℝ), innerR 7 6 (3/40) x / x^3) = (171457/364500000:ℝ) := by
  have h := row_integral row092 valid092
  norm_num [row092] at h ⊢
  exact h

def row093 : Row :=
  ⟨500/37,320/23,(-207),867/40, ![31,13,1,27,25],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨14,(-1)⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![13,14,0,1]], true⟩
theorem valid093 : row093.Valid := by decide +kernel
theorem piece093 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (500/37:ℝ) (320/23:ℝ) ∧
    (∫ x in (500/37:ℝ)..(320/23:ℝ), innerR 7 6 (3/40) x / x^3) = (1788927/128000000:ℝ) := by
  have h := row_integral row093 valid093
  norm_num [row093] at h ⊢
  exact h

def row094 : Row :=
  ⟨320/23,600/43,(-191),821/40, ![32,13,1,27,25],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨14,(-1)⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,13,0,1],![13,14,0,1]], false⟩
theorem valid094 : row094.Valid := by decide +kernel
theorem piece094 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (320/23:ℝ) (600/43:ℝ) ∧
    (∫ x in (320/23:ℝ)..(600/43:ℝ), innerR 7 6 (3/40) x / x^3) = (65441/46080000:ℝ) := by
  have h := row_integral row094 valid094
  norm_num [row094] at h ⊢
  exact h

def row095 : Row :=
  ⟨600/43,14,(-146),173/10, ![32,13,1,27,25],
   ![⟨0,0⟩,⟨14,(-1)⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![13,13,1,1],![13,14,1,1],![13,14,0,1]], false⟩
theorem valid095 : row095.Valid := by decide +kernel
theorem piece095 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (600/43:ℝ) (14:ℝ) ∧
    (∫ x in (600/43:ℝ)..(14:ℝ), innerR 7 6 (3/40) x / x^3) = (28787/17640000:ℝ) := by
  have h := row_integral row095 valid095
  norm_num [row095] at h ⊢
  exact h

def row096 : Row :=
  ⟨14,520/37,(-160),329/20, ![32,14,1,28,25],
   ![⟨0,0⟩,⟨(-14),1⟩,⟨(-1),3/40⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![13,14,1,1],![13,14,0,1]], true⟩
theorem valid096 : row096.Valid := by decide +kernel
theorem piece096 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (14:ℝ) (520/37:ℝ) ∧
    (∫ x in (14:ℝ)..(520/37:ℝ), innerR 7 6 (3/40) x / x^3) = (9179/6624800:ℝ) := by
  have h := row_integral row096 valid096
  norm_num [row096] at h ⊢
  exact h

def row097 : Row :=
  ⟨520/37,330/23,(-225),843/40, ![32,14,1,28,26],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-14),1⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![13,14,0,1]], true⟩
theorem valid097 : row097.Valid := by decide +kernel
theorem piece097 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (520/37:ℝ) (330/23:ℝ) ∧
    (∫ x in (520/37:ℝ)..(330/23:ℝ), innerR 7 6 (3/40) x / x^3) = (19941/2617472:ℝ) := by
  have h := row_integral row097 valid097
  norm_num [row097] at h ⊢
  exact h

def row098 : Row :=
  ⟨330/23,620/43,(-417/2),797/40, ![33,14,1,28,26],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-14),1⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![13,14,0,1]], false⟩
theorem valid098 : row098.Valid := by decide +kernel
theorem piece098 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (330/23:ℝ) (620/43:ℝ) ∧
    (∫ x in (330/23:ℝ)..(620/43:ℝ), innerR 7 6 (3/40) x / x^3) = (1036693/558148800:ℝ) := by
  have h := row_integral row098 valid098
  norm_num [row098] at h ⊢
  exact h

def row099 : Row :=
  ⟨620/43,29/2,(-417/2),797/40, ![33,14,1,28,26],
   ![⟨0,0⟩,⟨(-1),3/40⟩,⟨(-14),1⟩,⟨1/2,0⟩],
   ![![14,14,1,1],![14,14,0,1],![13,14,0,1]], false⟩
theorem valid099 : row099.Valid := by decide +kernel
theorem piece099 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (620/43:ℝ) (29/2:ℝ) ∧
    (∫ x in (620/43:ℝ)..(29/2:ℝ), innerR 7 6 (3/40) x / x^3) = (2771489/1293121600:ℝ) := by
  have h := row_integral row099 valid099
  norm_num [row099] at h ⊢
  exact h

theorem block004 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (280/23:ℝ) (29/2:ℝ) ∧
    (∫ x in (280/23:ℝ)..(29/2:ℝ), innerR 7 6 (3/40) x / x^3) = (7502365765669/1134439676370000:ℝ) := by
  have h := piece080
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (460/37:ℝ) (25/2:ℝ)
    (-(577181/82947200:ℝ)) (-(18071/10580000:ℝ)) h piece081
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (25/2:ℝ) (540/43:ℝ)
    (-(781367/90160000:ℝ)) (-(4637/3240000:ℝ)) h piece082
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (540/43:ℝ) (290/23:ℝ)
    (-(2949701/292118400:ℝ)) (-(5299/4359744:ℝ)) h piece083
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (290/23:ℝ) (480/37:ℝ)
    (-(34312311/3032982400:ℝ)) (-(194773/24220800:ℝ)) h piece084
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (480/37:ℝ) (13:ℝ)
    (-(1821793/94127040:ℝ)) (-(2137/3893760:ℝ)) h piece085
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (13:ℝ) (560/43:ℝ)
    (-(844302569/42419919360:ℝ)) (-(76327/105996800:ℝ)) h piece086
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (560/43:ℝ) (300/23:ℝ)
    (-(84120061/4078838400:ℝ)) (-(29209/47040000:ℝ)) h piece087
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (300/23:ℝ) (40/3:ℝ)
    (-(8665277339/407883840000:ℝ)) (-(1013/120000:ℝ)) h piece088
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (40/3:ℝ) (310/23:ℝ)
    (-(807233117/27192256000:ℝ)) (7749/1537600:ℝ) h piece089
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (310/23:ℝ) (580/43:ℝ)
    (-(644055530597/26131758016000:ℝ)) (91023/258624320:ℝ) h piece090
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (580/43:ℝ) (27/2:ℝ)
    (-(593899832023/24445838144000:ℝ)) (397021/980942400:ℝ) h piece091
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (27/2:ℝ) (500/37:ℝ)
    (-(14680696612163/614517793344000:ℝ)) (171457/364500000:ℝ) h piece092
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (500/37:ℝ) (320/23:ℝ)
    (-(66627934484581/2844989784000000:ℝ)) (1788927/128000000:ℝ) h piece093
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (320/23:ℝ) (600/43:ℝ)
    (-(17194482873523/1820793461760000:ℝ)) (65441/46080000:ℝ) h piece094
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (600/43:ℝ) (14:ℝ)
    (-(228260371189/28449897840000:ℝ)) (28787/17640000:ℝ) h piece095
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (14:ℝ) (520/37:ℝ)
    (-(25976074981/4064271120000:ℝ)) (9179/6624800:ℝ) h piece096
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (520/37:ℝ) (330/23:ℝ)
    (-(1851378529171/369848671920000:ℝ)) (19941/2617472:ℝ) h piece097
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (330/23:ℝ) (620/43:ℝ)
    (1124234087521/430304704830000:ℝ) (1036693/558148800:ℝ) h piece098
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (280/23:ℝ) (620/43:ℝ) (29/2:ℝ)
    (21682779182789/4850707581720000:ℝ) (2771489/1293121600:ℝ) h piece099
  norm_num at h
  exact h

end SplitData
