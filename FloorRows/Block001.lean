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

def row173 : Row :=
  ⟨1000/43,70/3,(-1065/2),829/40, ![53,23,1,46,43],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-23),1⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,23,1,2],![22,23,1,2]], false⟩
theorem valid173 : row173.Valid := by decide +kernel
theorem piece173 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1000/43:ℝ) (70/3:ℝ) ∧
    (∫ x in (1000/43:ℝ)..(70/3:ℝ), innerR 7 6 (3/40) x / x^3) = (-(11953/39200000:ℝ)) := by
  have h := row_integral row173 valid173
  norm_num [row173] at h ⊢
  exact h

def row174 : Row :=
  ⟨70/3,540/23,(-529),823/40, ![53,23,1,46,43],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-23),1⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,23,1,2],![22,23,1,2]], true⟩
theorem valid174 : row174.Valid := by decide +kernel
theorem piece174 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (70/3:ℝ) (540/23:ℝ) ∧
    (∫ x in (70/3:ℝ)..(540/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(383/714420:ℝ)) := by
  have h := row_integral row174 valid174
  norm_num [row174] at h ⊢
  exact h

def row175 : Row :=
  ⟨540/23,47/2,(-502),777/40, ![54,23,1,46,43],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-23),1⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,23,1,2],![22,23,1,2]], false⟩
theorem valid175 : row175.Valid := by decide +kernel
theorem piece175 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (540/23:ℝ) (47/2:ℝ) ∧
    (∫ x in (540/23:ℝ)..(47/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(98809/1288288800:ℝ)) := by
  have h := row_integral row175 valid175
  norm_num [row175] at h ⊢
  exact h

def row176 : Row :=
  ⟨47/2,1020/43,(-1051/2),817/40, ![54,23,1,47,43],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨24,(-1)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,23,1,2],![23,24,1,2]], true⟩
theorem valid176 : row176.Valid := by decide +kernel
theorem piece176 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (47/2:ℝ) (1020/43:ℝ) ∧
    (∫ x in (47/2:ℝ)..(1020/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(6676847/9192974400:ℝ)) := by
  have h := row_integral row176 valid176
  norm_num [row176] at h ⊢
  exact h

def row177 : Row :=
  ⟨1020/43,880/37,(-1051/2),817/40, ![54,23,1,47,43],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨24,(-1)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,23,1,2],![23,24,1,2]], true⟩
theorem valid177 : row177.Valid := by decide +kernel
theorem piece177 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1020/43:ℝ) (880/37:ℝ) ∧
    (∫ x in (1020/43:ℝ)..(880/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(305033/1611371520:ℝ)) := by
  have h := row_integral row177 valid177
  norm_num [row177] at h ⊢
  exact h

def row178 : Row :=
  ⟨880/37,550/23,(-1271/2),501/20, ![54,23,1,47,44],
   ![⟨0,0⟩,⟨24,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,24,1,1],![23,24,1,2]], true⟩
theorem valid178 : row178.Valid := by decide +kernel
theorem piece178 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (880/37:ℝ) (550/23:ℝ) ∧
    (∫ x in (880/37:ℝ)..(550/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(28119/77440000:ℝ)) := by
  have h := row_integral row178 valid178
  norm_num [row178] at h ⊢
  exact h

def row179 : Row :=
  ⟨550/23,24,(-608),239/10, ![55,23,1,47,44],
   ![⟨0,0⟩,⟨24,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![23,23,1,1],![23,24,1,1],![23,24,1,2]], false⟩
theorem valid179 : row179.Valid := by decide +kernel
theorem piece179 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (550/23:ℝ) (24:ℝ) ∧
    (∫ x in (550/23:ℝ)..(24:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2441/10890000:ℝ)) := by
  have h := row_integral row179 valid179
  norm_num [row179] at h ⊢
  exact h

def row180 : Row :=
  ⟨24,1040/43,(-632),461/20, ![55,24,1,48,44],
   ![⟨0,0⟩,⟨(-24),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![23,24,1,1],![23,24,1,2]], true⟩
theorem valid180 : row180.Valid := by decide +kernel
theorem piece180 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (24:ℝ) (1040/43:ℝ) ∧
    (∫ x in (24:ℝ)..(1040/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1241/1216800:ℝ)) := by
  have h := row_integral row180 valid180
  norm_num [row180] at h ⊢
  exact h

def row181 : Row :=
  ⟨1040/43,900/37,(-554),793/40, ![55,24,1,48,44],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-24),1⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![23,24,1,2]], true⟩
theorem valid181 : row181.Valid := by decide +kernel
theorem piece181 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1040/43:ℝ) (900/37:ℝ) ∧
    (∫ x in (1040/43:ℝ)..(900/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(1552463/2190240000:ℝ)) := by
  have h := row_integral row181 valid181
  norm_num [row181] at h ⊢
  exact h

def row182 : Row :=
  ⟨900/37,560/23,(-599),867/40, ![55,24,1,48,45],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-24),1⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![23,24,1,2]], true⟩
theorem valid182 : row182.Valid := by decide +kernel
theorem piece182 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (900/37:ℝ) (560/23:ℝ) ∧
    (∫ x in (900/37:ℝ)..(560/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(148109/1270080000:ℝ)) := by
  have h := row_integral row182 valid182
  norm_num [row182] at h ⊢
  exact h

def row183 : Row :=
  ⟨560/23,49/2,(-571),821/40, ![56,24,1,48,45],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-24),1⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![23,24,1,2]], false⟩
theorem valid183 : row183.Valid := by decide +kernel
theorem piece183 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (560/23:ℝ) (49/2:ℝ) ∧
    (∫ x in (560/23:ℝ)..(49/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(895/1229312:ℝ)) := by
  have h := row_integral row183 valid183
  norm_num [row183] at h ⊢
  exact h

def row184 : Row :=
  ⟨49/2,1060/43,(-1191/2),861/40, ![56,24,1,49,45],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨25,(-1)⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![24,25,1,2]], true⟩
theorem valid184 : row184.Valid := by decide +kernel
theorem piece184 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (49/2:ℝ) (1060/43:ℝ) ∧
    (∫ x in (49/2:ℝ)..(1060/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(7310199/10791054400:ℝ)) := by
  have h := row_integral row184 valid184
  norm_num [row184] at h ⊢
  exact h

def row185 : Row :=
  ⟨1060/43,570/23,(-1191/2),861/40, ![56,24,1,49,45],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨25,(-1)⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![24,25,1,2]], true⟩
theorem valid185 : row185.Valid := by decide +kernel
theorem piece185 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1060/43:ℝ) (570/23:ℝ) ∧
    (∫ x in (1060/43:ℝ)..(570/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2689427/4867435200:ℝ)) := by
  have h := row_integral row185 valid185
  norm_num [row185] at h ⊢
  exact h

def row186 : Row :=
  ⟨570/23,920/37,(-567),163/8, ![57,24,1,49,45],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨25,(-1)⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,24,1,2],![24,25,1,2]], false⟩
theorem valid186 : row186.Valid := by decide +kernel
theorem piece186 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (570/23:ℝ) (920/37:ℝ) ∧
    (∫ x in (570/23:ℝ)..(920/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(120701/366660480:ℝ)) := by
  have h := row_integral row186 valid186
  norm_num [row186] at h ⊢
  exact h

def row187 : Row :=
  ⟨920/37,25,(-682),25, ![57,24,1,49,46],
   ![⟨0,0⟩,⟨25,(-1)⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![24,24,1,1],![24,25,1,1],![24,25,1,2]], false⟩
theorem valid187 : row187.Valid := by decide +kernel
theorem piece187 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (920/37:ℝ) (25:ℝ) ∧
    (∫ x in (920/37:ℝ)..(25:ℝ), innerR 7 6 (3/40) x / x^3) = (-(10829/21160000:ℝ)) := by
  have h := row_integral row187 valid187
  norm_num [row187] at h ⊢
  exact h

def row188 : Row :=
  ⟨25,1080/43,(-707),483/20, ![57,25,1,50,46],
   ![⟨0,0⟩,⟨(-25),1⟩,⟨2,(-3/40)⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![24,25,1,1],![24,25,1,2]], true⟩
theorem valid188 : row188.Valid := by decide +kernel
theorem piece188 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (25:ℝ) (1080/43:ℝ) ∧
    (∫ x in (25:ℝ)..(1080/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(43897/58320000:ℝ)) := by
  have h := row_integral row188 valid188
  norm_num [row188] at h ⊢
  exact h

def row189 : Row :=
  ⟨1080/43,580/23,(-626),837/40, ![57,25,1,50,46],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-25),1⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![24,25,1,2]], true⟩
theorem valid189 : row189.Valid := by decide +kernel
theorem piece189 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1080/43:ℝ) (580/23:ℝ) ∧
    (∫ x in (1080/43:ℝ)..(580/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(61843/98094240:ℝ)) := by
  have h := row_integral row189 valid189
  norm_num [row189] at h ⊢
  exact h

def row190 : Row :=
  ⟨580/23,940/37,(-597),791/40, ![58,25,1,50,46],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-25),1⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![24,25,1,2]], false⟩
theorem valid190 : row190.Valid := by decide +kernel
theorem piece190 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (580/23:ℝ) (940/37:ℝ) ∧
    (∫ x in (580/23:ℝ)..(940/37:ℝ), innerR 7 6 (3/40) x / x^3) = (-(41561/37155380:ℝ)) := by
  have h := row_integral row190 valid190
  norm_num [row190] at h ⊢
  exact h

def row191 : Row :=
  ⟨940/37,51/2,(-644),173/8, ![58,25,1,50,47],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨(-25),1⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![24,25,1,2]], false⟩
theorem valid191 : row191.Valid := by decide +kernel
theorem piece191 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (940/37:ℝ) (51/2:ℝ) ∧
    (∫ x in (940/37:ℝ)..(51/2:ℝ), innerR 7 6 (3/40) x / x^3) = (-(2467801/4596487200:ℝ)) := by
  have h := row_integral row191 valid191
  norm_num [row191] at h ⊢
  exact h

def row192 : Row :=
  ⟨51/2,1100/43,(-1339/2),181/8, ![58,25,1,51,47],
   ![⟨0,0⟩,⟨2,(-3/40)⟩,⟨26,(-1)⟩,⟨1/2,0⟩],
   ![![25,25,1,1],![25,25,1,2],![25,26,1,2]], true⟩
theorem valid192 : row192.Valid := by decide +kernel
theorem piece192 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (51/2:ℝ) (1100/43:ℝ) ∧
    (∫ x in (51/2:ℝ)..(1100/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(5636239/12588840000:ℝ)) := by
  have h := row_integral row192 valid192
  norm_num [row192] at h ⊢
  exact h

theorem block001 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1000/43:ℝ) (1100/43:ℝ) ∧
    (∫ x in (1000/43:ℝ)..(1100/43:ℝ), innerR 7 6 (3/40) x / x^3) =
      (-(177871222612077391/16857950255546400000:ℝ)) := by
  have h := piece173
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (70/3:ℝ) (540/23:ℝ)
    (-(11953/39200000:ℝ)) (-(383/714420:ℝ)) h piece174
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (540/23:ℝ) (47/2:ℝ)
    (-(3433391/4082400000:ℝ)) (-(98809/1288288800:ℝ)) h piece175
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (47/2:ℝ) (1020/43:ℝ)
    (-(306519397/334000800000:ℝ)) (-(6676847/9192974400:ℝ)) h piece176
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (1020/43:ℝ) (880/37:ℝ)
    (-(3376404239/2053749600000:ℝ)) (-(305033/1611371520:ℝ)) h piece177
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (880/37:ℝ) (550/23:ℝ)
    (-(6305698559/3439497600000:ℝ)) (-(28119/77440000:ℝ)) h piece178
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (550/23:ℝ) (24:ℝ)
    (-(944325493/429937200000:ℝ)) (-(2441/10890000:ℝ)) h piece179
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (24:ℝ) (1040/43:ℝ)
    (-(94608743/39085200000:ℝ)) (-(1241/1216800:ℝ)) h piece180
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (1040/43:ℝ) (900/37:ℝ)
    (-(22725646067/6605398800000:ℝ)) (-(1552463/2190240000:ℝ)) h piece181
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (900/37:ℝ) (560/23:ℝ)
    (-(12649668799/3048645600000:ℝ)) (-(148109/1270080000:ℝ)) h piece182
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (560/23:ℝ) (49/2:ℝ)
    (-(60690855377/14227012800000:ℝ)) (-(895/1229312:ℝ)) h piece183
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (49/2:ℝ) (1060/43:ℝ)
    (-(1740696214549/348561813600000:ℝ)) (-(7310199/10791054400:ℝ)) h piece184
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (1060/43:ℝ) (570/23:ℝ)
    (-(113324400155809/19981839477600000:ℝ)) (-(2689427/4867435200:ℝ)) h piece185
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (570/23:ℝ) (920/37:ℝ)
    (-(15982836178861/2567975810400000:ℝ)) (-(120701/366660480:ℝ)) h piece186
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (920/37:ℝ) (25:ℝ)
    (-(468532192602301/71497852826400000:ℝ)) (-(10829/21160000:ℝ)) h piece187
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (25:ℝ) (1080/43:ℝ)
    (-(21961846477607/3108602296800000:ℝ)) (-(43897/58320000:ℝ)) h piece188
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (1080/43:ℝ) (580/23:ℝ)
    (-(656145000739199/83932262013600000:ℝ)) (-(61843/98094240:ℝ)) h piece189
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (580/23:ℝ) (940/37:ℝ)
    (-(22085895206846717/2614334531608800000:ℝ)) (-(41561/37155380:ℝ)) h piece190
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (940/37:ℝ) (51/2:ℝ)
    (-(40533803018921231/4237024930538400000:ℝ)) (-(2467801/4596487200:ℝ)) h piece191
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (1000/43:ℝ) (51/2:ℝ) (1100/43:ℝ)
    (-(263227428069888697/26053195849480800000:ℝ)) (-(5636239/12588840000:ℝ)) h piece192
  norm_num at h
  exact h

end U66Data
