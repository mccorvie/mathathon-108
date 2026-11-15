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

def row313 : Row :=
  ⟨79/2,1700/43,(-3249/2),1477/40, ![90,39,2,79,73],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨40,(-1)⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![39,40,2,3]], true⟩
theorem valid313 : row313.Valid := by decide +kernel
theorem piece313 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (79/2:ℝ) (1700/43:ℝ) ∧
    (∫ x in (79/2:ℝ)..(1700/43:ℝ), innerR 7 6 (3/40) x / x^3) = (-(6742029/72145960000:ℝ)) := by
  have h := row_integral row313 valid313
  norm_num [row313] at h ⊢
  exact h

def row314 : Row :=
  ⟨1700/43,910/23,(-3249/2),1477/40, ![90,39,2,79,73],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨40,(-1)⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![39,40,2,3]], true⟩
theorem valid314 : row314.Valid := by decide +kernel
theorem piece314 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (1700/43:ℝ) (910/23:ℝ) ∧
    (∫ x in (1700/43:ℝ)..(910/23:ℝ), innerR 7 6 (3/40) x / x^3) = (-(7703211/95728360000:ℝ)) := by
  have h := row_integral row314 valid314
  norm_num [row314] at h ⊢
  exact h

def row315 : Row :=
  ⟨910/23,40,(-1579),1431/40, ![91,39,2,79,73],
   ![⟨0,0⟩,⟨3,(-3/40)⟩,⟨40,(-1)⟩,⟨1/2,0⟩],
   ![![39,39,2,2],![39,39,2,3],![39,40,2,3]], false⟩
theorem valid315 : row315.Valid := by decide +kernel
theorem piece315 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (910/23:ℝ) (40:ℝ) ∧
    (∫ x in (910/23:ℝ)..(40:ℝ), innerR 7 6 (3/40) x / x^3) = (-(5703/5299840:ℝ)) := by
  have h := row_integral row315 valid315
  norm_num [row315] at h ⊢
  exact h

theorem block008 : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (79/2:ℝ) (40:ℝ) ∧
    (∫ x in (79/2:ℝ)..(40:ℝ), innerR 7 6 (3/40) x / x^3) = (-(454341/363475840:ℝ)) := by
  have h := piece313
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (79/2:ℝ) (1700/43:ℝ) (910/23:ℝ)
    (-(6742029/72145960000:ℝ)) (-(7703211/95728360000:ℝ)) h piece314
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (79/2:ℝ) (910/23:ℝ) (40:ℝ)
    (-(179769/1033634420:ℝ)) (-(5703/5299840:ℝ)) h piece315
  norm_num at h
  exact h

end U66Data
