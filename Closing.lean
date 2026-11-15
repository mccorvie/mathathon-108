import DataRows.Block000
import DataRows.Block001
import DataRows.Block002
import DataRows.Block003
import DataRows.Block004
import DataRows.Block005
import DataRows.Block006
import DataRows.Block007
import SplitTail

/-!
E609, Codex lane C. PROOF-DRAFT until final gate. A re-derivation of
Fauzan's theorem using Firsching formalisation, Paul-Lez metadata, Apache-2.0.
The prefix is checked from the complete rational floor/gamma/max certificate.
The upper tail is the parent's attributed standalone second-primitive adapter.
No old numerical chunk module enters this import closure.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set Mathathon.P108
noncomputable section
namespace SplitClosing

theorem prefix21_statement : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume 3 21 ∧
    (∫ x in (3:ℝ)..21, innerR 7 6 (3/40) x / x^3) = (1408666529353495546850141/2479235603396797365120000:ℝ) :=
      by
  have h := SplitData.block000
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (120/23:ℝ) (15/2:ℝ)
    (10638527/22176000:ℝ)
    (1536908029/19603584000:ℝ) h SplitData.block001
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (15/2:ℝ) (420/43:ℝ)
    (142095661/254592000:ℝ)
    (-(1012095961/66853248000:ℝ)) h SplitData.block002
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (420/43:ℝ) (280/23:ℝ)
    (707864960911/1303638336000:ℝ)
    (-(1323874307579/26456189760000:ℝ)) h SplitData.block003
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (280/23:ℝ) (29/2:ℝ)
    (55426887071363/112438806480000:ℝ)
    (7502365765669/1134439676370000:ℝ) h SplitData.block004
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (29/2:ℝ) (620/37:ℝ)
    (704386958141411/1410001021520000:ℝ)
    (224727991002371393/5140650573805824000:ℝ) h SplitData.block005
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (620/37:ℝ) (820/43:ℝ)
    (143974498445671176211/265009400270334720000:ℝ)
    (12950950551423942019/638203380967536384000:ℝ) h SplitData.block006
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3)
    (3:ℝ) (820/43:ℝ) (21:ℝ)
    (174123087934668374996129/308962491608719428480000:ℝ)
    (1552446518659/336590045792000:ℝ) h SplitData.block007
  norm_num at h
  exact h

theorem prefix21_integral :
    (∫ x in (3:ℝ)..21, innerR 7 6 (3/40) x / x^3) = (1408666529353495546850141/2479235603396797365120000:ℝ) :=
  prefix21_statement.2

theorem closing_neg :
    Mathathon.P108.thetaPkg 5 6 (3/40) 1000000 (-2650371/2000000) < 0 := by
  have hA : thetaPkg 7 6 (3/40) 1000000 0 < (2650371/2000000:ℝ)+751/768 := by
    have ht := SplitTail.tail21_upper
    have hfirst := innerR_div_intervalIntegrable 7 6 (3/40) 21 (by norm_num)
    have hlast := innerR_div_intervalIntegrable 7 6 (3/40) 1000000 (by norm_num)
    have htail := hfirst.symm.trans hlast
    have hc := intervalIntegral.integral_add_adjacent_intervals hfirst htail
    unfold thetaPkg
    rw [Iout_7_6,←hc,prefix21_integral]
    norm_num at ht ⊢
    linarith
  have hs := theta_sstep_7_6 1000000 0 (by norm_num)
  unfold thetaPkg at hA hs ⊢
  linarith

#print axioms prefix21_statement
#print axioms prefix21_integral
#print axioms closing_neg
#check closing_neg
end SplitClosing
