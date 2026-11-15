import DataRows.Block000
import DataRows.Block001
import DataRows.Block002
import DataRows.Block003
import DataRows.Block004
import DataRows.Block005
import DataRows.Block006
import DataRows.Block007
import FloorRows.Block000
import FloorRows.Block001
import FloorRows.Block002
import FloorRows.Block003
import FloorRows.Block004
import FloorRows.Block005
import FloorRows.Block006
import FloorRows.Block007
import FloorRows.Block008
/- U66/E261, Codex. All mathematical declarations PROOF-DRAFT until parent gate.
C prefix [3,21] recombined with newly kernel-checked [21,40] continuation. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set Mathathon.P108
noncomputable section
namespace U66
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


theorem prefix40_statement : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume 3 40 ∧
    (∫ x in (3:ℝ)..40, innerR 7 6 (3/40) x / x^3) = (326882988539734810408990473093139159093973/575013403956391564243577805652060235520000:ℝ) := by
  have h := prefix21_statement
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (21:ℝ) (1000/43:ℝ)
    (1408666529353495546850141/2479235603396797365120000:ℝ) (-(1265884887087383/320554374940800000:ℝ)) h U66Data.block000
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1000/43:ℝ) (1100/43:ℝ)
    (92675528827783344072207143/164249358725037825439200000:ℝ) (-(177871222612077391/16857950255546400000:ℝ)) h U66Data.block001
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1100/43:ℝ) (1200/43:ℝ)
    (2565045004841098333984603/4632674220449784820080000:ℝ) (924038669094175/258847283208818304:ℝ) h U66Data.block002
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1200/43:ℝ) (1120/37:ℝ)
    (8605337395838235415168151/15442357420360792417860000:ℝ) (368864833759259165087/29464613251102149120000:ℝ) h U66Data.block003
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1120/37:ℝ) (1400/43:ℝ)
    (10316090667443808848930601579187/18105572853688935296745423360000:ℝ) (19210226232986479165021/3235501353744520084224000:ℝ) h U66Data.block004
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1400/43:ℝ) (1500/43:ℝ)
    (378178245405388605224382045975898937/656888288704688261501220704924160000:ℝ) (210606056149584935207/148053555964500426240000:ℝ) h U66Data.block005
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1500/43:ℝ) (1600/43:ℝ)
    (16189135570865583339296944370191303/28050905301443444680322397669734400:ℝ) (-(2749509615197511216503/1172576699628975793152000:ℝ)) h U66Data.block006
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (1600/43:ℝ) (79/2:ℝ)
    (2970890418564046380376948437141204149039/5168659810843969116796204994625260544000:ℝ) (-(5004596518329758699088043/988968453237774924794880000:ℝ)) h U66Data.block007
  norm_num at h
  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) (3:ℝ) (79/2:ℝ) (40:ℝ)
    (25880538193367782917116981487194828207165867/45426058912554933575242646646512758606080000:ℝ) (-(454341/363475840:ℝ)) h U66Data.block008
  norm_num at h
  exact h
end U66
namespace U53
theorem innerIntegral40_value :
    (∫ x in (3:ℝ)..40, innerR 7 6 (3/40) x / x^3) = (326882988539734810408990473093139159093973/575013403956391564243577805652060235520000:ℝ) :=
  U66.prefix40_statement.2
end U53
#print axioms U66.prefix21_statement
#print axioms U66.prefix40_statement
#print axioms U53.innerIntegral40_value
