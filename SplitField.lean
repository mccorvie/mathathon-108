import SplitFieldCore
import NumericCertificates

/-!
PROOF-DRAFT selected129-cell original16 certificate, Codex gpt-6.1-sol lane C.
Fauzan re-derivation reusing Firsching mo271/Zeta5@be1c0d82;
Comparator metadata Paul-Lez, Apache-2.0. All numeric soundness hypotheses
are discharged by kernel-checked CPrimitive data certificates. No old
point/interval proof chunks, native evaluation, or assumed field bound.
-/
set_option autoImplicit false
set_option maxRecDepth 200000
namespace CSplitField
open CField CFieldData

theorem numeric_sound : Sound numeric := by
  constructor
  · intro i hi
    have hm : sr numeric i ∈ CPrimitive.sqrtRows := getD_mem CPrimitive.sqrtRows i hi
    exact CPrimitive.sqrt_sound (CPrimitive.all_sqrt_ok hm)
  · intro i hi
    have hm : lr numeric i ∈ CPrimitive.logRows := getD_mem CPrimitive.logRows i hi
    exact CPrimitive.log_sound (CPrimitive.all_log_ok hm)
  · intro i hi
    have hi' : i < CPrimitive.atanRows.length := hi
    have hr : CPrimitive.atanRows[i]? = some (ar numeric i) := by
      simp only [ar,numeric,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi',Option.getD_some]
    exact CPrimitive.atan_sound (CPrimitive.all_atan_ok i hi) hr

/-- PROOF-DRAFT: actual unchanged original16 model, threshold -32999/5000. -/
theorem local_field_certificate : U48.LocalFieldStatement ((-32999:ℝ)/5000) :=
  local_field_of_numeric_sound numeric_sound

#check local_field_certificate
#print axioms numeric_sound
#print axioms local_field_certificate
end CSplitField
