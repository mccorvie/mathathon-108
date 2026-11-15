import FieldAverage.OneLog

/-! E211/U16. All new mathematical declarations have status PROOF-DRAFT.
The whole E201 analytic result remains CONJECTURE. -/

noncomputable section
namespace U16
open Real MeasureTheory

def primitive (b u : ℝ) : ℝ :=
  2*u*Real.log ((u+Real.sqrt (u^2+b))/2)-2*Real.sqrt (u^2+b)

def T (a b : ℝ) : ℝ :=
  2*a*Real.log ((a+Real.sqrt (a^2+b))/2)-2*Real.sqrt (a^2+b)+2*Real.sqrt b

lemma root_sum_pos {b : ℝ} (hb : 0<b) (u : ℝ) :
    0<u+Real.sqrt (u^2+b) := by
  have h := Real.lt_sqrt_of_sq_lt (show (-u)^2<u^2+b by nlinarith)
  linarith

lemma primitive_deriv {b : ℝ} (hb : 0<b) (u : ℝ) :
    HasDerivAt (primitive b) (2*Real.log ((u+Real.sqrt (u^2+b))/2)) u := by
  have hq : 0<u^2+b := by nlinarith [sq_nonneg u]
  have hs := ((hasDerivAt_pow 2 u).add_const b).sqrt hq.ne'
  have hi := ((hasDerivAt_id u).add hs).div_const 2
  have hl := hi.log (show (u+Real.sqrt (u^2+b))/2≠0 by
    exact ne_of_gt (div_pos (root_sum_pos hb u) (by norm_num)))
  have hp := (((hasDerivAt_id u).mul hl).const_mul 2).sub (hs.const_mul 2)
  change HasDerivAt (fun x => 2*(x*Real.log ((x+Real.sqrt (x^2+b))/2))-2*Real.sqrt (x^2+b)) _ u at hp
  have hf : (fun x => 2*(x*Real.log ((x+Real.sqrt (x^2+b))/2))-2*Real.sqrt (x^2+b))=primitive b := by
    funext x
    unfold primitive
    ring
  rw [hf] at hp
  have hsn : Real.sqrt (u^2+b)≠0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hsum : u+Real.sqrt (u^2+b)≠0 := (root_sum_pos hb u).ne'
  convert hp using 1
  dsimp only [id_eq,Pi.add_apply]
  norm_num
  field_simp
  ring

lemma log_root_continuous {b : ℝ} (hb : 0<b) :
    Continuous (fun u : ℝ => 2*Real.log ((u+Real.sqrt (u^2+b))/2)) := by
  apply Continuous.const_mul
  apply Continuous.log
  · fun_prop
  · intro u
    exact ne_of_gt (div_pos (root_sum_pos hb u) (by norm_num))

/-- PROOF-DRAFT: the outer u-integral, without any Fubini swap. -/
theorem integral_log_root {b : ℝ} (hb : 0<b) (a : ℝ) :
    (∫ u in (0:ℝ)..a, 2*Real.log ((u+Real.sqrt (u^2+b))/2))=T a b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => primitive_deriv hb u) ((log_root_continuous hb).intervalIntegrable 0 a)
  convert h using 1
  simp [primitive,T]

end U16
#check U16.integral_log_root
#print axioms U16.integral_log_root
