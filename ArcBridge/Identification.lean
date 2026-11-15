import ArcBridge.ArcsinePotential
import ArcBridge.UTranslation

/-!
E209 / [108/U14], Codex, event work.
Every mathematical declaration in this file carries status PROOF-DRAFT.
This file identifies the prior-work angular integral with E207's explicit function.
It does not convert an angular integral to a Borel-measure integral.
-/

noncomputable section
namespace U14
open Real Set MeasureTheory
open Mathathon.P108.UTranslation

lemma omega_eq_closed {a b : ℝ} (hab : a<b) (t : ℝ) :
    Apery.Uω a b t = closedPotential a b t := by
  by_cases hm : a≤t ∧ t≤b
  · rw [Apery.Uω_of_mem hm.1 hm.2, closedPotential_of_mem hm.1 hm.2]
  · have hL : 0<b-a := sub_pos.mpr hab
    have harg : 1+2*intervalDistance a b t/(b-a) =
        |(t-(a+b)/2)/((b-a)/2)| := by
      rcases lt_or_ge t a with hta | hat
      · have hd : intervalDistance a b t=a-t := by
          unfold intervalDistance
          rw [max_eq_left (by linarith : t-b≤0),max_eq_left (by linarith : 0≤a-t)]
        rw [hd,abs_of_neg (div_neg_of_neg_of_pos (by linarith) (by linarith))]
        field_simp
        ring
      · have hbt : b<t := lt_of_not_ge (fun htb => hm ⟨hat,htb⟩)
        have hd : intervalDistance a b t=t-b := by
          unfold intervalDistance
          rw [max_eq_right (by linarith : 0≤t-b),max_eq_right (by linarith : a-t≤t-b)]
        rw [hd,abs_of_pos (div_pos (by linarith) (by linarith))]
        field_simp
        ring
    have hge : 1≤|(t-(a+b)/2)/((b-a)/2)| := by
      rw [←harg]
      have hd := intervalDistance_nonneg a b t
      have hp : 0≤2*intervalDistance a b t/(b-a) := by positivity
      linarith
    rw [Apery.Uω_eq_log_add hab,if_pos hge,closedPotential_eq_arcosh hab t,harg,
      Real.arcosh,sq_abs]

lemma omega_eq_arcosh {a b : ℝ} (hab : a<b) (t : ℝ) :
    Apery.Uω a b t=arcoshPotential a b t := by
  rw [omega_eq_closed hab,closedPotential_eq_arcosh hab]
  rfl

/-- PROOF-DRAFT: exact angular-integral identity, with the complex real-axis embedding. -/
theorem angular_integral_closed {a b : ℝ} (hab : a<b) (t : ℝ) :
    (∫ θ in (0:ℝ)..2*π,
      Real.log ‖(t:ℂ)-Apery.arcCurve ((a+b)/2) ((b-a)/2) θ‖) =
      2*π*closedPotential a b t := by
  rw [Apery.arc_potential_real hab t,omega_eq_closed hab]

/-- PROOF-DRAFT: the same angular-integral identity as a real logarithm of absolute value. -/
theorem angular_integral_real {a b : ℝ} (hab : a<b) (t : ℝ) :
    (∫ θ in (0:ℝ)..2*π,
      Real.log |t-((a+b)/2+(b-a)/2*Real.cos θ)|) =
      2*π*closedPotential a b t := by
  have h := angular_integral_closed hab t
  simpa only [Apery.arcCurve,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

/-- PROOF-DRAFT: normalized angular mean equals the explicit potential. -/
theorem angular_mean_closed {a b : ℝ} (hab : a<b) (t : ℝ) :
    (2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,
      Real.log |t-((a+b)/2+(b-a)/2*Real.cos θ)|) = closedPotential a b t := by
  rw [angular_integral_real hab t]
  have hp : (2*π:ℝ)≠0 := by positivity
  field_simp


/-- PROOF-DRAFT: the normalized real angular mean, with no Borel measure introduced. -/
def angularMean (a b t : ℝ) : ℝ :=
  (2*π)⁻¹*(∫ θ in (0:ℝ)..2*π,
      Real.log |t-((a+b)/2+(b-a)/2*Real.cos θ)|)

lemma angularMean_eq_closed {a b : ℝ} (hab : a<b) (t : ℝ) :
    angularMean a b t=closedPotential a b t := angular_mean_closed hab t

/-- PROOF-DRAFT: composition of the identified angular mean with E207's translation bound. -/
theorem angular_mean_translation {a b e : ℝ} (hab : a<b) (he : 0≤e) (x : ℝ) :
    |angularMean a b (x+e)-angularMean a b x| ≤ 2*Real.sqrt (e/(b-a)) := by
  rw [angularMean_eq_closed hab,angularMean_eq_closed hab]
  exact closedPotential_translation hab he x

end U14

#check U14.omega_eq_closed
#print axioms U14.omega_eq_closed
#check U14.angular_integral_real
#print axioms U14.angular_integral_real
#check U14.angular_mean_closed
#print axioms U14.angular_mean_closed

#check U14.angular_mean_translation
#print axioms U14.angular_mean_translation
