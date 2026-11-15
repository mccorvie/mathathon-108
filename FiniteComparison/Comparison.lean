import FiniteComparison.Mixture

/-! E220/U25, Codex (GPT-6). Every new mathematical declaration has status PROOF-DRAFT.
The comparison class is finite nonnegative arcsine mixtures only. Whole E201 remains CONJECTURE. -/
noncomputable section
namespace U25
open MeasureTheory Set Real Finset
open Mathathon.P108.ArcMeasure
open Mathathon.P108.FiniteDuality
variable {ι : Type*} [Fintype ι]

def lower (a : ι→ℝ) : Fin 15⊕ι→ℝ := Sum.elim (fun _=>0) a
def upper (b : ι→ℝ) : Fin 15⊕ι→ℝ := Sum.elim U11.width b
def trial : Fin 15⊕ι→ℝ := Sum.elim U11.mass (fun _=>0)
def comparison (c : ι→ℝ) : Fin 15⊕ι→ℝ := Sum.elim (fun _=>0) c

lemma ends_lt (a b : ι→ℝ) (hab : ∀ i,a i<b i) (p : Fin 15⊕ι) :
    lower a p<upper b p := by
  cases p with
  | inl j => exact U20.width_pos j
  | inr i => exact hab i

lemma K_left_left (a b : ι→ℝ) (hab : ∀ i,a i<b i) (i j : Fin 15) :
    K (lower a) (upper b) (.inl i) (.inl j)=U20.kernel (U11.width i) (U11.width j) := by
  rw [←kernel_eq (lower a) (upper b) (ends_lt a b hab)]
  rfl

lemma K_left_right (a b : ι→ℝ) (hab : ∀ i,a i<b i) (i : Fin 15) (j : ι) :
    K (lower a) (upper b) (.inl i) (.inr j)=mutualEnergy 0 (U11.width i) (a j) (b j) := by
  rw [←kernel_eq (lower a) (upper b) (ends_lt a b hab)]
  rfl

lemma K_right_right (a b : ι→ℝ) (hab : ∀ i,a i<b i) (i j : ι) :
    K (lower a) (upper b) (.inr i) (.inr j)=K a b i j := by
  rw [←kernel_eq (lower a) (upper b) (ends_lt a b hab),←kernel_eq a b hab]
  rfl

lemma trial_quadratic (a b : ι→ℝ) (hab : ∀ i,a i<b i) :
    quadratic (K (lower a) (upper b)) (trial (ι:=ι))=U20.energy := by
  rw [U20.energy_eq_sum]
  unfold quadratic bilinear trial
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,K_left_left a b hab]

lemma comparison_quadratic (a b c : ι→ℝ) (hab : ∀ i,a i<b i) :
    quadratic (K (lower a) (upper b)) (comparison c)=quadratic (K a b) c := by
  unfold quadratic bilinear comparison
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,K_right_right a b hab]

/-- PROOF-DRAFT: finite arcsine comparison, relative to the actual explicit trial witness. -/
theorem finite_comparison_lower (a b c : ι→ℝ) (hab : ∀ i,a i<b i)
    (hc : ∀ i,0≤c i) (hmass : (∑ i,c i)=U11.lam)
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂rho a b c)-U16.V6 t≤H) :
    U20.integralWitness≤U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂rho a b c ∂rho a b c)+U11.C6 := by
  classical
  let V : Fin 15⊕ι→ℝ := Sum.elim (fun j=>U11.W (U11.width j))
    (fun i=>2*(∑ p,comparison c p*K (lower a) (upper b) (.inr i) p)-H)
  have hp : ∀ p,2*(∑ q,comparison c q*K (lower a) (upper b) p q)-V p≤H := by
    intro p
    cases p with
    | inl j =>
      simpa only [Fintype.sum_sum_type,comparison,Sum.elim_inl,Sum.elim_inr,
        zero_mul,Finset.sum_const_zero,zero_add,V,K_left_right a b hab] using
        trial_row a b c hab hc H hfield j
    | inr i =>
      change 2*(∑ q,comparison c q*K (lower a) (upper b) (.inr i) q)-
        (2*(∑ q,comparison c q*K (lower a) (upper b) (.inr i) q)-H)≤H
      linarith
  have ha : ∀ p : Fin 15⊕ι,0≤trial p := by
    intro p;cases p with
    | inl j => exact (U11.mass_pos j).le
    | inr i => exact le_refl _
  have hma : (∑ p : Fin 15⊕ι,trial p)=U11.lam := by
    simpa only [trial,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const_zero,add_zero] using U11.mass_sum
  have hmb : (∑ p : Fin 15⊕ι,comparison c p)=U11.lam := by
    simpa only [comparison,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const_zero,zero_add] using hmass
  have hdual := Mathathon.P108.ArcPairs.arcsine_weak_duality
    (fun p=>(lower a p+upper b p)/2) (fun p=>(upper b p-lower a p)/2)
    (fun p=>by linarith [ends_lt a b hab p])
    trial (comparison c) V U11.lam H ha hma hmb hp
  change quadratic (K (lower a) (upper b)) trial-(∑ p,trial p*V p)≤
    U11.lam*H-quadratic (K (lower a) (upper b)) (comparison c) at hdual
  have hV : (∑ p,trial p*V p)=∑ j : Fin 15,U11.mass j*U11.W (U11.width j) := by
    simp only [trial,V,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,
      Finset.sum_const_zero,add_zero]
  rw [trial_quadratic a b hab,comparison_quadratic a b c hab,hV] at hdual
  rw [energy_rho a b c hab hc]
  unfold U20.integralWitness
  rw [U20.sigma_field_integral]
  linarith

/-- PROOF-DRAFT: every admissible finite nonnegative arcsine mixture has the desired strict floor. -/
theorem finite_comparison_gt (a b c : ι→ℝ) (_ha : ∀ i,0≤a i) (hab : ∀ i,a i<b i)
    (hc : ∀ i,0≤c i) (hmass : (∑ i,c i)=U11.lam)
    (H : ℝ) (hfield : ∀ t,0≤t→2*(∫ y,Real.log |t-y| ∂rho a b c)-U16.V6 t≤H) :
    (-139:ℝ)/100<U11.lam*H-
      (∫ x,∫ y,Real.log |x-y| ∂rho a b c ∂rho a b c)+U11.C6 := by
  exact U20.integralWitness_gt.trans_le (finite_comparison_lower a b c hab hc hmass H hfield)

end U25
#print axioms U25.finite_comparison_gt
