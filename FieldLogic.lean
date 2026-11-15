import Cells

/-!
PROOF-DRAFT, Codex gpt-6.1-sol lane C, 2026-11-14.
Fauzan re-derivation reusing Firsching mo271/Zeta5@be1c0d82;
Comparator metadata Paul-Lez, Apache-2.0. Generic real point/cell/cover
consumers reuse U49 NumericBase/Cells, attributed in their unchanged headers.
No old point or interval proof chunks are imported.
-/
set_option autoImplicit false
open Finset Polynomial Set
namespace CField

def aQ (j : ℕ) : ℚ := ((Apery.table1.getD (j - 1) (0,0,0)).1 : ℚ) / 10^12
def bQ (j : ℕ) : ℚ := ((Apery.table1.getD (j - 1) (0,0,0)).2.1 : ℚ) / 10^12
def cQ (j : ℕ) : ℚ := ((Apery.table1.getD (j - 1) (0,0,0)).2.2 : ℚ) / 10^12
def qmQ : ℚ := 59205077 / 10^10
def qpQ : ℚ := 59205079 / 10^10

@[simp] theorem aQ_cast (j : ℕ) : (aQ j : ℝ) = Apery.aρ j := by
  simp [aQ, Apery.aρ]
@[simp] theorem bQ_cast (j : ℕ) : (bQ j : ℝ) = Apery.bρ j := by
  simp [bQ, Apery.bρ]
@[simp] theorem cQ_cast (j : ℕ) : (cQ j : ℝ) = Apery.cρ j := by
  simp [cQ, Apery.cρ]
@[simp] theorem qmQ_cast : (qmQ : ℝ) = Apery.qm := by
  norm_num [qmQ, Apery.qm]
@[simp] theorem qpQ_cast : (qpQ : ℝ) = Apery.qp := by
  norm_num [qpQ, Apery.qp]

/-- PROOF-DRAFT: generic weighted component consumption for the fixed original16. -/
theorem potential_sum_upper (p : ℚ) (u : ℕ → ℚ)
    (h : ∀ j ∈ Finset.Icc 1 16, Apery.Uω (Apery.aρ j) (Apery.bρ j) p ≤ (u j : ℝ)) :
    Apery.Uρ p ≤ ((∑ j ∈ Finset.Icc 1 16, cQ j * u j : ℚ) : ℝ) := by
  unfold Apery.Uρ
  push_cast
  apply Finset.sum_le_sum
  intro j hj
  rw [cQ_cast]
  exact mul_le_mul_of_nonneg_left (h j hj) (by unfold Apery.cρ; positivity)

/-- PROOF-DRAFT: fixed aggregate can be weakened to the stored rational bound. -/
theorem potential_upper (p ub : ℚ) (u : ℕ → ℚ)
    (h : ∀ j ∈ Finset.Icc 1 16, Apery.Uω (Apery.aρ j) (Apery.bρ j) p ≤ (u j : ℝ))
    (hs : (∑ j ∈ Finset.Icc 1 16, cQ j * u j : ℚ) ≤ ub) :
    Apery.Uρ p ≤ (ub : ℝ) :=
  (potential_sum_upper p u h).trans (by exact_mod_cast hs)

/-- PROOF-DRAFT: the common inner endpoint is the constant middle potential. -/
theorem mid_upper {ub : ℝ} (h : Apery.Uρ (Apery.aρ 1) ≤ ub) : Apery.Uρmid ≤ ub := by
  have heq := Apery.Uρ_of_mem (t := Apery.aρ 1) le_rfl
    (show Apery.aρ 1 ≤ Apery.bρ 1 by norm_num [Apery.aρ, Apery.bρ, Apery.table1])
  rw [heq] at h
  exact h

/-- PROOF-DRAFT: generic signed mixed-endpoint critical-bracket consumption. -/
theorem critical_lower {slo shi l1 l2 A1 A2 : ℝ} (hslo : 0 < slo)
    (hsl : slo ≤ Real.sqrt Apery.qm) (hsh : Real.sqrt Apery.qp ≤ shi)
    (hl1 : l1 ≤ Real.log (1 + Apery.qm))
    (hl2 : Real.log (Apery.qp + (3/40)^2) ≤ l2)
    (ha1 : A1 ≤ Real.arctan (1/shi)) (ha2 : Real.arctan ((3/40)/slo) ≤ A2)
    (hneg : 3.14159265358979323846 + A1 - 6*A2 ≤ 0) :
    l1 - 6*(3/40)*l2 - 2 + 12*(3/40) +
      2*shi*(3.14159265358979323846 + A1 - 6*A2) ≤ U49.Vstar := by
  have hshi : 0 < shi := Apery.sqrt_qp_pos.trans_le hsh
  have h1 : Real.arctan (1/shi) ≤ Real.arctan (1/Real.sqrt Apery.qp) :=
    Real.arctan_strictMono.monotone
      (div_le_div_of_nonneg_left zero_le_one Apery.sqrt_qp_pos hsh)
  have h2 : Real.arctan ((3/40)/Real.sqrt Apery.qm) ≤ Real.arctan ((3/40)/slo) :=
    Real.arctan_strictMono.monotone
      (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 3/40) hslo hsl)
  have hP : 3.14159265358979323846 + A1 - 6*A2 ≤ Real.pi +
      Real.arctan (1/Real.sqrt Apery.qp) - 6*Real.arctan ((3/40)/Real.sqrt Apery.qm) := by
    linarith [Real.pi_gt_d20]
  have hprod : 2*shi*(3.14159265358979323846 + A1 - 6*A2) ≤
      2*Real.sqrt Apery.qp*(Real.pi + Real.arctan (1/Real.sqrt Apery.qp) -
        6*Real.arctan ((3/40)/Real.sqrt Apery.qm)) := by
    calc
      _ ≤ 2*Real.sqrt Apery.qp*(3.14159265358979323846 + A1 - 6*A2) :=
        mul_le_mul_of_nonpos_right (by linarith) hneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  unfold U49.Vstar
  have hL2 := mul_le_mul_of_nonneg_left hl2 (by norm_num : (0:ℝ) ≤ 6*(3/40))
  have hhead : l1 - 6*(3/40)*l2 - 2 + 12*(3/40) ≤
      Real.log (1+Apery.qm) - 6*(3/40)*Real.log (Apery.qp+(3/40)^2) - 2 + 12*(3/40) := by
    simpa only [add_comm] using
      add_le_add_right (sub_le_sub_right (sub_le_sub hl1 hL2) 2) (12*(3/40))
  exact add_le_add hhead hprod

structure Cell where
  left : ℚ
  right : ℚ
  upper : ℚ
  lower : ℚ
  kind : ℕ
  deriving DecidableEq, Repr, Inhabited

def CellOK (T : ℚ) (c : Cell) : Prop :=
  0 ≤ c.left ∧ c.left ≤ c.right ∧ 2*c.upper-c.lower ≤ T ∧
  match c.kind with
  | 0 => c.right ≤ aQ 1
  | 1 => bQ 1 ≤ c.left
  | 2 => aQ 1 ≤ c.left ∧ c.right ≤ qmQ
  | 3 => qpQ ≤ c.left ∧ c.right ≤ bQ 1
  | 4 => qmQ ≤ c.left ∧ c.right ≤ qpQ
  | _ => False

instance (T : ℚ) (c : Cell) : Decidable (CellOK T c) := by
  unfold CellOK
  split <;> infer_instance

def CellInputs (c : Cell) : Prop :=
  match c.kind with
  | 0 => Apery.Uρ c.left ≤ (c.upper : ℝ) ∧ (c.lower : ℝ) ≤ Apery.Vfield c.right
  | 1 => Apery.Uρ c.right ≤ (c.upper : ℝ) ∧ (c.lower : ℝ) ≤ Apery.Vfield c.left
  | 2 => Apery.Uρmid ≤ (c.upper : ℝ) ∧ (c.lower : ℝ) ≤ Apery.Vfield Apery.qm
  | 3 => Apery.Uρmid ≤ (c.upper : ℝ) ∧ (c.lower : ℝ) ≤ Apery.Vfield Apery.qp
  | 4 => Apery.Uρmid ≤ (c.upper : ℝ) ∧ (c.lower : ℝ) ≤ U49.Vstar
  | _ => False

def CellClaim (T : ℚ) (c : Cell) : Prop :=
  ∀ t : ℝ, (c.left : ℝ) < t → t ≤ (c.right : ℝ) →
    2*Apery.Uρ t-Apery.Vfield t ≤ (T : ℝ)

/-- PROOF-DRAFT: one generic case split consumes all numerical cell rows. -/
theorem cell_sound (T : ℚ) (c : Cell) (hOK : CellOK T c) (h : CellInputs c) :
    CellClaim T c := by
  rcases hOK with ⟨hl0,hlr,hnum,hregion⟩
  have hl0' : (0 : ℝ) ≤ c.left := by exact_mod_cast hl0
  have hlr' : (c.left : ℝ) ≤ c.right := by exact_mod_cast hlr
  have hnum' : 2*(c.upper : ℝ)-(c.lower : ℝ) ≤ (T : ℝ) := by exact_mod_cast hnum
  intro t ht1 ht2
  have ht : 0 < t := hl0'.trans_lt ht1
  rcases c with ⟨l,r,U,V,k⟩
  dsimp only at *
  match k with
  | 0 =>
    exact U49.check_left hlr' (by simpa using (show (r:ℝ) ≤ (aQ 1:ℝ) by exact_mod_cast hregion))
      h.1 h.2 hnum' t ht1.le ht2 ht
  | 1 =>
    exact U49.check_right (by simpa using (show (bQ 1:ℝ) ≤ (l:ℝ) by exact_mod_cast hregion))
      hlr' h.1 h.2 hnum' t ht1.le ht2 ht
  | 2 =>
    apply U49.check_mid_left h.1 h.2 hnum' t ?_ ?_ ht
    · have : (aQ 1:ℝ) ≤ l := by exact_mod_cast hregion.1
      simpa using this.trans ht1.le
    · have : (r:ℝ) ≤ qmQ := by exact_mod_cast hregion.2
      simpa using ht2.trans this
  | 3 =>
    apply U49.check_mid_right h.1 h.2 hnum' t ?_ ?_ ht
    · have : (qpQ:ℝ) ≤ l := by exact_mod_cast hregion.1
      simpa using this.trans ht1.le
    · have : (r:ℝ) ≤ bQ 1 := by exact_mod_cast hregion.2
      simpa using ht2.trans this
  | 4 =>
    apply U49.check_critical h.1 h.2 hnum' t ?_ ?_ ht
    · have : (qmQ:ℝ) ≤ l := by exact_mod_cast hregion.1
      simpa using this.trans ht1.le
    · have : (r:ℝ) ≤ qpQ := by exact_mod_cast hregion.2
      simpa using ht2.trans this
  | _+5 => exact False.elim hregion

def Chain (left right : ℚ) : List Cell → Prop
  | [] => left = right
  | c::cs => c.left = left ∧ Chain c.right right cs

instance (left right : ℚ) (cs : List Cell) : Decidable (Chain left right cs) := by
  induction cs generalizing left with
  | nil => exact inferInstanceAs (Decidable (left = right))
  | cons c cs ih =>
    change Decidable (c.left = left ∧ Chain c.right right cs)
    letI := ih c.right
    infer_instance

/-- PROOF-DRAFT: checked adjacency consumes the entire cover by one list induction. -/
theorem cover_sound (T left right : ℚ) (cs : List Cell) (hchain : Chain left right cs)
    (h : ∀ c ∈ cs, CellClaim T c) :
    ∀ t : ℝ, (left:ℝ) < t → t ≤ (right:ℝ) →
      2*Apery.Uρ t-Apery.Vfield t ≤ (T:ℝ) := by
  induction cs generalizing left with
  | nil =>
    intro t ht1 ht2
    change left = right at hchain
    subst left
    exact False.elim (not_lt_of_ge ht2 ht1)
  | cons c cs ih =>
    rcases hchain with ⟨hc,hchain⟩
    intro t ht1 ht2
    by_cases hright : t ≤ (c.right:ℝ)
    · exact h c (by simp) t (by simpa [hc] using ht1) hright
    · exact ih c.right hchain (fun c' hc' => h c' (by simp [hc'])) t
        (lt_of_not_ge hright) ht2

end CField
