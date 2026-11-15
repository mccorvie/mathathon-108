import NumericBase
/- Author Codex GPT-6, U49/E244. PROOF-DRAFT.
Attribution: Firsching mo271/Zeta5@be1c0d82 TableCheck.lean:21-40,46-65;
Paul-Lez metadata, Apache-2.0. Only M0 generalized to T; original16 unchanged. -/
open Real Set Finset
namespace U49
open Apery
lemma check_left {l r U V T : ℝ} (hlr : l ≤ r) (hr : r ≤ aρ 1)
    (hU : Uρ l ≤ U) (hV : V ≤ Vfield r) (hnum : 2 * U - V ≤ T) :
    ∀ t, l ≤ t → t ≤ r → 0 < t → 2 * Uρ t - Vfield t ≤ T := by
  intro t ht1 ht2 ht0
  have h1 : Uρ t ≤ Uρ l := Uρ_antitoneOn (show l ∈ Iic (aρ 1) from hlr.trans hr)
    (show t ∈ Iic (aρ 1) from ht2.trans hr) ht1
  have h2 : Vfield r ≤ Vfield t := Vfield_antitoneOn ⟨ht0, ht2.trans (hr.trans aρ_one_lt_qm.le)⟩
    ⟨ht0.trans_le ht2, hr.trans aρ_one_lt_qm.le⟩ ht2
  linarith

/-- Intervals to the right of `b₁`: `Uρ` nondecreasing, `V` nondecreasing. -/
lemma check_right {l r U V T : ℝ} (hl : bρ 1 ≤ l) (hlr : l ≤ r)
    (hU : Uρ r ≤ U) (hV : V ≤ Vfield l) (hnum : 2 * U - V ≤ T) :
    ∀ t, l ≤ t → t ≤ r → 0 < t → 2 * Uρ t - Vfield t ≤ T := by
  intro t ht1 ht2 _
  have h1 : Uρ t ≤ Uρ r := Uρ_monotoneOn (show t ∈ Ici (bρ 1) from hl.trans ht1)
    (show r ∈ Ici (bρ 1) from hl.trans hlr) ht2
  have h2 : Vfield l ≤ Vfield t := Vfield_monotoneOn (show l ∈ Ici qp from qp_lt_bρ_one.le.trans hl)
    (show t ∈ Ici qp from qp_lt_bρ_one.le.trans (hl.trans ht1)) ht1
  linarith

lemma check_mid_left {U V T : ℝ} (hU : Uρmid ≤ U) (hV : V ≤ Vfield qm) (hnum : 2 * U - V ≤ T) :
    ∀ t, aρ 1 ≤ t → t ≤ qm → 0 < t → 2 * Uρ t - Vfield t ≤ T := by
  intro t ht1 ht2 _
  have ht : t ∈ Icc (aρ 1) qm := ⟨ht1, ht2⟩
  have hqmb : qm ≤ bρ 1 := by norm_num [bρ, table1]
  rw [Uρ_of_mem ht.1 (ht.2.trans hqmb)]
  have h2 : Vfield qm ≤ Vfield t := Vfield_antitoneOn ⟨aρ_one_pos.trans_le ht.1, ht.2⟩
    ⟨by norm_num, le_rfl⟩ ht.2
  change 2 * Uρmid - Vfield t ≤ T
  linarith

/-- The interval `[q₊, b₁]`. -/
lemma check_mid_right {U V T : ℝ} (hU : Uρmid ≤ U) (hV : V ≤ Vfield qp) (hnum : 2 * U - V ≤ T) :
    ∀ t, qp ≤ t → t ≤ bρ 1 → 0 < t → 2 * Uρ t - Vfield t ≤ T := by
  intro t ht1 ht2 _
  have ht : t ∈ Icc qp (bρ 1) := ⟨ht1, ht2⟩
  rw [Uρ_of_mem ((aρ_one_lt_qm.le.trans (by norm_num)).trans ht.1) ht.2]
  have h2 : Vfield qp ≤ Vfield t := Vfield_monotoneOn (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici qp from ht.1) ht.1
  change 2 * Uρmid - Vfield t ≤ T
  linarith

/-- PROOF-DRAFT: prior critical-bracket cell shape with an explicit numeric threshold. -/
lemma check_critical {U V T : ℝ} (hU : Uρmid ≤ U) (hV : V ≤ U49.Vstar)
    (hnum : 2 * U - V ≤ T) :
    ∀ t, qm ≤ t → t ≤ qp → 0 < t → 2 * Uρ t - Vfield t ≤ T := by
  intro t h1 h2 ht
  have hx := Uρ_of_mem (t := t) (by have := aρ_one_lt_qm; linarith)
    (by have := qp_lt_bρ_one; linarith)
  have hv := hV.trans (U49.Vfield_ge_Vstar h1 h2)
  rw [hx]
  change 2 * Uρmid - Vfield t ≤ T
  linarith
end U49
#print axioms U49.check_left
#print axioms U49.check_right
#print axioms U49.check_critical
