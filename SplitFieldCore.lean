import FieldCertificates
import AnalyticInterface

/-!
PROOF-DRAFT generic selected field assembly, Codex gpt-6.1-sol lane C.
Fauzan re-derivation reusing Firsching mo271/Zeta5@be1c0d82;
Comparator metadata Paul-Lez, Apache-2.0. The sole premise below is the
exact indexed primitive-table soundness, discharged in SplitField.lean.
No old point/interval certificate is imported.
-/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CSplitField
open CField CFieldData CFieldCert

theorem getD_mem {α : Type*} [Inhabited α] (xs : List α) (i : ℕ) (hi : i < xs.length) :
    xs.getD i default ∈ xs := by
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using
    (List.getElem_mem hi : xs[i] ∈ xs)

/-- PROOF-DRAFT: every checked U row consumes the same primitive soundness table. -/
theorem all_U_real (hd : Sound numeric) :
    ∀ i, i < uRows.length → Apery.Uρ ((ug uRows i).point:ℝ) ≤ ((ug uRows i).upper:ℝ) := by
  intro i hi
  apply U_sound numeric hd
  exact all_u_ok _ (getD_mem uRows i hi)

/-- PROOF-DRAFT: every checked V row consumes the same primitive soundness table. -/
theorem all_V_real (hd : Sound numeric) :
    ∀ i, i < vRows.length → ((vg vRows i).lower:ℝ) ≤ Apery.Vfield ((vg vRows i).point:ℝ) := by
  intro i hi
  apply V_sound numeric hd
  exact all_v_ok _ (getD_mem vRows i hi)

/-- PROOF-DRAFT: selected129-cell certificate, with its sole primitive premise explicit. -/
theorem local_field_of_numeric_sound (hd : Sound numeric) :
    U48.LocalFieldStatement ((-32999:ℝ)/5000) := by
  have hcritical := critical_sound numeric hd critical critical_ok
  have hcells : ∀ c ∈ cells, CellClaim tau c := by
    intro c hc
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
    exact cell_sound tau r.cell (all_cell_ok r hr)
      (route_sound uRows vRows critical (all_U_real hd) (all_V_real hd) hcritical r (all_route_ok r hr))
  have hcover := cover_sound tau 0 2 cells chain_ok hcells
  intro t ht ht2
  have h := hcover t (by simpa using ht) (by simpa using ht2)
  simpa [tau] using h

#print axioms local_field_of_numeric_sound
end CSplitField
