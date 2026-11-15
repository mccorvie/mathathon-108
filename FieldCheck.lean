import FieldLogic
import Primitive

/-!
PROOF-DRAFT generic field checker, Codex gpt-6.1-sol, lane C.
Fauzan re-derivation reusing Firsching mo271/Zeta5@be1c0d82;
Comparator metadata Paul-Lez, Apache-2.0. Primitive proofs are provided
by CPrimitive; point and cover data do not assume desired real inequalities.
-/
set_option autoImplicit false
open Finset
namespace CField

@[simp] theorem piLo_cast : (CPrimitive.piLo : ℝ) = 3.14159265358979323846 := by
  norm_num [CPrimitive.piLo]

structure Tables where
  sq : List CPrimitive.SqrtRow
  logs : List CPrimitive.LogRow
  ats : List CPrimitive.AtanRow

def sr (d : Tables) (i : ℕ) : CPrimitive.SqrtRow := d.sq.getD i default
def lr (d : Tables) (i : ℕ) : CPrimitive.LogRow := d.logs.getD i default
def ar (d : Tables) (i : ℕ) : CPrimitive.AtanRow := d.ats.getD i default

structure Sound (d : Tables) : Prop where
  sqrt : ∀ i, i < d.sq.length →
    CPrimitive.bound (sr d i).lower ((sr d i).bound : ℝ) (Real.sqrt ((sr d i).input : ℝ))
  log : ∀ i, i < d.logs.length →
    CPrimitive.bound (lr d i).lower ((lr d i).bound : ℝ) (Real.log ((lr d i).input : ℝ))
  atan : ∀ i, i < d.ats.length →
    CPrimitive.bound (ar d i).lower ((ar d i).bound : ℝ) (Real.arctan ((ar d i).input : ℝ))

structure Term where
  side : ℕ
  sqrtId : ℕ
  logId : ℕ
  deriving DecidableEq, Repr, Inhabited

def TermOK (d : Tables) (a b p : ℚ) (r : Term) : Prop :=
  r.logId < d.logs.length ∧ (lr d r.logId).lower = false ∧
  if r.side = 0 then
    a ≤ p ∧ p ≤ b ∧ (lr d r.logId).input = (b-a)/4
  else
    r.sqrtId < d.sq.length ∧ (sr d r.sqrtId).lower = false ∧ a < b ∧
      (sr d r.sqrtId).input = (p-a)*(p-b) ∧
    if r.side = 1 then
      p ≤ a ∧ (lr d r.logId).input = ((a+b)/2-p+(sr d r.sqrtId).bound)/2
    else
      r.side = 2 ∧ b ≤ p ∧
        (lr d r.logId).input = (p-(a+b)/2+(sr d r.sqrtId).bound)/2

instance (d : Tables) (a b p : ℚ) (r : Term) : Decidable (TermOK d a b p r) := by
  unfold TermOK
  split <;> first | infer_instance | split <;> infer_instance

def termUpper (d : Tables) (r : Term) : ℚ := (lr d r.logId).bound

/-- PROOF-DRAFT: generic component witness consumption; inside sqrtId is ignored. -/
theorem term_sound (d : Tables) (hd : Sound d) (a b p : ℚ) (r : Term)
    (h : TermOK d a b p r) :
    Apery.Uω (a:ℝ) (b:ℝ) (p:ℝ) ≤ (termUpper d r : ℝ) := by
  rcases h with ⟨hli,hldir,h⟩
  have hlog := hd.log r.logId hli
  simp only [CPrimitive.bound,hldir,Bool.false_eq_true,↓reduceIte] at hlog
  change Apery.Uω (a:ℝ) (b:ℝ) (p:ℝ) ≤ ((lr d r.logId).bound : ℝ)
  by_cases hz : r.side = 0
  · rw [if_pos hz] at h
    rcases h with ⟨ha,hb,hin⟩
    rw [hin] at hlog
    push_cast at hlog
    exact U49.Uω_le_inside (by exact_mod_cast ha) (by exact_mod_cast hb) hlog
  · rw [if_neg hz] at h
    rcases h with ⟨hsi,hsdir,hab,hsin,hcase⟩
    have hsqrt := hd.sqrt r.sqrtId hsi
    simp only [CPrimitive.bound,hsdir,Bool.false_eq_true,↓reduceIte] at hsqrt
    rw [hsin] at hsqrt
    push_cast at hsqrt
    obtain ⟨hs0,hsq⟩ := Real.sqrt_le_iff.mp hsqrt
    by_cases hl : r.side = 1
    · rw [if_pos hl] at hcase
      rcases hcase with ⟨hp,hin⟩
      rw [hin] at hlog
      push_cast at hlog
      exact U49.Uω_le_left (by exact_mod_cast hab) (by exact_mod_cast hp) hs0 hsq hlog
    · rw [if_neg hl] at hcase
      rcases hcase with ⟨_,hp,hin⟩
      rw [hin] at hlog
      push_cast at hlog
      exact U49.Uω_le_right (by exact_mod_cast hab) (by exact_mod_cast hp) hs0 hsq hlog

structure UPoint where
  point : ℚ
  upper : ℚ
  terms : List Term
  deriving DecidableEq, Repr, Inhabited

def ut (r : UPoint) (j : ℕ) : Term := r.terms.getD (j-1) default

def UOK (d : Tables) (r : UPoint) : Prop :=
  r.terms.length = 16 ∧
    (∀ j ∈ Icc 1 16, TermOK d (aQ j) (bQ j) r.point (ut r j)) ∧
    (∑ j ∈ Icc 1 16, cQ j * termUpper d (ut r j) : ℚ) ≤ r.upper

instance (d : Tables) (r : UPoint) : Decidable (UOK d r) := by
  unfold UOK
  infer_instance

/-- PROOF-DRAFT: one generic proof consumes every U endpoint row. -/
theorem U_sound (d : Tables) (hd : Sound d) (r : UPoint) (h : UOK d r) :
    Apery.Uρ (r.point:ℝ) ≤ (r.upper:ℝ) := by
  apply potential_upper r.point r.upper (fun j => termUpper d (ut r j)) ?_ h.2.2
  intro j hj
  simpa only [aQ_cast,bQ_cast] using term_sound d hd (aQ j) (bQ j) r.point (ut r j) (h.2.1 j hj)

structure VPoint where
  point : ℚ
  lower : ℚ
  pos : Bool
  slo : ℕ
  shi : ℕ
  llo : ℕ
  lhi : ℕ
  alo : ℕ
  ahi : ℕ
  deriving DecidableEq, Repr, Inhabited

def pBound (d : Tables) (r : VPoint) : ℚ :=
  CPrimitive.piLo + (ar d r.alo).bound - 6*(ar d r.ahi).bound

def vExpr (d : Tables) (r : VPoint) : ℚ :=
  (lr d r.llo).bound - 6*(3/40)*(lr d r.lhi).bound - 2 + 12*(3/40) +
    2*(if r.pos then (sr d r.slo).bound else (sr d r.shi).bound)*pBound d r

def VOK (d : Tables) (r : VPoint) : Prop :=
  0 < r.point ∧
  r.slo < d.sq.length ∧ r.shi < d.sq.length ∧
  r.llo < d.logs.length ∧ r.lhi < d.logs.length ∧
  r.alo < d.ats.length ∧ r.ahi < d.ats.length ∧
  (sr d r.slo).lower = true ∧ (sr d r.shi).lower = false ∧
  (lr d r.llo).lower = true ∧ (lr d r.lhi).lower = false ∧
  (ar d r.alo).lower = true ∧ (ar d r.ahi).lower = false ∧
  (sr d r.slo).input = r.point ∧ (sr d r.shi).input = r.point ∧
  0 < (sr d r.slo).bound ∧
  (lr d r.llo).input = 1+r.point ∧ (lr d r.lhi).input = r.point+(3/40)^2 ∧
  (ar d r.alo).input = 1/(sr d r.shi).bound ∧
  (ar d r.ahi).input = (3/40)/(sr d r.slo).bound ∧
  (if r.pos then 0 ≤ pBound d r else pBound d r ≤ 0) ∧ r.lower ≤ vExpr d r

instance (d : Tables) (r : VPoint) : Decidable (VOK d r) := by
  unfold VOK
  split <;> infer_instance

/-- PROOF-DRAFT: one generic signed proof consumes every noncritical V endpoint. -/
theorem V_sound (d : Tables) (hd : Sound d) (r : VPoint) (h : VOK d r) :
    (r.lower:ℝ) ≤ Apery.Vfield (r.point:ℝ) := by
  rcases h with ⟨hp,hsl,hsh,hll,hlh,hal,hah,hsld,hshd,hlld,hlhd,hald,hahd,
    hsli,hshi,hsl0,hlli,hlhi,hali,hahi,hP,hb⟩
  have sl := hd.sqrt r.slo hsl
  have sh := hd.sqrt r.shi hsh
  have ll := hd.log r.llo hll
  have lh := hd.log r.lhi hlh
  have al := hd.atan r.alo hal
  have ah := hd.atan r.ahi hah
  simp only [CPrimitive.bound,hsld,hshd,hlld,hlhd,hald,hahd,↓reduceIte] at sl sh ll lh al ah
  rw [hsli] at sl
  rw [hshi] at sh
  rw [hlli] at ll
  rw [hlhi] at lh
  rw [hali] at al
  rw [hahi] at ah
  push_cast at ll lh al ah
  have hp' : (0:ℝ) < r.point := by exact_mod_cast hp
  have hs0 : (0:ℝ) < (sr d r.slo).bound := by exact_mod_cast hsl0
  have hsum : (r.lower:ℝ) ≤ (vExpr d r:ℝ) := by exact_mod_cast hb
  cases hpos : r.pos with
  | false =>
    rw [hpos] at hP
    have hpneg : 3.14159265358979323846 + ((ar d r.alo).bound:ℝ) -
        6*((ar d r.ahi).bound:ℝ) ≤ 0 := by
      have : (pBound d r:ℝ) ≤ 0 := by exact_mod_cast hP
      simpa [pBound] using this
    have hh := U49.Vfield_ge_of_bounds_neg hp' hs0 sl sh ll lh al ah hpneg
    apply le_trans hsum
    simpa [vExpr,pBound,hpos] using hh
  | true =>
    rw [hpos] at hP
    have hppos : 0 ≤ 3.14159265358979323846 + ((ar d r.alo).bound:ℝ) -
        6*((ar d r.ahi).bound:ℝ) := by
      have : (0:ℝ) ≤ (pBound d r:ℝ) := by exact_mod_cast hP
      simpa [pBound] using this
    have hh := U49.Vfield_ge_of_bounds_pos hp' hs0 sl sh ll lh al ah hppos
    apply le_trans hsum
    simpa [vExpr,pBound,hpos] using hh

def CriticalOK (d : Tables) (r : VPoint) : Prop :=
  r.point = qmQ ∧ r.pos = false ∧
  r.slo < d.sq.length ∧ r.shi < d.sq.length ∧
  r.llo < d.logs.length ∧ r.lhi < d.logs.length ∧
  r.alo < d.ats.length ∧ r.ahi < d.ats.length ∧
  (sr d r.slo).lower = true ∧ (sr d r.shi).lower = false ∧
  (lr d r.llo).lower = true ∧ (lr d r.lhi).lower = false ∧
  (ar d r.alo).lower = true ∧ (ar d r.ahi).lower = false ∧
  (sr d r.slo).input = qmQ ∧ (sr d r.shi).input = qpQ ∧
  0 < (sr d r.slo).bound ∧
  (lr d r.llo).input = 1+qmQ ∧ (lr d r.lhi).input = qpQ+(3/40)^2 ∧
  (ar d r.alo).input = 1/(sr d r.shi).bound ∧
  (ar d r.ahi).input = (3/40)/(sr d r.slo).bound ∧
  pBound d r ≤ 0 ∧ r.lower ≤ vExpr d r

instance (d : Tables) (r : VPoint) : Decidable (CriticalOK d r) := by
  unfold CriticalOK
  infer_instance

/-- PROOF-DRAFT: the mixed qm/qp numerical record yields the actual Vstar bound. -/
theorem critical_sound (d : Tables) (hd : Sound d) (r : VPoint) (h : CriticalOK d r) :
    (r.lower:ℝ) ≤ U49.Vstar := by
  rcases h with ⟨_,hpos,hsl,hsh,hll,hlh,hal,hah,hsld,hshd,hlld,hlhd,hald,hahd,
    hsli,hshi,hsl0,hlli,hlhi,hali,hahi,hP,hb⟩
  have sl := hd.sqrt r.slo hsl
  have sh := hd.sqrt r.shi hsh
  have ll := hd.log r.llo hll
  have lh := hd.log r.lhi hlh
  have al := hd.atan r.alo hal
  have ah := hd.atan r.ahi hah
  simp only [CPrimitive.bound,hsld,hshd,hlld,hlhd,hald,hahd,↓reduceIte] at sl sh ll lh al ah
  rw [hsli] at sl
  rw [hshi] at sh
  rw [hlli] at ll
  rw [hlhi] at lh
  rw [hali] at al
  rw [hahi] at ah
  push_cast at ll lh al ah
  simp only [qmQ_cast,qpQ_cast] at sl sh ll lh
  have hs0 : (0:ℝ) < (sr d r.slo).bound := by exact_mod_cast hsl0
  have hpneg : 3.14159265358979323846 + ((ar d r.alo).bound:ℝ) -
      6*((ar d r.ahi).bound:ℝ) ≤ 0 := by
    have : (pBound d r:ℝ) ≤ 0 := by exact_mod_cast hP
    simpa [pBound] using this
  have hh := critical_lower hs0 sl sh ll lh al ah hpneg
  have hsum : (r.lower:ℝ) ≤ (vExpr d r:ℝ) := by exact_mod_cast hb
  apply le_trans hsum
  simpa [vExpr,pBound,hpos] using hh

structure RoutedCell where
  cell : Cell
  uId : ℕ
  vId : ℕ
  deriving DecidableEq, Repr, Inhabited

def ug (us : List UPoint) (i : ℕ) : UPoint := us.getD i default
def vg (vs : List VPoint) (i : ℕ) : VPoint := vs.getD i default

def RouteOK (us : List UPoint) (vs : List VPoint) (critical : VPoint) (r : RoutedCell) : Prop :=
  r.uId < us.length ∧ (ug us r.uId).upper = r.cell.upper ∧
  if r.cell.kind = 4 then
    (ug us r.uId).point = aQ 1 ∧ critical.lower = r.cell.lower
  else
    r.vId < vs.length ∧ (vg vs r.vId).lower = r.cell.lower ∧
    match r.cell.kind with
    | 0 => (ug us r.uId).point = r.cell.left ∧ (vg vs r.vId).point = r.cell.right
    | 1 => (ug us r.uId).point = r.cell.right ∧ (vg vs r.vId).point = r.cell.left
    | 2 => (ug us r.uId).point = aQ 1 ∧ (vg vs r.vId).point = qmQ
    | 3 => (ug us r.uId).point = aQ 1 ∧ (vg vs r.vId).point = qpQ
    | _ => False

instance (us : List UPoint) (vs : List VPoint) (critical : VPoint) (r : RoutedCell) :
    Decidable (RouteOK us vs critical r) := by
  unfold RouteOK
  split
  · infer_instance
  · split <;> infer_instance

/-- PROOF-DRAFT: checked numeric references give exactly the cell consumer's inputs. -/
theorem route_sound (us : List UPoint) (vs : List VPoint) (critical : VPoint)
    (hu : ∀ i, i < us.length → Apery.Uρ ((ug us i).point:ℝ) ≤ ((ug us i).upper:ℝ))
    (hv : ∀ i, i < vs.length → ((vg vs i).lower:ℝ) ≤ Apery.Vfield ((vg vs i).point:ℝ))
    (hc : (critical.lower:ℝ) ≤ U49.Vstar) (r : RoutedCell)
    (h : RouteOK us vs critical r) : CellInputs r.cell := by
  rcases h with ⟨hui,hU,h⟩
  have hUp := hu r.uId hui
  rw [hU] at hUp
  by_cases hk : r.cell.kind = 4
  · rw [if_pos hk] at h
    rcases h with ⟨hpoint,hV⟩
    rw [hpoint,aQ_cast] at hUp
    have hm := mid_upper hUp
    simp only [CellInputs,hk]
    exact ⟨hm,by simpa only [hV] using hc⟩
  · rw [if_neg hk] at h
    rcases h with ⟨hvi,hV,hpoints⟩
    have hVp := hv r.vId hvi
    rw [hV] at hVp
    cases hkind : r.cell.kind with
    | zero =>
      simp only [hkind] at hpoints
      rw [hpoints.1] at hUp
      rw [hpoints.2] at hVp
      simp only [CellInputs,hkind]
      exact ⟨hUp,hVp⟩
    | succ k =>
      cases k with
      | zero =>
        simp only [hkind] at hpoints
        rw [hpoints.1] at hUp
        rw [hpoints.2] at hVp
        simp only [CellInputs,hkind]
        exact ⟨hUp,hVp⟩
      | succ k =>
        cases k with
        | zero =>
          simp only [hkind] at hpoints
          rw [hpoints.1,aQ_cast] at hUp
          rw [hpoints.2,qmQ_cast] at hVp
          simp only [CellInputs,hkind]
          exact ⟨mid_upper hUp,hVp⟩
        | succ k =>
          cases k with
          | zero =>
            simp only [hkind] at hpoints
            rw [hpoints.1,aQ_cast] at hUp
            rw [hpoints.2,qpQ_cast] at hVp
            simp only [CellInputs,hkind]
            exact ⟨mid_upper hUp,hVp⟩
          | succ k => simp [hkind] at hpoints

end CField
