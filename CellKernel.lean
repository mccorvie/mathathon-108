import MarginPieces

/-!
E609, Codex lane C. PROOF-DRAFT until final gate. A re-derivation of
Fauzan's theorem using Firsching's formalisation (mo271/Zeta5, Apache-2.0;
Comparator metadata Paul-Lez). Generic consumer of the actual U18 cell data;
the underlying innerR and integration helpers are attributed exact copies.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
noncomputable section
namespace SplitCells

structure Aff where
  c : ℚ
  m : ℚ
  deriving DecidableEq

def Aff.at (a : Aff) (x : ℝ) : ℝ := (a.c : ℝ) + (a.m : ℝ) * x
def Aff.qat (a : Aff) (x : ℚ) : ℚ := a.c + a.m * x

def Aff.nonnegCert (a : Aff) (l r : ℚ) : Prop :=
  0 ≤ a.qat l ∧ 0 ≤ a.qat r

def Aff.posCert (a : Aff) (l r : ℚ) : Prop :=
  a.nonnegCert l r ∧ (0 < a.qat l ∨ 0 < a.qat r)

lemma affine_nonneg (a : Aff) (l r : ℚ) (h : a.nonnegCert l r)
    (x : ℝ) (hl : (l : ℝ) ≤ x) (hr : x ≤ (r : ℝ)) : 0 ≤ a.at x := by
  have h0 : 0 ≤ (a.c : ℝ) + (a.m : ℝ) * (l : ℝ) := by exact_mod_cast h.1
  have h1 : 0 ≤ (a.c : ℝ) + (a.m : ℝ) * (r : ℝ) := by exact_mod_cast h.2
  unfold Aff.at
  by_cases hm : 0 ≤ (a.m : ℝ)
  · nlinarith [mul_nonneg hm (sub_nonneg.mpr hl)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hm) (sub_nonpos.mpr hr)]

lemma affine_pos (a : Aff) (l r : ℚ) (h : a.posCert l r)
    (x : ℝ) (hl : (l : ℝ) < x) (hr : x < (r : ℝ)) : 0 < a.at x := by
  have h0 : 0 ≤ (a.c : ℝ) + (a.m : ℝ) * (l : ℝ) := by exact_mod_cast h.1.1
  have h1 : 0 ≤ (a.c : ℝ) + (a.m : ℝ) * (r : ℝ) := by exact_mod_cast h.1.2
  rcases h.2 with h2 | h2
  · have h2' : 0 < (a.c : ℝ) + (a.m : ℝ) * (l : ℝ) := by exact_mod_cast h2
    unfold Aff.at
    by_cases hm : 0 ≤ (a.m : ℝ)
    · nlinarith [mul_nonneg hm (sub_nonneg.mpr hl.le)]
    · nlinarith [mul_pos_of_neg_of_neg (lt_of_not_ge hm) (sub_neg.mpr hr)]
  · have h2' : 0 < (a.c : ℝ) + (a.m : ℝ) * (r : ℝ) := by exact_mod_cast h2
    unfold Aff.at
    by_cases hm : (a.m : ℝ) ≤ 0
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos hm (sub_nonpos.mpr hr.le)]
    · nlinarith [mul_pos (lt_of_not_ge hm) (sub_pos.mpr hl)]

def floorCert (a : Aff) (n : ℤ) (l r : ℚ) : Prop :=
  (Aff.mk (a.c - n) a.m).nonnegCert l r ∧
  (Aff.mk (n + 1 - a.c) (-a.m)).posCert l r

lemma floor_of_cert (a : Aff) (n : ℤ) (l r : ℚ) (h : floorCert a n l r)
    (x : ℝ) (hl : (l : ℝ) < x) (hr : x < (r : ℝ)) : ⌊a.at x⌋ = n := by
  apply Int.floor_eq_iff.mpr
  have h0 := affine_nonneg _ _ _ h.1 x hl.le hr.le
  have h1 := affine_pos _ _ _ h.2 x hl hr
  dsimp [Aff.at] at h0 h1 ⊢
  push_cast at h0 h1
  constructor <;> linarith

def zFloorCert (lo hi : Aff) (c e : ℚ) (n : ℤ) (l r : ℚ) : Prop :=
  if 0 < e then
    (Aff.mk (e*lo.c-n) (c+e*lo.m)).nonnegCert l r ∧
    (Aff.mk (n+1-e*hi.c) (-c-e*hi.m)).nonnegCert l r
  else
    (Aff.mk (e*hi.c-n) (c+e*hi.m)).nonnegCert l r ∧
    (Aff.mk (n+1-e*lo.c) (-c-e*lo.m)).nonnegCert l r

lemma zfloor_of_cert (lo hi : Aff) (c e : ℚ) (n : ℤ) (l r : ℚ)
    (hne : e ≠ 0) (h : zFloorCert lo hi c e n l r)
    (x z : ℝ) (hl : (l : ℝ) < x) (hr : x < (r : ℝ))
    (hzl : lo.at x < z) (hzr : z < hi.at x) :
    ⌊(c : ℝ)*x+(e : ℝ)*z⌋ = n := by
  apply Int.floor_eq_iff.mpr
  by_cases he : (0 : ℚ) < e
  · rw [zFloorCert, if_pos he] at h
    have h0 := affine_nonneg _ _ _ h.1 x hl.le hr.le
    have h1 := affine_nonneg _ _ _ h.2 x hl.le hr.le
    have he' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
    dsimp [Aff.at] at h0 h1 hzl hzr
    push_cast at h0 h1
    constructor <;> nlinarith [mul_pos he' (sub_pos.mpr hzl), mul_pos he' (sub_pos.mpr hzr)]
  · rw [zFloorCert, if_neg he] at h
    have h0 := affine_nonneg _ _ _ h.1 x hl.le hr.le
    have h1 := affine_nonneg _ _ _ h.2 x hl.le hr.le
    have heq : e < 0 := lt_of_le_of_ne (le_of_not_gt he) hne
    have he' : (e : ℝ) < 0 := by exact_mod_cast heq
    dsimp [Aff.at] at h0 h1 hzl hzr
    push_cast at h0 h1
    constructor <;> nlinarith [mul_pos_of_neg_of_neg he' (sub_neg.mpr hzl),
      mul_pos_of_neg_of_neg he' (sub_neg.mpr hzr)]

structure Row where
  l : ℚ
  r : ℚ
  a : ℚ
  b : ℚ
  floors : Fin 5 → ℤ
  nodes : Fin 4 → Aff
  zFloors : Fin 3 → Fin 4 → ℤ
  positive : Bool

def globals : Fin 5 → Aff := ![⟨0,23/10⟩,⟨0,1⟩,⟨0,3/40⟩,⟨0,2⟩,⟨0,37/20⟩]
def xCoeffs : Fin 4 → ℚ := ![1,1,3/40,3/40]
def zCoeffs : Fin 4 → ℚ := ![-1,1,-1,1]
def next (j : Fin 3) : Fin 4 := ⟨j.val+1, by omega⟩
def nodeDiff (r : Row) (j : Fin 3) : Aff :=
  ⟨(r.nodes (next j)).c-(r.nodes j.castSucc).c,
    (r.nodes (next j)).m-(r.nodes j.castSucc).m⟩
def beta (r : Row) : Aff := ⟨((r.floors 3 : ℚ)-r.floors 0)/2,3/20⟩
def maxAff (r : Row) : Aff := if r.positive then beta r else ⟨0,0⟩
def gammaVal (r : Row) (j : Fin 3) : ℚ :=
  let T : ℚ := r.floors 0
  let ex : ℚ := r.zFloors j 0+r.zFloors j 1+1
  let ea : ℚ := r.zFloors j 2+r.zFloors j 3+1
  (T-3*ea)*(T+3*ea-ex-7)
def gammaAff (r : Row) : Aff :=
  ⟨∑ j : Fin 3, gammaVal r j*(nodeDiff r j).c,
    ∑ j : Fin 3, gammaVal r j*(nodeDiff r j).m⟩
def resultAff (r : Row) : Aff :=
  let T : ℚ := r.floors 0
  let q : ℚ := r.floors 3
  let L : ℚ := r.floors 4
  ⟨-(gammaAff r).c+T/2*(2*T-q-7)-(maxAff r).c-L*(L+1)/2,
    -(gammaAff r).m-23/20*(2*T-q-7)-(maxAff r).m-
      37/40*(2*(r.floors 1 : ℚ)-12*r.floors 2-2*L)⟩

def Row.Valid (r : Row) : Prop :=
  0 < r.l ∧ r.l < r.r ∧ r.nodes 0 = ⟨0,0⟩ ∧ r.nodes 3 = ⟨1/2,0⟩ ∧
  (∀ j : Fin 3, (nodeDiff r j).nonnegCert r.l r.r) ∧
  (∀ i : Fin 5, floorCert (globals i) (r.floors i) r.l r.r) ∧
  (∀ j : Fin 3, ∀ k : Fin 4,
    zFloorCert (r.nodes j.castSucc) (r.nodes (next j))
      (xCoeffs k) (zCoeffs k) (r.zFloors j k) r.l r.r) ∧
  (if r.positive then (beta r).nonnegCert r.l r.r else
    (Aff.mk (-(beta r).c) (-(beta r).m)).nonnegCert r.l r.r) ∧
  (resultAff r).c = r.a ∧ (resultAff r).m = r.b

instance (a : Aff) (l r : ℚ) : Decidable (a.nonnegCert l r) := by
  unfold Aff.nonnegCert
  infer_instance

instance (a : Aff) (l r : ℚ) : Decidable (a.posCert l r) := by
  unfold Aff.posCert
  infer_instance

instance (a : Aff) (n : ℤ) (l r : ℚ) : Decidable (floorCert a n l r) := by
  unfold floorCert
  infer_instance

instance (lo hi : Aff) (c e : ℚ) (n : ℤ) (l r : ℚ) :
    Decidable (zFloorCert lo hi c e n l r) := by
  unfold zFloorCert
  split <;> infer_instance

instance (r : Row) : Decidable r.Valid := by
  unfold Row.Valid
  infer_instance

end SplitCells
