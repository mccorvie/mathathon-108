import ClassData

/-! E418 local outer proof, Codex lane B. PROOF-DRAFT until driver gate.
Actual E405 inputs unchanged. Generic class-count proof blocks adapt
Firsching/Paul-Lez mo271/Zeta5@be1c0d82 Growth/OuterPrime.lean:16-139,
Apache-2.0. No PNT integration or all-allocation inner statement is attempted.
-/

open Finset
namespace BOuterBridge
open AperyS AperyS.AssemblyTarget Mathathon.P108.RangeBridgeTarget

theorem outer_finite_facts (s ν n p M : ℕ) (hscope : ParameterScope s ν)
    (hn : max 1 s ≤ n) (hM : 3 ≤ M) (hp : p.Prime) (hout : 40 * n < 3 * p) :
    OuterOK s (40 * n) (3 * n) p ∧ ¬p * M ≤ 40 * n ∧ 2 * (3 * n) < p := by
  obtain ⟨hodd, hs, heven, hν, hνmax⟩ := hscope
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hns : s ≤ n := (le_max_right _ _).trans hn
  have hp7 : 7 ≤ p := by omega
  have hps : s ≤ p := by omega
  have hsq : 2 * (40 * n) < p ^ 2 := by
    have hmul := Nat.mul_le_mul_left p (show 6 ≤ p by omega)
    nlinarith
  have hpodd : 2 * (p / 2) + 1 = p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · omega
  refine ⟨⟨hpodd, hps, hp7, hout, hsq, by omega⟩, ?_, by omega⟩
  have hmul := Nat.mul_le_mul_left p hM
  omega

theorem selected_sharp_outer (s ν n p M : ℕ) (L : Allocations)
    (hscope : ParameterScope s ν) (hn : max 1 s ≤ n) (hM : 3 ≤ M)
    (hp : p.Prime) (hout : 40 * n < 3 * p) :
    LpSharp s ν (40 * n) (3 * n) M p L =
      vSK ν (40 * n) (3 * n) p + ⌊WOsharp s ν (40 * n) (3 * n) p⌋ := by
  have h := outer_finite_facts s ν n p M hscope hn hM hp hout
  unfold LpSharp
  rw [if_neg h.2.1, if_neg (by omega), if_pos h.1]

variable {p m : ℕ} [Fact p.Prime]

lemma jc_eq_iff (hm : 2 * m + 1 = p) (j : ℕ) (c : Fin (m + 1)) :
    jc hm j = c ↔ ((j : ℤ) : ZMod p) = (((c : ℕ) : ℤ) : ZMod p) ∨
      ((j : ℤ) : ZMod p) = -(((c : ℕ) : ℤ) : ZMod p) := by
  unfold jc
  constructor
  · intro h
    rcases ccls_spec hm ((j : ℤ) : ZMod p) with h1 | h1 <;> rw [h] at h1
    · left; exact h1.symm
    · right; rw [h1]; ring
  · intro h
    refine (ccls_unique hm _ c ?_).symm
    rcases h with h | h
    · left; exact h.symm
    · right; rw [h]; ring

lemma neg_ne_self_zmod (hm : 2 * m + 1 = p) {x : ZMod p} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero_zmod hm h3
  · exact hx h3

lemma card_class (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) (X : ℕ) :
    ((Icc 1 X).filter fun j => jc hm j = c).card = SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  have hc0 : (((c : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply hc
    have := (ccls_eq_zero_iff hm _).mpr h
    rw [ccls_self hm c] at this
    exact this
  unfold SX
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, jc_eq_iff hm]
    tauto
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact neg_ne_self_zmod hm hc0 (h1.2.symm.trans h2.2)

lemma card_class_Ioc (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) {X Y : ℕ} (hXY : X ≤ Y) :
    ((Icc (X + 1) Y).filter fun j => jc hm j = c).card =
      SX p Y (((c : ℕ) : ℤ) : ZMod p) - SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  rw [← card_class hm hc, ← card_class hm hc]
  have hsplit : (Icc 1 Y).filter (fun j => jc hm j = c) =
      (Icc 1 X).filter (fun j => jc hm j = c) ∪ (Icc (X + 1) Y).filter (fun j => jc hm j = c) := by
    ext j; simp only [mem_filter, mem_union, mem_Icc]; omega
  have hdisj : Disjoint ((Icc 1 X).filter (fun j => jc hm j = c))
      ((Icc (X + 1) Y).filter (fun j => jc hm j = c)) := by
    rw [disjoint_left]; intro j h1 h2
    simp only [mem_filter, mem_Icc] at h1 h2; omega
  rw [hsplit, card_union_of_disjoint hdisj]
  omega

lemma SX_small (hm : 2 * m + 1 = p) {X : ℕ} (hX : X < p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = aCnt p X c := by
  rw [SX_class hm hc1 hcm, Nat.div_eq_of_lt hX, Nat.mod_eq_of_lt hX]; ring

noncomputable def GO (s ν q a d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * q + a - 2), min 0 ((i : ℚ) + (ν : ℚ) / 2 * d -
    ((2 * q + a : ℕ) + ((s : ℚ) - 1)) / 2)

lemma neg_two_min_zero (x : ℝ) : -2 * min 0 x = max 0 (-2 * x) := by
  by_cases hx : 0 ≤ x
  · rw [min_eq_left hx, max_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem removed_class_cost (s ν q a : ℕ) :
    -2 * (GO s ν q a 1 : ℝ) = Mathathon.P108.cRem (s : ℝ) (ν : ℝ) (2 * q + a) := by
  unfold GO Mathathon.P108.cRem
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [neg_two_min_zero]
  congr 1
  ring

lemma class_data (hm : 2 * m + 1 = p) (N K : ℕ) (hNK : N ≤ K) (hN2 : 2 * N < p)
    {c : Fin (m + 1)} (hc : c ≠ 0) :
    LoC hm N K c = 2 * (K / p) + aCnt p (K % p) c - aCnt p N c ∧
      nbC hm N K c = 2 * (K / p) + aCnt p (K % p) c - 2 ∧
      ellC hm K c = 2 * (K / p) + aCnt p (K % p) c ∧
      delC N c = aCnt p N c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact False.elim (hc (Fin.ext h))
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have hNm : N ≤ m := by omega
  have hN : N < p := by omega
  have hK := SX_class hm hc1 hcm K
  have hNs := SX_small hm hN hc1 hcm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LoC tailC tailO
    rw [card_class_Ioc hm hc hNK, hK, hNs]
  · unfold nbC bigC tailC tailO
    rw [filter_filter]
    rcases le_or_gt p K with hpK | hpK
    · have e : (Icc (N + 1) K).filter (fun j => jc hm j = c ∧ p < j) =
          (Icc (p + 1) K).filter (fun j => jc hm j = c) := by
        ext j; simp only [mem_filter, mem_Icc]; omega
      rw [e, card_class_Ioc hm hc hpK, hK, SX_class hm hc1 hcm p, Nat.div_self (by omega), Nat.mod_self]
      unfold aCnt
      split_ifs <;> omega
    · have e : (Icc (N + 1) K).filter (fun j => jc hm j = c ∧ p < j) = ∅ := by
        ext j; simp only [mem_filter, mem_Icc, notMem_empty, iff_false]; omega
      rw [e, card_empty, Nat.div_eq_of_lt hpK]
      unfold aCnt
      split_ifs <;> omega
  · unfold ellC
    rw [card_class hm hc, hK]
  · unfold delC aCnt
    split_ifs <;> omega

lemma sum_wO_class (hm : 2 * m + 1 = p) (s ν N K : ℕ) (hNK : N ≤ K) (hN2 : 2 * N < p)
    {c : Fin (m + 1)} (hc : c ≠ 0) :
    ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i =
      GO s ν (K / p) (aCnt p (K % p) c) (aCnt p N c) := by
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm N K hNK hN2 hc
  have hδ : aCnt p N c ≤ 1 := by
    have hcm := Nat.lt_succ_iff.mp c.isLt
    unfold aCnt
    split_ifs <;> omega
  have hsub : nbC hm N K c ≤ LoC hm N K c := by rw [hL, hnb]; omega
  rw [← sum_range_add_sum_Ico _ hsub]
  have h0 : ∑ i ∈ Ico (nbC hm N K c) (LoC hm N K c), wO hm s ν N K c i = 0 := by
    apply sum_eq_zero
    intro i hi
    unfold wO
    rw [if_neg hc, if_neg (by have := (mem_Ico.mp hi).1; omega)]
  rw [h0, add_zero, hnb]
  unfold GO
  apply sum_congr rfl
  intro i hi
  unfold wO
  rw [if_neg hc, if_pos (by rw [hnb]; exact mem_range.mp hi), hl, hd]

/-- Exact cost of an actual removed ordinary class; the right side is the
actual cRem definition used by Tout. No allocation/energy hypothesis occurs. -/
theorem actual_removed_class_cost (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hNK : N ≤ K) (hN2 : 2 * N < p) {c : Fin (m + 1)} (hc : c ≠ 0) (hcN : (c : ℕ) ≤ N) :
    -2 * ((∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) =
      Mathathon.P108.cRem (s : ℝ) (ν : ℝ) (2 * (K / p) + aCnt p (K % p) c) := by
  have hd : aCnt p N c = 1 := by
    have hcm := Nat.lt_succ_iff.mp c.isLt
    unfold aCnt
    rw [if_pos hcN, if_neg (by omega)]
  rw [sum_wO_class hm s ν N K hNK hN2 hc, hd]
  exact removed_class_cost s ν (K / p) (aCnt p (K % p) c)

/-- Auxiliary coordinates for unremoved and removed class values. -/
noncomputable def classProfile (B R : ℕ → ℝ) (a d : ℕ) : ℝ :=
  if d = 0 then B a else R a

/-- Exact continuous interval-count identity for a prefix of at most half a
residue period. The actual assembly definitions are unchanged. -/
theorem continuous_profile (f g : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 2) (B R : ℕ → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      bcoef (fun a => bcoef (classProfile B R a) j) i * ccount f g i j) =
      B 0 / 2 + (B 1 - B 0) * min f (1 / 2) +
        (B 2 - B 1) * max 0 (f - 1 / 2) +
      (R 0 - B 0) * g +
      ((R 1 - B 1) - (R 0 - B 0)) * min f g +
      ((R 2 - B 2) - (R 1 - B 1)) * max 0 (f + g - 1) := by
  have h00 : ccount f g 0 0 = 1 / 2 := by norm_num [ccount, cvHi, cvLo]
  have h10 : ccount f g 1 0 = min f (1 / 2) := by
    have hmin : 0 ≤ min f (1 / 2) := le_min hf0 (by norm_num)
    simp [ccount, cvHi, cvLo, hf0]
  have h20 : ccount f g 2 0 = max 0 (f - 1 / 2) := by
    have h1f : 0 ≤ 1 - f := by linarith
    simp [ccount, cvHi, cvLo, max_eq_left h1f]
    congr 1 <;> ring
  have h01 : ccount f g 0 1 = g := by
    have h : max 0 (min (1 / 2) g) = g := by
      rw [min_eq_right hg1, max_eq_right hg0]
    simpa [ccount, cvHi, cvLo] using h
  have h11 : ccount f g 1 1 = min f g := by
    have hmin : 0 ≤ min f g := le_min hf0 hg0
    have hm : min f g ≤ 1 / 2 := (min_le_right _ _).trans hg1
    have h : max 0 (min (min f g) (1 / 2)) = min f g := by
      rw [min_eq_left hm, max_eq_right hmin]
    simpa [ccount, cvHi, cvLo] using h
  have h21 : ccount f g 2 1 = max 0 (f + g - 1) := by
    have h1f : 0 ≤ 1 - f := by linarith
    change max 0 (min (min (1 / 2) g) (1 / 2) - max (max (1 - f) 0) 0) =
      max 0 (f + g - 1)
    rw [min_eq_right hg1, min_eq_left hg1, max_eq_left h1f, max_eq_left h1f]
    congr 1 <;> ring
  simp only [Fin.sum_univ_three, bcoef, classProfile,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, if_pos rfl, if_neg (by decide : ¬(1 : ℕ) = 0),
    if_neg (by decide : ¬(2 : ℕ) = 0)]
  simp only [ite_true, sub_self, zero_mul, mul_zero, add_zero]
  rw [h00, h10, h20, h01, h11, h21]
  ring


/-- Nonremoved ordinary classes have their full elementary cost; only the
actual scope bound s>=5 and the outer q<=2 are used. -/
theorem unremoved_class_cost (s ν q a : ℕ) (hs : 5 ≤ s)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ha : a ≤ 2) :
    -2 * (GO s ν q a 0 : ℝ) = (s + 2 : ℝ) * (2 * q + a - 2 : ℕ) := by
  have hsQ : (5 : ℚ) ≤ s := by exact_mod_cast hs
  have hsR : (5 : ℝ) ≤ s := by exact_mod_cast hs
  interval_cases q <;> interval_cases a <;>
    norm_num [GO, Finset.sum_range_succ] <;>
    repeat rw [min_eq_right (by linarith)] <;> push_cast <;> ring

/-- The only half-period endpoint correction needed by a linear class cost. -/
lemma min_half_plus_max (f : ℝ) : min f (1 / 2) + max 0 (f - 1 / 2) = f := by
  by_cases h : f ≤ 1 / 2
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring

/-- Continuous density formula for a profile linear in its unremoved class
size; R0,R1,R2 stay symbolic. -/
theorem continuous_linear_profile (s q : ℕ) (hq : 1 ≤ q)
    (f g : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 2) (R : ℕ → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      bcoef (fun a => bcoef (classProfile
        (fun a => (s + 2 : ℝ) * (2 * q + a - 2 : ℕ)) R a) j) i * ccount f g i j) =
      (s + 2 : ℝ) * ((q : ℝ) - 1 + f -
        ((g - min f g) * (2 * q - 2 : ℝ) +
        (min f g - max 0 (f + g - 1)) * (2 * q - 1 : ℝ) +
        max 0 (f + g - 1) * (2 * q : ℝ))) +
      (g - min f g) * R 0 + (min f g - max 0 (f + g - 1)) * R 1 +
        max 0 (f + g - 1) * R 2 := by
  rw [continuous_profile f g hf0 hf1 hg0 hg1]
  norm_num only [Nat.add_zero, Nat.add_sub_cancel]
  rw [Nat.cast_sub (by omega : 2 ≤ 2 * q),
    Nat.cast_sub (by omega : 2 ≤ 2 * q + 1)]
  push_cast
  have h := min_half_plus_max f
  linear_combination (s + 2 : ℝ) * h

/-- Continuous density formula for zero weights of ordinary classes. -/
theorem continuous_zero_profile (f g : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 2) (R : ℕ → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      bcoef (fun a => bcoef (classProfile (fun _ => 2) R a) j) i * ccount f g i j) =
      1 - 2 * g + (g - min f g) * R 0 +
      (min f g - max 0 (f + g - 1)) * R 1 + max 0 (f + g - 1) * R 2 := by
  rw [continuous_profile f g hf0 hf1 hg0 hg1]
  ring


lemma aCnt_le_two (p v c : ℕ) : aCnt p v c ≤ 2 := by
  unfold aCnt
  split_ifs <;> omega

lemma aCnt_small_le_one (hm : 2 * m + 1 = p) (N : ℕ) (hN : 2 * N < p)
    (c : Fin (m + 1)) : aCnt p N c ≤ 1 := by
  have hcm := Nat.lt_succ_iff.mp c.isLt
  unfold aCnt
  split_ifs <;> omega

noncomputable def costProfile (s ν q : ℕ) : ℕ → ℕ → ℝ :=
  classProfile (fun a => (s + 2 : ℝ) * (2 * q + a - 2 : ℕ))
    (fun a => Mathathon.P108.cRem s ν (2 * q + a))

noncomputable def zeroProfile (s ν q : ℕ) : ℕ → ℕ → ℝ :=
  classProfile (fun _ => 2) (fun a => Mathathon.P108.zRem s ν (2 * q + a))

/-- The actual ordinary class cost equals its two-state profile exactly. -/
theorem actual_class_cost (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hs : 5 ≤ s) (hNK : N ≤ K) (hN2 : 2 * N < p)
    (hpK : p ≤ K) (hK3 : K < 3 * p)
    {c : Fin (m + 1)} (hc : c ≠ 0) :
    -2 * ((∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) =
      costProfile s ν (K / p) (aCnt p (K % p) c) (aCnt p N c) := by
  have hp0 : 0 < p := by omega
  have hq1 : 1 ≤ K / p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  have hq2 : K / p ≤ 2 := by
    have := (Nat.div_lt_iff_lt_mul hp0).mpr hK3
    omega
  have hd := aCnt_small_le_one hm N hN2 c
  rw [sum_wO_class hm s ν N K hNK hN2 hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
  · rw [hd]
    simpa [costProfile, classProfile] using
      unremoved_class_cost s ν (K / p) (aCnt p (K % p) c) hs hq1 hq2
        (aCnt_le_two _ _ _)
  · rw [hd]
    simpa [costProfile, classProfile] using
      removed_class_cost s ν (K / p) (aCnt p (K % p) c)

noncomputable def GZ (s ν q a d : ℕ) : ℝ :=
  (2 - d : ℕ) + ∑ i ∈ range (2 * q + a - 2),
    if (2 * q + a : ℕ) + (s : ℝ) - 1 - (ν : ℝ) * d - 2 * i ≤ 0 then 1 else 0

lemma GZ_profile (s ν q a d : ℕ) (hs : 5 ≤ s)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ha : a ≤ 2) (hd : d ≤ 1) :
    GZ s ν q a d = zeroProfile s ν q a d := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
  · subst d
    have hsum : (∑ i ∈ range (2 * q + a - 2),
        if (2 * q + a : ℕ) + (s : ℝ) - 1 - (ν : ℝ) * 0 - 2 * i ≤ 0
          then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hiN := mem_range.mp hi
      have hle : 2 * q + a ≤ 6 := by omega
      have hsub : 2 ≤ 2 * q + a := by omega
      have hiR : (i : ℝ) < (2 * q + a - 2 : ℕ) := by exact_mod_cast hiN
      have hsR : (5 : ℝ) ≤ s := by exact_mod_cast hs
      have hlR : ((2 * q + a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hle
      rw [Nat.cast_sub hsub] at hiR
      norm_num only [Nat.cast_ofNat] at hiR
      rw [if_neg (by simp only [mul_zero, sub_zero]; nlinarith)]
    change (2 : ℝ) + _ = 2
    simp only [Nat.cast_zero]
    rw [hsum, add_zero]
  · subst d
    simp [GZ, zeroProfile, classProfile, Mathathon.P108.zRem]

/-- Exact zero-weight count of an actual nonzero class. -/
theorem actual_class_zeros (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hs : 5 ≤ s) (hNK : N ≤ K) (hN2 : 2 * N < p)
    (hpK : p ≤ K) (hK3 : K < 3 * p)
    {c : Fin (m + 1)} (hc : c ≠ 0) :
    (((range (LoC hm N K c)).filter fun i => wO hm s ν N K c i = 0).card : ℝ) =
      zeroProfile s ν (K / p) (aCnt p (K % p) c) (aCnt p N c) := by
  have hp0 : 0 < p := by omega
  have hq1 : 1 ≤ K / p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  have hq2 : K / p ≤ 2 := by
    have := (Nat.div_lt_iff_lt_mul hp0).mpr hK3
    omega
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm N K hNK hN2 hc
  have hδ := aCnt_small_le_one hm N hN2 c
  have hsub : nbC hm N K c ≤ LoC hm N K c := by rw [hL, hnb]; omega
  have hgap : LoC hm N K c - nbC hm N K c = 2 - aCnt p N c := by
    rw [hL, hnb]
    omega
  rw [← GZ_profile s ν (K / p) (aCnt p (K % p) c) (aCnt p N c)
    hs hq1 hq2 (aCnt_le_two _ _ _) hδ]
  rw [card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← sum_range_add_sum_Ico _ hsub]
  have htail : (∑ i ∈ Ico (nbC hm N K c) (LoC hm N K c),
      if wO hm s ν N K c i = 0 then (1 : ℝ) else 0) = (2 - aCnt p N c : ℕ) := by
    have he : ∀ i ∈ Ico (nbC hm N K c) (LoC hm N K c), wO hm s ν N K c i = 0 := by
      intro i hi
      unfold wO
      rw [if_neg hc, if_neg (by have := (mem_Ico.mp hi).1; omega)]
    calc
      _ = ∑ _i ∈ Ico (nbC hm N K c) (LoC hm N K c), (1 : ℝ) :=
        sum_congr rfl (fun i hi => if_pos (he i hi))
      _ = _ := by simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, hgap]
  rw [htail]
  unfold GZ
  rw [add_comm]
  congr 1
  rw [hnb]
  apply sum_congr rfl
  intro i hi
  have hi' : i < nbC hm N K c := by rw [hnb]; exact mem_range.mp hi
  have he : wO hm s ν N K c i = 0 ↔
      ((2 * (K / p) + aCnt p (K % p) c : ℕ) : ℝ) + s - 1 -
        (ν : ℝ) * aCnt p N c - 2 * i ≤ 0 := by
    rw [wO, if_neg hc, if_pos hi', hl, hd, min_eq_left_iff]
    constructor
    · intro h
      have hq : ((2 * (K / p) + aCnt p (K % p) c : ℕ) : ℚ) + s - 1 -
          (ν : ℚ) * aCnt p N c - 2 * i ≤ 0 := by linarith
      exact_mod_cast hq
    · intro h
      have hq : ((2 * (K / p) + aCnt p (K % p) c : ℕ) : ℚ) + s - 1 -
          (ν : ℚ) * aCnt p N c - 2 * i ≤ 0 := by exact_mod_cast h
      linarith
  simp only [he]


/-- Generic splitting of the zero residue class. The finite sum identity is
adapted from upstream Growth/InnerPrime.lean:21-30 (Apache-2.0). -/
lemma sum_erase_zero_Icc {m : ℕ} (F : ℕ → ℝ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by ext c; simp only [mem_Ico, mem_Icc]; omega
  rw [h2] at h1
  linarith

lemma sum_split_zero {m : ℕ} (F : Fin (m + 1) → ℝ) (G : ℕ → ℝ)
    (hF : ∀ c, c ≠ 0 → F c = G c) :
    ∑ c, F c = F 0 + ∑ c ∈ Icc 1 m, G c := by
  rw [← add_sum_erase _ _ (mem_univ (0 : Fin (m + 1)))]
  congr 1
  rw [sum_congr rfl (fun c hc => hF c (mem_erase.mp hc).1)]
  exact sum_erase_zero_Icc G

/-- At most two poles occur in the zero class in the actual outer range. -/
lemma zero_class_length (hm : 2 * m + 1 = p) (N K : ℕ) (hK3 : K < 3 * p) :
    LoC hm N K 0 ≤ 2 := by
  unfold LoC tailC tailO
  have hsub : (Icc (N + 1) K).filter (fun j => jc hm j = 0) ⊆ {p, 2 * p} := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.mp hj
    have hdvd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hj2
    obtain ⟨t, rfl⟩ := hdvd
    have := mem_Icc.mp hj1
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst t; omega
      · exact h
    have ht3 : t < 3 := by
      by_contra h
      have := Nat.mul_le_mul_left p (show 3 ≤ t by omega)
      omega
    interval_cases t <;> simp [mul_comm]
  exact (card_le_card hsub).trans card_le_two

lemma zero_class_cost_bound (hm : 2 * m + 1 = p) (s ν N K : ℕ) (hK3 : K < 3 * p) :
    |-2 * ((∑ i ∈ range (LoC hm N K 0), wO hm s ν N K 0 i : ℚ) : ℝ)| ≤ 8 := by
  have hL := zero_class_length hm N K hK3
  have hrow : ∀ i, (-2 : ℚ) ≤ wO hm s ν N K 0 i ∧ wO hm s ν N K 0 i ≤ 0 := by
    intro i
    unfold wO
    rw [if_pos rfl]
    split_ifs <;> norm_num
  have hlow := sum_le_sum (fun i (_ : i ∈ range (LoC hm N K 0)) => (hrow i).1)
  have hupp := sum_nonpos (fun i (_ : i ∈ range (LoC hm N K 0)) => (hrow i).2)
  simp only [sum_const, card_range, nsmul_eq_mul] at hlow
  have hLR : (LoC hm N K 0 : ℚ) ≤ 2 := by exact_mod_cast hL
  have hlow' : (-4 : ℚ) ≤ ∑ i ∈ range (LoC hm N K 0), wO hm s ν N K 0 i := by linarith
  have hlR : (-4 : ℝ) ≤ ((∑ i ∈ range (LoC hm N K 0), wO hm s ν N K 0 i : ℚ) : ℝ) :=
    by exact_mod_cast hlow'
  have huR : ((∑ i ∈ range (LoC hm N K 0), wO hm s ν N K 0 i : ℚ) : ℝ) ≤ 0 :=
    by exact_mod_cast hupp
  rw [abs_le]
  constructor <;> linarith

lemma zero_class_zeros_bound (hm : 2 * m + 1 = p) (s ν N K : ℕ) (hK3 : K < 3 * p) :
    |(((range (LoC hm N K 0)).filter fun i => wO hm s ν N K 0 i = 0).card : ℝ)| ≤ 2 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (card_filter_le _ _).trans (by simpa using zero_class_length hm N K hK3)

noncomputable def profileError (H : ℕ → ℕ → ℝ) : ℝ :=
  5 / 2 * ∑ i : Fin 3, ∑ j : Fin 3, |bcoef (fun a => bcoef (H a) j) i|

noncomputable def continuousProfile (H : ℕ → ℕ → ℝ) (f g : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, bcoef (fun a => bcoef (H a) j) i * ccount f g i j

lemma profileError_nonneg (H : ℕ → ℕ → ℝ) : 0 ≤ profileError H := by
  unfold profileError
  positivity

/-- Total actual row cost differs from its continuous interval sum by a
constant depending only on s,nu,q; the zero residue class contributes <=8. -/
theorem actual_cost_profile_approx (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hs : 5 ≤ s) (hNK : N ≤ K) (hN2 : 2 * N < p)
    (hpK : p ≤ K) (hK3 : K < 3 * p) :
    |-2 * ((∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) -
      (p : ℝ) * continuousProfile (costProfile s ν (K / p))
        ((K % p : ℕ) / (p : ℝ)) ((N : ℝ) / p)| ≤
      profileError (costProfile s ν (K / p)) + 8 := by
  have hp0 : 0 < p := by omega
  have hsplit := sum_split_zero
    (fun c => -2 * ((∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ))
    (fun c => costProfile s ν (K / p) (aCnt p (K % p) c) (aCnt p N c))
    (fun c hc => actual_class_cost hm s ν N K hs hNK hN2 hpK hK3 hc)
  have heq : -2 * ((∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) =
      ∑ c, -2 * ((∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) := by
    push_cast
    rw [mul_sum]
  rw [heq, hsplit]
  have hsum := class_sum_approx hm (Nat.mod_lt K hp0) (show N < p by omega)
    (costProfile s ν (K / p))
  change |_ - (p : ℝ) * continuousProfile _ _ _| ≤ profileError _ at hsum
  have hz := zero_class_cost_bound hm s ν N K hK3
  rw [abs_le] at hsum hz ⊢
  constructor <;> linarith [hsum.1, hsum.2, hz.1, hz.2]

/-- The actual zero-weight count differs from its continuous interval sum by
its profile error plus at most two zero-class rows. -/
theorem actual_zero_profile_approx (hm : 2 * m + 1 = p) (s ν N K : ℕ)
    (hs : 5 ≤ s) (hNK : N ≤ K) (hN2 : 2 * N < p)
    (hpK : p ≤ K) (hK3 : K < 3 * p) :
    |(outerZeroCount hm s ν N K : ℝ) -
      (p : ℝ) * continuousProfile (zeroProfile s ν (K / p))
        ((K % p : ℕ) / (p : ℝ)) ((N : ℝ) / p)| ≤
      profileError (zeroProfile s ν (K / p)) + 2 := by
  have hp0 : 0 < p := by omega
  have hsplit := sum_split_zero
    (fun c => (((range (LoC hm N K c)).filter fun i => wO hm s ν N K c i = 0).card : ℝ))
    (fun c => zeroProfile s ν (K / p) (aCnt p (K % p) c) (aCnt p N c))
    (fun c hc => actual_class_zeros hm s ν N K hs hNK hN2 hpK hK3 hc)
  have heq : (outerZeroCount hm s ν N K : ℝ) =
      ∑ c, (((range (LoC hm N K c)).filter fun i => wO hm s ν N K c i = 0).card : ℝ) := by
    unfold outerZeroCount
    push_cast
    rfl
  rw [heq, hsplit]
  have hsum := class_sum_approx hm (Nat.mod_lt K hp0) (show N < p by omega)
    (zeroProfile s ν (K / p))
  change |_ - (p : ℝ) * continuousProfile _ _ _| ≤ profileError _ at hsum
  have hz := zero_class_zeros_bound hm s ν N K hK3
  rw [abs_le] at hsum hz ⊢
  constructor <;> linarith [hsum.1, hsum.2, hz.1, hz.2]

/-- Natural-rank truncation differs from its actual continuous expression
only by the use of p-1 instead of p. -/
theorem actual_raw_rank_approx (s ν K N p : ℕ) (hodd : Odd s)
    (hs : 1 ≤ s) (hν : 2 ≤ ν) (hNK : N ≤ K) (hp : 1 ≤ p) :
    |(rawRank s ν K N p : ℝ) -
      min ((K : ℝ) - N) (max 0 ((K : ℝ) + ((ν : ℝ) - 2) * N -
        ((s : ℝ) - 1) / 2 * p))| ≤ ((s : ℝ) - 1) / 2 := by
  have hrN : 2 * ((s - 1) / 2) = s - 1 := by rcases hodd with ⟨k, hk⟩; omega
  have hr : (((s - 1) / 2 : ℕ) : ℝ) = ((s : ℝ) - 1) / 2 := by
    have hR := congrArg (fun a : ℕ => (a : ℝ)) hrN
    rw [Nat.cast_mul, Nat.cast_sub hs] at hR
    norm_num only [Nat.cast_ofNat] at hR
    linarith
  let r : ℝ := ((s : ℝ) - 1) / 2
  let x : ℝ := K + ((ν : ℝ) - 2) * N - r * p
  have hr0 : 0 ≤ r := by
    dsimp [r]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have he : (rawRank s ν K N p : ℝ) = min ((K : ℝ) - N) (max 0 (x + r)) := by
    unfold rawRank
    rw [Nat.cast_min, Nat.cast_sub hNK, cast_trunc_sub]
    congr 2
    push_cast
    rw [Nat.cast_sub hν, Nat.cast_sub hp, hr]
    push_cast
    dsimp [x, r]
    ring
  rw [he]
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · simpa using hr0
  · refine (abs_max0_sub _ _).trans ?_
    change |x + r - x| ≤ r
    have hx : x + r - x = r := by ring
    rw [hx, abs_of_nonneg hr0]


/-- The profile densities give the actual gOuter formula exactly after
scaling; this is an algebraic identity, with no asymptotic premise. -/
theorem density_gOuter_identity (s ν q : ℕ) (hq1 : 1 ≤ q)
    (f g y : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 2)
    (hy : 1 / 3 < y ∧ y ≤ 1) (hq : ⌊1 / y⌋₊ = q)
    (hrel : (q : ℝ) * y + f * y = 1) :
    Mathathon.P108.gOuter s ν (y * g) y =
      y * continuousProfile (costProfile s ν q) f g +
        min (min (1 - y * g)
          (max 0 (1 + ((ν : ℝ) - 2) * (y * g) - ((s : ℝ) - 1) / 2 * y)))
          (y * continuousProfile (zeroProfile s ν q) f g) := by
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hv : 1 - (q : ℝ) * y = y * f := by linarith
  have hu : max 0 (y * g + y * f - y) = y * max 0 (f + g - 1) := by
    rw [mul_max_of_nonneg _ _ hy0, mul_zero]
    congr 1
    ring
  have hm : min (y * g) (y * f) = y * min f g := by
    rw [mul_min_of_nonneg _ _ hy0]
    exact min_comm _ _
  have hC := continuous_linear_profile s q hq1 f g hf0 hf1 hg0 hg1
    (fun a => Mathathon.P108.cRem s ν (2 * q + a))
  change continuousProfile (costProfile s ν q) f g = _ at hC
  have hZ := continuous_zero_profile f g hf0 hf1 hg0 hg1
    (fun a => Mathathon.P108.zRem s ν (2 * q + a))
  change continuousProfile (zeroProfile s ν q) f g = _ at hZ
  unfold Mathathon.P108.gOuter
  rw [if_pos hy, hq]
  dsimp only
  rw [hv, hu, hm, hC, hZ]
  simp only [Nat.add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  · linear_combination -(s + 2 : ℝ) * hrel
  · congr 1
    ring

/-- Finite scale conversion from residue fractions to the actual gOuter
at alpha=N/K and y=p/K. -/
theorem scaled_gOuter_profile (s ν K N p : ℕ) (hK0 : 0 < K) (hp0 : 0 < p)
    (hpK : p ≤ K) (hK3 : K < 3 * p) (hN2 : 2 * N < p) :
    (K : ℝ) * Mathathon.P108.gOuter s ν ((N : ℝ) / K) ((p : ℝ) / K) =
      (p : ℝ) * continuousProfile (costProfile s ν (K / p))
        ((K % p : ℕ) / (p : ℝ)) ((N : ℝ) / p) +
      min (min ((K : ℝ) - N)
        (max 0 ((K : ℝ) + ((ν : ℝ) - 2) * N - ((s : ℝ) - 1) / 2 * p)))
        ((p : ℝ) * continuousProfile (zeroProfile s ν (K / p))
          ((K % p : ℕ) / (p : ℝ)) ((N : ℝ) / p)) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hq1 : 1 ≤ K / p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  have hf0 : (0 : ℝ) ≤ ((K % p : ℕ) : ℝ) / p := by positivity
  have hf1 : ((K % p : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hpR]
    exact_mod_cast (Nat.mod_lt K hp0).le
  have hg0 : (0 : ℝ) ≤ (N : ℝ) / p := by positivity
  have hg1 : (N : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hpR]
    have hN : (2 : ℝ) * N < p := by exact_mod_cast hN2
    linarith
  have hy : 1 / 3 < (p : ℝ) / K ∧ (p : ℝ) / K ≤ 1 := by
    constructor
    · rw [lt_div_iff₀ hKR]
      have h3 : (K : ℝ) < 3 * p := by exact_mod_cast hK3
      linarith
    · rw [div_le_one hKR]
      exact_mod_cast hpK
  have hq : ⌊1 / ((p : ℝ) / K)⌋₊ = K / p := by
    rw [one_div_div, Nat.floor_div_eq_div]
  have hrel : ((K / p : ℕ) : ℝ) * ((p : ℝ) / K) +
      (((K % p : ℕ) : ℝ) / p) * ((p : ℝ) / K) = 1 := by
    have hd : ((K / p : ℕ) : ℝ) * p + (K % p : ℕ) = K := by
      exact_mod_cast (show K / p * p + K % p = K by
        simpa [Nat.mul_comm] using Nat.div_add_mod K p)
    field_simp
    nlinarith
  have hid := density_gOuter_identity s ν (K / p) hq1
    (((K % p : ℕ) : ℝ) / p) ((N : ℝ) / p) ((p : ℝ) / K)
    hf0 hf1 hg0 hg1 hy hq hrel
  have ha : ((p : ℝ) / K) * ((N : ℝ) / p) = (N : ℝ) / K := by field_simp <;> ring
  rw [ha] at hid
  rw [hid, mul_add, mul_min_of_nonneg _ _ hKR.le,
    mul_min_of_nonneg _ _ hKR.le, mul_max_of_nonneg _ _ hKR.le, mul_zero]
  congr 1
  · field_simp
  · congr 1
    · field_simp <;> ring
    · field_simp


noncomputable def poleError (s ν q : ℕ) : ℝ :=
  profileError (costProfile s ν q) + profileError (zeroProfile s ν q) +
    ((s : ℝ) - 1) / 2 + 11

lemma poleError_nonneg (s ν q : ℕ) (hs : 1 ≤ s) : 0 ≤ poleError s ν q := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold poleError
  linarith [profileError_nonneg (costProfile s ν q),
    profileError_nonneg (zeroProfile s ν q)]

/-- Actual sharp outer pole cost versus actual gOuter, with an explicit
finite profile-error constant. This includes rational-floor rounding. -/
theorem sharp_pole_profile_bound (hm : 2 * m + 1 = p) (s ν K N : ℕ)
    (hodd : Odd s) (hs : 5 ≤ s) (hν : 2 ≤ ν) (hNK : N ≤ K)
    (hN2 : 2 * N < p) (hpK : p ≤ K) (hK3 : K < 3 * p) :
    |-(⌊WOsharp s ν K N p⌋ : ℝ) -
      (K : ℝ) * Mathathon.P108.gOuter s ν ((N : ℝ) / K) ((p : ℝ) / K)| ≤
      poleError s ν (K / p) := by
  have hp0 : 0 < p := by omega
  have hK0 : 0 < K := by omega
  have hm' : m = p / 2 := by omega
  subst m
  have hc := actual_cost_profile_approx hm s ν N K hs hNK hN2 hpK hK3
  have hz := actual_zero_profile_approx hm s ν N K hs hNK hN2 hpK hK3
  have hr := actual_raw_rank_approx s ν K N p hodd (by omega) hν hNK (by omega)
  have hR0 : 0 ≤ ((s : ℝ) - 1) / 2 := by
    have hsR : (5 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hmin :
      |min (rawRank s ν K N p : ℝ) (outerZeroCount hm s ν N K : ℝ) -
        min (min ((K : ℝ) - N)
          (max 0 ((K : ℝ) + ((ν : ℝ) - 2) * N - ((s : ℝ) - 1) / 2 * p)))
          ((p : ℝ) * continuousProfile (zeroProfile s ν (K / p))
            ((K % p : ℕ) / (p : ℝ)) ((N : ℝ) / p))| ≤
        ((s : ℝ) - 1) / 2 + profileError (zeroProfile s ν (K / p)) + 2 := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · exact hr.trans (by linarith [profileError_nonneg (zeroProfile s ν (K / p))])
    · exact hz.trans (by linarith)
  have hWO : -(WOsharp s ν K N p : ℝ) =
      -2 * ((∑ c, ∑ i ∈ range (LoC hm N K c), wO hm s ν N K c i : ℚ) : ℝ) +
      min (rawRank s ν K N p : ℝ) (outerZeroCount hm s ν N K : ℝ) := by
    unfold WOsharp
    rw [dif_pos (Fact.out : p.Prime), dif_pos hm]
    push_cast
    ring
  have hflo : (⌊WOsharp s ν K N p⌋ : ℝ) ≤ (WOsharp s ν K N p : ℝ) := by
    exact_mod_cast (Int.floor_le (WOsharp s ν K N p))
  have hfhi : (WOsharp s ν K N p : ℝ) < (⌊WOsharp s ν K N p⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (WOsharp s ν K N p))
  rw [scaled_gOuter_profile s ν K N p hK0 hp0 hpK hK3 hN2, abs_le]
  rw [abs_le] at hc hmin
  unfold poleError
  constructor <;> linarith [hc.1, hc.2, hmin.1, hmin.2]

/-- A fixed constant for the two outer quotient values q=1,2. -/
noncomputable def sharpPoleConstant (s ν : ℕ) : ℝ := poleError s ν 1 + poleError s ν 2

lemma sharpPoleConstant_nonneg (s ν : ℕ) (hs : 1 ≤ s) : 0 ≤ sharpPoleConstant s ν :=
  add_nonneg (poleError_nonneg s ν 1 hs) (poleError_nonneg s ν 2 hs)

/-- The actual sharp pole cost has bounded error uniformly in the approved
finite parameter scope, for K/3<p<=K. No asymptotic hypothesis is assumed. -/
theorem sharp_pole_bound (s ν n p : ℕ) (hscope : ParameterScope s ν)
    (hn : max 1 s ≤ n) (hp : p.Prime) (hpK : p ≤ 40 * n) (hout : 40 * n < 3 * p) :
    |-(⌊WOsharp s ν (40 * n) (3 * n) p⌋ : ℝ) -
      ((40 * n : ℕ) : ℝ) * Mathathon.P108.gOuter s ν (3 / 40)
        ((p : ℝ) / ((40 * n : ℕ) : ℝ))| ≤ sharpPoleConstant s ν := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfact := outer_finite_facts s ν n p 3 hscope hn (by norm_num) hp hout
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hK0 : (0 : ℝ) < (40 * n : ℕ) := by positivity
  have ha : ((3 * n : ℕ) : ℝ) / (40 * n : ℕ) = (3 / 40 : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have h := sharp_pole_profile_bound hfact.1.1 s ν (40 * n) (3 * n)
    hscope.1 hscope.2.1 hscope.2.2.2.1 (by omega) hfact.2.2 hpK hout
  rw [ha] at h
  have hq : 40 * n / p = 1 ∨ 40 * n / p = 2 := by
    have hq1 : 1 ≤ 40 * n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
    have hq3 : 40 * n / p < 3 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hout
    omega
  unfold sharpPoleConstant
  rcases hq with hq | hq
  · rw [hq] at h
    exact h.trans (le_add_of_nonneg_right (poleError_nonneg s ν 2 (by have := hscope.2.1; omega)))
  · rw [hq] at h
    exact h.trans (le_add_of_nonneg_left (poleError_nonneg s ν 1 (by have := hscope.2.1; omega)))

#print axioms actual_class_cost
#print axioms actual_class_zeros
#print axioms actual_cost_profile_approx
#print axioms actual_zero_profile_approx
#print axioms actual_raw_rank_approx
#print axioms scaled_gOuter_profile
#print axioms sharp_pole_profile_bound
#print axioms sharpPoleConstant_nonneg
#print axioms sharp_pole_bound

#print axioms outer_finite_facts
#print axioms selected_sharp_outer
#print axioms class_data
#print axioms sum_wO_class
#print axioms actual_removed_class_cost

end BOuterBridge
