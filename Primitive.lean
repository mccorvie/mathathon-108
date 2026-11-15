import NumericBase

/-!
E608 numerical primitive checker, Codex gpt-6.1-sol, lane C.
PROOF-DRAFT pending final gate. Fauzan re-derivation reusing Firsching's
mo271/Zeta5@be1c0d82 (Apache-2.0; Comparator metadata Paul-Lez).
Models: Apery/Certificates.lean:68-132, Apery/EnergyConst.lean:40-48,
and U49 NumericBase.lean:48-80. Fixed log terms6 and atan pairs3 are
the existing certificate formulas. No old field proof chunks are imported.
-/
set_option autoImplicit false
open Finset

namespace CPrimitive

structure SqrtRow where
  input : ℚ
  bound : ℚ
  lower : Bool
  deriving DecidableEq, Repr, Inhabited

structure LogRow where
  input : ℚ
  bound : ℚ
  k : ℕ
  lower : Bool
  deriving DecidableEq, Repr, Inhabited

inductive AtanTag where
  | series | inverse | half
  deriving DecidableEq, Repr, Inhabited

structure AtanRow where
  input : ℚ
  bound : ℚ
  lower : Bool
  tag : AtanTag
  child : Option ℕ
  sqrt : Option ℕ
  deriving DecidableEq, Repr, Inhabited

def bound (lower : Bool) (q x : ℝ) : Prop := if lower then q ≤ x else x ≤ q

def checkSqrt (r : SqrtRow) : Bool :=
  decide (0 ≤ r.bound) &&
    if r.lower then decide (r.bound ^ 2 ≤ r.input) else decide (r.input ≤ r.bound ^ 2)

def logSeries (y : ℚ) (k : ℕ) : ℚ :=
  2 * ∑ j ∈ range 6, (1 / (2 * (j : ℚ) + 1)) *
    ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * j + 1)

def logLo (y : ℚ) (k : ℕ) : ℚ := logSeries y k - k * (6931471808 / 10000000000)

def logHi (y : ℚ) (k : ℕ) : ℚ :=
  logSeries y k + 2 * ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ 13 /
    (13 * (1 - ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ 2)) -
      k * (6931471803 / 10000000000)

def checkLog (r : LogRow) : Bool :=
  decide (0 < r.input ∧ 1 ≤ 2 ^ r.k * r.input) &&
    if r.lower then decide (r.bound ≤ logLo r.input r.k)
    else decide (logHi r.input r.k ≤ r.bound)

def atanSeries (x : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ range n, (-1 : ℚ) ^ j * (x ^ (2 * j + 1) / (2 * (j : ℚ) + 1))

def piLo : ℚ := 314159265358979323846 / 100000000000000000000
def piHi : ℚ := 314159265358979323847 / 100000000000000000000

def checkSeries (r : AtanRow) : Bool :=
  decide (0 ≤ r.input ∧ r.input < 1 ∧ r.child = none ∧ r.sqrt = none) &&
    if r.lower then decide (r.bound ≤ atanSeries r.input 6)
    else decide (atanSeries r.input 7 ≤ r.bound)

def checkInverse (r c : AtanRow) : Bool :=
  decide (1 < r.input ∧ c.lower = !r.lower ∧ c.input = 1 / r.input ∧ r.sqrt = none) &&
    if r.lower then decide (r.bound ≤ piLo / 2 - c.bound)
    else decide (piHi / 2 - c.bound ≤ r.bound)

def checkHalf (r : AtanRow) (s : SqrtRow) (c : AtanRow) : Bool :=
  checkSqrt s &&
    (decide (0 ≤ r.input ∧ s.lower = !r.lower ∧ s.input = 1 + r.input ^ 2 ∧
      c.lower = r.lower ∧ c.input = r.input / (1 + s.bound)) &&
      if r.lower then decide (r.bound ≤ 2 * c.bound)
      else decide (2 * c.bound ≤ r.bound))

def checkAtan (sq : List SqrtRow) (nodes : List AtanRow) : ℕ → ℕ → Bool
  | 0, i => match nodes[i]? with
    | none => false
    | some r => match r.tag with
      | .series => checkSeries r
      | _ => false
  | fuel + 1, i => match nodes[i]? with
    | none => false
    | some r => match r.tag with
      | .series => checkSeries r
      | .inverse => match r.child with
        | none => false
        | some j => match nodes[j]? with
          | none => false
          | some c => checkInverse r c && checkAtan sq nodes fuel j
      | .half => match r.child, r.sqrt with
        | some j, some k => match nodes[j]?, sq[k]? with
          | some c, some s => checkHalf r s c && checkAtan sq nodes fuel j
          | _, _ => false
        | _, _ => false

/-- PROOF-DRAFT: checked rational square comparisons imply the real enclosure. -/
theorem sqrt_sound {r : SqrtRow} (h : checkSqrt r = true) :
    bound r.lower (r.bound : ℝ) (Real.sqrt (r.input : ℝ)) := by
  cases hd : r.lower
  · simp only [checkSqrt, hd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] at h
    exact Apery.sqrt_le_of_sq_le (by exact_mod_cast h.1) (by exact_mod_cast h.2)
  · simp only [checkSqrt, hd, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Apery.le_sqrt_of_sq_le (by exact_mod_cast h.1) (by exact_mod_cast h.2)

lemma cast_logLo (y : ℚ) (k : ℕ) :
    (logLo y k : ℝ) = 2 * ∑ j ∈ range 6, (1 / (2 * (j : ℝ) + 1)) *
      ((2 ^ k * (y : ℝ) - 1) / (2 ^ k * (y : ℝ) + 1)) ^ (2 * j + 1) -
        k * 0.6931471808 := by
  simp only [logLo, logSeries]
  push_cast
  norm_num

lemma cast_logHi (y : ℚ) (k : ℕ) :
    (logHi y k : ℝ) = 2 * ∑ j ∈ range 6, (1 / (2 * (j : ℝ) + 1)) *
      ((2 ^ k * (y : ℝ) - 1) / (2 ^ k * (y : ℝ) + 1)) ^ (2 * j + 1) +
        2 * ((2 ^ k * (y : ℝ) - 1) / (2 ^ k * (y : ℝ) + 1)) ^ 13 /
          (13 * (1 - ((2 ^ k * (y : ℝ) - 1) / (2 ^ k * (y : ℝ) + 1)) ^ 2)) -
            k * 0.6931471803 := by
  simp only [logHi, logSeries]
  push_cast
  norm_num

/-- PROOF-DRAFT: the six-term exact rational log certificate is sound. -/
theorem log_sound {r : LogRow} (h : checkLog r = true) :
    bound r.lower (r.bound : ℝ) (Real.log (r.input : ℝ)) := by
  have hp : 0 < (r.input : ℝ) := by
    have h1 : 0 < r.input := by
      have := (Bool.and_eq_true_iff.mp h).1
      exact (of_decide_eq_true this).1
    exact_mod_cast h1
  have hk : (1 : ℝ) ≤ 2 ^ r.k * (r.input : ℝ) := by
    have h1 : (1 : ℚ) ≤ 2 ^ r.k * r.input := by
      have := (Bool.and_eq_true_iff.mp h).1
      exact (of_decide_eq_true this).2
    exact_mod_cast h1
  cases hd : r.lower
  · simp only [checkLog, hd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have hh : (logHi r.input r.k : ℝ) ≤ r.bound := by exact_mod_cast h.2
    rw [cast_logHi] at hh
    have hbase := U49.log_le_of_pow_two_upper hp r.k 6 hk
    norm_num only [Nat.cast_ofNat] at hbase hh
    exact hbase.trans hh
  · simp only [checkLog, hd, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh : (r.bound : ℝ) ≤ logLo r.input r.k := by exact_mod_cast h.2
    rw [cast_logLo] at hh
    exact hh.trans (Apery.log_ge_of_pow_two hp r.k 6 hk)

lemma cast_atanSeries (x : ℚ) (n : ℕ) :
    (atanSeries x n : ℝ) =
      ∑ j ∈ range n, (-1 : ℝ) ^ j * ((x : ℝ) ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) := by
  simp only [atanSeries]
  push_cast
  rfl

lemma series_sound {r : AtanRow} (h : checkSeries r = true) :
    bound r.lower (r.bound : ℝ) (Real.arctan (r.input : ℝ)) := by
  have hb : 0 ≤ r.input ∧ r.input < 1 ∧ r.child = none ∧ r.sqrt = none :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hx0 : (0 : ℝ) ≤ r.input := by exact_mod_cast hb.1
  have hx1 : (r.input : ℝ) < 1 := by exact_mod_cast hb.2.1
  have hn := (Bool.and_eq_true_iff.mp h).2
  cases hd : r.lower
  · have hhq : atanSeries r.input 7 ≤ r.bound := by simpa [hd] using hn
    have hh : (atanSeries r.input 7 : ℝ) ≤ r.bound := by exact_mod_cast hhq
    rw [cast_atanSeries] at hh
    exact (Apery.arctan_le_partial hx0 hx1 3).trans hh
  · have hhq : r.bound ≤ atanSeries r.input 6 := by simpa [hd] using hn
    have hh : (r.bound : ℝ) ≤ atanSeries r.input 6 := by exact_mod_cast hhq
    rw [cast_atanSeries] at hh
    exact hh.trans (Apery.arctan_ge_partial hx0 hx1 3)

lemma piLo_le : (piLo : ℝ) ≤ Real.pi := by
  have h := Real.pi_gt_d20.le
  norm_num [piLo] at *
  exact h

lemma pi_le_piHi : Real.pi ≤ (piHi : ℝ) := by
  have h := Real.pi_lt_d20.le
  norm_num [piHi] at *
  exact h

lemma inverse_sound {r c : AtanRow} (h : checkInverse r c = true)
    (hc : bound c.lower (c.bound : ℝ) (Real.arctan (c.input : ℝ))) :
    bound r.lower (r.bound : ℝ) (Real.arctan (r.input : ℝ)) := by
  have hb : 1 < r.input ∧ c.lower = !r.lower ∧ c.input = 1 / r.input ∧ r.sqrt = none :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hx : (0 : ℝ) < r.input := by exact_mod_cast (lt_trans (by norm_num) hb.1)
  have hi : (c.input : ℝ) = 1 / (r.input : ℝ) := by exact_mod_cast hb.2.2.1
  have hn := (Bool.and_eq_true_iff.mp h).2
  cases hd : r.lower
  · have hcdir : c.lower = true := by simpa [hd] using hb.2.1
    have hchild : (c.bound : ℝ) ≤ Real.arctan (1 / (r.input : ℝ)) := by
      simpa [bound, hcdir, hi] using hc
    have hhq : piHi / 2 - c.bound ≤ r.bound := by simpa [hd] using hn
    have hh : (piHi : ℝ) / 2 - (c.bound : ℝ) ≤ r.bound := by exact_mod_cast hhq
    have hbase := Apery.arctan_le_inv hx hchild
    have hpi := pi_le_piHi
    change Real.arctan (r.input : ℝ) ≤ (r.bound : ℝ)
    linarith
  · have hcdir : c.lower = false := by simpa [hd] using hb.2.1
    have hchild : Real.arctan (1 / (r.input : ℝ)) ≤ (c.bound : ℝ) := by
      simpa [bound, hcdir, hi] using hc
    have hhq : r.bound ≤ piLo / 2 - c.bound := by simpa [hd] using hn
    have hh : (r.bound : ℝ) ≤ (piLo : ℝ) / 2 - (c.bound : ℝ) := by exact_mod_cast hhq
    have hbase := Apery.arctan_ge_inv hx hchild
    have hpi := piLo_le
    change (r.bound : ℝ) ≤ Real.arctan (r.input : ℝ)
    linarith

lemma half_sound {r c : AtanRow} {s : SqrtRow} (h : checkHalf r s c = true)
    (hc : bound c.lower (c.bound : ℝ) (Real.arctan (c.input : ℝ))) :
    bound r.lower (r.bound : ℝ) (Real.arctan (r.input : ℝ)) := by
  have hs : checkSqrt s = true := (Bool.and_eq_true_iff.mp h).1
  have rest := (Bool.and_eq_true_iff.mp h).2
  have hb : 0 ≤ r.input ∧ s.lower = !r.lower ∧ s.input = 1 + r.input ^ 2 ∧
      c.lower = r.lower ∧ c.input = r.input / (1 + s.bound) :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp rest).1
  have hn := (Bool.and_eq_true_iff.mp rest).2
  have hx : (0 : ℝ) ≤ r.input := by exact_mod_cast hb.1
  have hsin : (s.input : ℝ) = 1 + (r.input : ℝ) ^ 2 := by exact_mod_cast hb.2.2.1
  have hcin : (c.input : ℝ) = (r.input : ℝ) / (1 + (s.bound : ℝ)) := by
    exact_mod_cast hb.2.2.2.2
  have hsn : (0 : ℝ) ≤ s.bound := by
    have hq : (0 : ℚ) ≤ s.bound := of_decide_eq_true (Bool.and_eq_true_iff.mp hs).1
    exact_mod_cast hq
  have hsreal := sqrt_sound hs
  cases hd : r.lower
  · have hsdir : s.lower = true := by simpa [hd] using hb.2.1
    have hcdir : c.lower = false := by simpa [hd] using hb.2.2.2.1
    have hsr : (s.bound : ℝ) ≤ Real.sqrt (1 + (r.input : ℝ) ^ 2) := by
      simpa [bound, hsdir, hsin] using hsreal
    have hcr : Real.arctan ((r.input : ℝ) / (1 + (s.bound : ℝ))) ≤ (c.bound : ℝ) := by
      simpa [bound, hcdir, hcin] using hc
    have hhq : 2 * c.bound ≤ r.bound := by simpa [hd] using hn
    have hh : 2 * (c.bound : ℝ) ≤ r.bound := by exact_mod_cast hhq
    exact (Apery.arctan_le_half hx hsn hsr hcr).trans hh
  · have hsdir : s.lower = false := by simpa [hd] using hb.2.1
    have hcdir : c.lower = true := by simpa [hd] using hb.2.2.2.1
    have hsr : Real.sqrt (1 + (r.input : ℝ) ^ 2) ≤ (s.bound : ℝ) := by
      simpa [bound, hsdir, hsin] using hsreal
    have hcr : (c.bound : ℝ) ≤ Real.arctan ((r.input : ℝ) / (1 + (s.bound : ℝ))) := by
      simpa [bound, hcdir, hcin] using hc
    have hhq : r.bound ≤ 2 * c.bound := by simpa [hd] using hn
    have hh : (r.bound : ℝ) ≤ 2 * (c.bound : ℝ) := by exact_mod_cast hhq
    exact hh.trans (Apery.arctan_ge_half hx hsr hcr)

/-- PROOF-DRAFT: bounded recursion certifies every accepted atan row; cycles fail closed. -/
theorem atan_sound {sq : List SqrtRow} {nodes : List AtanRow} {fuel i : ℕ} {r : AtanRow}
    (h : checkAtan sq nodes fuel i = true) (hr : nodes[i]? = some r) :
    bound r.lower (r.bound : ℝ) (Real.arctan (r.input : ℝ)) := by
  induction fuel generalizing i r with
  | zero =>
    cases ht : r.tag <;> simp [checkAtan, hr, ht] at h
    exact series_sound h
  | succ fuel ih =>
    cases ht : r.tag with
    | series => exact series_sound (by simpa [checkAtan, hr, ht] using h)
    | inverse =>
      cases hj : r.child with
      | none => simp [checkAtan, hr, ht, hj] at h
      | some j =>
        cases hc : nodes[j]? with
        | none => simp [checkAtan, hr, ht, hj, hc] at h
        | some c =>
          have hh : checkInverse r c = true ∧ checkAtan sq nodes fuel j = true := by
            simpa [checkAtan, hr, ht, hj, hc] using h
          exact inverse_sound hh.1 (ih hh.2 hc)
    | half =>
      cases hj : r.child with
      | none => simp [checkAtan, hr, ht, hj] at h
      | some j =>
        cases hk : r.sqrt with
        | none => simp [checkAtan, hr, ht, hj, hk] at h
        | some k =>
          cases hc : nodes[j]? with
          | none => simp [checkAtan, hr, ht, hj, hk, hc] at h
          | some c =>
            cases hs : sq[k]? with
            | none => simp [checkAtan, hr, ht, hj, hk, hc, hs] at h
            | some s =>
              have hh : checkHalf r s c = true ∧ checkAtan sq nodes fuel j = true := by
                simpa [checkAtan, hr, ht, hj, hk, hc, hs] using h
              exact half_sound hh.1 (ih hh.2 hc)

#print axioms sqrt_sound
#print axioms log_sound
#print axioms atan_sound
end CPrimitive
