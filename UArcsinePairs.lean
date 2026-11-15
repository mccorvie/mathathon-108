import UFiniteEnergy
import ArcBridge.ArcsineAtoms

/-!
E210 / U15, Codex, event work 2026-11-14.
Overall status CONJECTURE, parent gate and human statement comparison pending.
Generic prior inputs: Firsching/Paul-Lez, mo271/Zeta5@be1c0d82070da93c343f93bffd495b8ebc323645.
The first bound below is copied from Apery/ArcsineAtoms.lean:112-142, namespace only changed.
Later adaptations of Apery/EnergyAtoms.lean are located in declaration-map.json.
Apache-2.0; LICENSE copied. No certificate constants or fixed sixteen-atom tables are imported.
-/

noncomputable section

namespace Mathathon.P108.ArcPairs

open MeasureTheory Set Real intervalIntegral Filter Topology Finset
open Apery

-- CITED / PRIOR WORK: Apery/ArcsineAtoms.lean:112-142, namespace adaptation only.
lemma arc_abs_log_integral_le {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∫ θ in (0:ℝ)..2 * π, |Real.log ‖z - arcCurve m r θ‖| ≤
      2 * π * |Real.log (r / 2)| + 4 * π * Real.log (1 + ‖(z - m) / r + sq‖) +
        4 * π * Real.log (1 + ‖(z - m) / r - sq‖) := by
  rw [intervalIntegral.integral_congr_ae (g := fun θ => |Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) (by
      filter_upwards [arc_log_ae hr hsq] with θ hθ _
      rw [hθ])]
  have h1 := abs_log_circle_integral_le ((z - m) / r + sq)
  have h2 := abs_log_circle_integral_le ((z - m) / r - sq)
  have hi1 := (circle_log_integrable 0 ((z - m) / r + sq) 1).abs
  have hi2 := (circle_log_integrable 0 ((z - m) / r - sq) 1).abs
  have hmono : (∫ θ in (0:ℝ)..2 * π, |Real.log (r / 2) +
      Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) ≤
      ∫ θ in (0:ℝ)..2 * π, (|Real.log (r / 2)| +
        |Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖| +
        |Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) := by
    apply integral_mono_on (by positivity)
    · exact ((intervalIntegrable_const.add (circle_log_integrable 0 _ 1)).add
        (circle_log_integrable 0 _ 1)).abs
    · exact (intervalIntegrable_const.add hi1).add hi2
    intro θ _
    exact abs_add_three _ _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hi1) hi2,
    intervalIntegral.integral_add intervalIntegrable_const hi1, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hmono
  linarith



-- CITED / PRIOR WORK: Apery/EnergyAtoms.lean:142-148, namespace and bound-variable renaming.
lemma norm_root_le {z sq : ℂ} (hsq : sq ^ 2 = z ^ 2 - 1) : ‖sq‖ ≤ ‖z‖ + 1 := by
  have h1 : ‖sq‖ ^ 2 = ‖z ^ 2 - 1‖ := by rw [← norm_pow, hsq]
  have h2 : ‖z ^ 2 - 1‖ ≤ ‖z‖ ^ 2 + 1 := by
    calc ‖z ^ 2 - 1‖ ≤ ‖z ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ ^ 2 + 1 := by rw [norm_pow, norm_one]
  nlinarith [norm_nonneg sq, norm_nonneg z]

-- CONJECTURE: generic adaptation of Apery/EnergyAtoms.lean:150-190, arcsine branch only.
theorem arc_point_abs_log_le {m r R : ℝ} (hr : 0 < r) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ R →
      ∫ theta in (0 : ℝ)..2 * Real.pi, |Real.log ‖z - arcCurve m r theta‖| ≤ C := by
  refine ⟨2 * Real.pi * |Real.log (r / 2)| +
    8 * Real.pi * (2 * ((R + |m|) / r) + 1), fun z hz => ?_⟩
  set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
  have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  refine (arc_abs_log_integral_le hr hsq).trans ?_
  have hz' : ‖(z - m) / r‖ ≤ (R + |m|) / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    calc ‖z - m‖ ≤ ‖z‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hs := norm_root_le hsq
  have hq1 : Real.log (1 + ‖(z - m) / r + sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r + sq‖ by positivity)
    have := norm_add_le ((z - m) / r) sq
    linarith
  have hq2 : Real.log (1 + ‖(z - m) / r - sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r - sq‖ by positivity)
    have := norm_sub_le ((z - m) / r) sq
    linarith
  nlinarith [Real.pi_pos]

variable {ι : Type*} [Fintype ι]

def family (m r : ι → ℝ) (i : ι) (theta : ℝ) : ℂ := arcCurve (m i) (r i) theta

def familyBound (m r : ι → ℝ) : ℝ := ∑ i, (|m i| + |r i|)

-- CONJECTURE: continuity, by the generic prior arc-curve lemma.
omit [Fintype ι] in
theorem continuous_family (m r : ι → ℝ) (i : ι) : Continuous (family m r i) :=
  continuous_arcCurve _ _

-- CONJECTURE: finite uniform bound, replacing Apery/EnergyAtoms.lean:68-90 table constants.
theorem family_norm_le (m r : ι → ℝ) (i : ι) (theta : ℝ) :
    ‖family m r i theta‖ ≤ familyBound m r := by
  classical
  refine (norm_arcCurve_le (m i) (r i) theta).trans ?_
  change |m i| + |r i| ≤ ∑ j, (|m j| + |r j|)
  exact Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (m j)) (abs_nonneg (r j)))
    (Finset.mem_univ i)

-- CONJECTURE: generic adaptation of Apery/EnergyAtoms.lean:194-198.
omit [Fintype ι] in
theorem family_log_measurable (m r : ι → ℝ) (i j : ι) :
    Measurable fun p : ℝ × ℝ => Real.log ‖family m r i p.1 - family m r j p.2‖ := by
  apply Real.measurable_log.comp
  exact (continuous_norm.comp (((continuous_family m r i).comp continuous_fst).sub
    ((continuous_family m r j).comp continuous_snd))).measurable

-- CONJECTURE: generic adaptation of Apery/EnergyAtoms.lean:199-218, no fixed atom tables.
theorem family_pair_integrable (m r : ι → ℝ) (hr : ∀ i, 0 < r i) (i j : ι) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖family m r i p.1 - family m r j p.2‖)
      (μcirc.prod μcirc) := by
  obtain ⟨C, hC⟩ := arc_point_abs_log_le (m := m j) (R := familyBound m r) (hr j)
  have hmeas := (family_log_measurable m r i j).aestronglyMeasurable (μ := μcirc.prod μcirc)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with theta
    have h := arc_log_integrable (z := family m r i theta) (m := m j) (hr j)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp h
  · refine Integrable.mono' (integrable_const C) hmeas.norm.integral_prod_right' ?_
    filter_upwards with theta
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have h := hC (family m r i theta) (family_norm_le m r i theta)
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] at h
    simpa [Real.norm_eq_abs, μcirc, family] using h

-- CONJECTURE: generic arcsine branch of Apery/EnergyAtoms.lean:220-237.
theorem arc_preimage_countable {m r : ℝ} (hr : 0 < r) (c : ℂ) :
    {theta : ℝ | c = arcCurve m r theta}.Countable := by
  refine (cos_preimage_countable ((c.re - m) / r)).mono ?_
  intro theta htheta
  simp only [Set.mem_ofPred_eq] at htheta
  have h : c.re = m + r * Real.cos theta := by
    rw [htheta]
    rfl
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  field_simp [hr.ne']
  ring

-- CONJECTURE: generic adaptation of Apery/EnergyAtoms.lean:239-257; includes i=j.
omit [Fintype ι] in
theorem family_pair_ae_ne (m r : ι → ℝ) (hr : ∀ i, 0 < r i) (i j : ι) :
    ∀ᵐ p ∂(μcirc.prod μcirc), family m r i p.1 ≠ family m r j p.2 := by
  rw [ae_iff]
  simp only [not_not]
  have hS : MeasurableSet {p : ℝ × ℝ | family m r i p.1 = family m r j p.2} :=
    (isClosed_eq ((continuous_family m r i).comp continuous_fst)
      ((continuous_family m r j).comp continuous_snd)).measurableSet
  rw [Measure.prod_apply hS]
  have hzero : ∀ theta, μcirc (Prod.mk theta ⁻¹'
      {p : ℝ × ℝ | family m r i p.1 = family m r j p.2}) = 0 := by
    intro theta
    have hc := (arc_preimage_countable (m := m j) (hr j) (family m r i theta)).measure_zero
      (volume : Measure ℝ)
    refine le_antisymm ?_ bot_le
    calc μcirc (Prod.mk theta ⁻¹' {p : ℝ × ℝ | family m r i p.1 = family m r j p.2})
        ≤ volume (Prod.mk theta ⁻¹' {p : ℝ × ℝ | family m r i p.1 = family m r j p.2}) :=
          (Measure.le_iff'.mp Measure.restrict_le_self) _
      _ = volume {phi : ℝ | family m r i theta = family m r j phi} := rfl
      _ = 0 := hc
  simp only [hzero, lintegral_zero]

-- CONJECTURE: finite arcsine-family weak duality; all analytic curve premises are discharged.
theorem arcsine_weak_duality (m r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (a b V : ι → ℝ) (lam M : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hma : ∑ i, a i = lam) (hmb : ∑ i, b i = lam)
    (hpotential : ∀ i, 2 * (∑ j, b j * Mathathon.P108.FiniteDuality.curveKernel (family m r) i j) -
      V i ≤ M) :
    Mathathon.P108.FiniteDuality.quadratic (Mathathon.P108.FiniteDuality.curveKernel (family m r)) a -
      (∑ i, a i * V i) ≤ lam * M -
      Mathathon.P108.FiniteDuality.quadratic (Mathathon.P108.FiniteDuality.curveKernel (family m r)) b := by
  exact Mathathon.P108.FiniteDuality.finite_curve_weak_duality (family m r)
    (continuous_family m r) (family_norm_le m r) (family_pair_integrable m r hr)
    (family_pair_ae_ne m r hr) a b V lam M ha hma hmb hpotential

end Mathathon.P108.ArcPairs

#print axioms Mathathon.P108.ArcPairs.arcsine_weak_duality
#print axioms Mathathon.P108.ArcPairs.family_pair_integrable
#print axioms Mathathon.P108.ArcPairs.family_pair_ae_ne
