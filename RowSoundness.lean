import CellKernel

/-!
E609, Codex lane C. PROOF-DRAFT until final gate. Fauzan re-derivation
using Firsching formalisation, Paul-Lez Comparator metadata, Apache-2.0.
Generic root-definition consumer of every floor, gamma segment and max bit.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open MeasureTheory Set Mathathon.P108
noncomputable section
namespace SplitCells

theorem row_affine (r : Row) (hv : r.Valid) (x : ℝ)
    (hl : (r.l : ℝ) < x) (hr : x < (r.r : ℝ)) :
    innerR 7 6 (3/40) x = (r.a : ℝ)+(r.b : ℝ)*x := by
  rcases hv with ⟨hl0,hlr,hzero,hhalf,horder,hfloor,hzfloor,hmax,ha,hb⟩
  have hg (i : Fin 5) : ⌊(globals i).at x⌋ = r.floors i :=
    floor_of_cert _ _ _ _ (hfloor i) x hl hr
  have hT : ⌊2*Hc 6 (3/40)*x⌋ = r.floors 0 := by
    convert hg 0 using 1 <;> congr 1 <;> norm_num [globals, Aff.at, Hc]
  have hx : ⌊x⌋ = r.floors 1 := by simpa [globals, Aff.at] using hg 1
  have halpha : ⌊(3/40:ℝ)*x⌋ = r.floors 2 := by
    simpa [globals, Aff.at] using hg 2
  have hq : ⌊2*x⌋ = r.floors 3 := by simpa [globals, Aff.at] using hg 3
  have hL : ⌊2*((1-(3/40:ℝ))*x)⌋ = r.floors 4 := by
    convert hg 4 using 1 <;> norm_num [globals, Aff.at] <;> ring
  have hgamma (j : Fin 3) (z : ℝ)
      (hz : z ∈ Ioo ((r.nodes j.castSucc).at x) ((r.nodes (next j)).at x)) :
      gammaIntegrand 7 6 (3/40) x z = (gammaVal r j : ℝ) := by
    have hzf (k : Fin 4) :
        ⌊(xCoeffs k : ℝ)*x+(zCoeffs k : ℝ)*z⌋ = r.zFloors j k := by
      apply zfloor_of_cert _ _ _ _ _ _ _ _ (hzfloor j k) x z hl hr hz.1 hz.2
      fin_cases k <;> norm_num [zCoeffs]
    have hz0 : ⌊x-z⌋ = r.zFloors j 0 := by
      simpa [xCoeffs,zCoeffs,sub_eq_add_neg] using hzf 0
    have hz1 : ⌊x+z⌋ = r.zFloors j 1 := by
      simpa [xCoeffs,zCoeffs] using hzf 1
    have hz2 : ⌊(3/40:ℝ)*x-z⌋ = r.zFloors j 2 := by
      simpa [xCoeffs,zCoeffs,sub_eq_add_neg] using hzf 2
    have hz3 : ⌊(3/40:ℝ)*x+z⌋ = r.zFloors j 3 := by
      simpa [xCoeffs,zCoeffs] using hzf 3
    unfold gammaIntegrand Tc ell
    rw [hT,hz0,hz1,hz2,hz3]
    dsimp [gammaVal]
    push_cast
    norm_num
  have hI (j : Fin 3) := MarginPieces.const_piece_open
    (gammaIntegrand 7 6 (3/40) x) ((r.nodes j.castSucc).at x)
    ((r.nodes (next j)).at x) (gammaVal r j : ℝ)
    (show (r.nodes j.castSucc).at x ≤ (r.nodes (next j)).at x from by
      have hh := affine_nonneg _ _ _ (horder j) x hl.le hr.le
      dsimp [nodeDiff, Aff.at] at hh ⊢
      push_cast at hh
      linarith)
    (fun z hz => hgamma j z hz)
  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x)
    ((r.nodes 0).at x) ((r.nodes 1).at x) ((r.nodes 2).at x)
    ((gammaVal r 0 : ℝ)*((r.nodes 1).at x-(r.nodes 0).at x))
    ((gammaVal r 1 : ℝ)*((r.nodes 2).at x-(r.nodes 1).at x)) (hI 0) (hI 1)
  have hc2 := integral_concat (gammaIntegrand 7 6 (3/40) x)
    ((r.nodes 0).at x) ((r.nodes 2).at x) ((r.nodes 3).at x)
    ((gammaVal r 0 : ℝ)*((r.nodes 1).at x-(r.nodes 0).at x)+
      (gammaVal r 1 : ℝ)*((r.nodes 2).at x-(r.nodes 1).at x))
    ((gammaVal r 2 : ℝ)*((r.nodes 3).at x-(r.nodes 2).at x)) hc1 (hI 2)
  have hG : (∫ z in (0:ℝ)..(1/2), gammaIntegrand 7 6 (3/40) x z) =
      (gammaAff r).at x := by
    have ht := hc2.2
    simp only [hzero,hhalf,Aff.at, Rat.cast_zero, Rat.cast_one, zero_mul,
      add_zero,zero_add,Rat.cast_div,Rat.cast_ofNat] at ht
    rw [ht]
    simp [gammaAff,nodeDiff,next,Aff.at,Fin.sum_univ_succ,hzero,hhalf]
    push_cast
    ring
  have hM : max (sigmaC 6 (3/40) x-nplus x) 0 = (maxAff r).at x := by
    have he : sigmaC 6 (3/40) x-nplus x = (beta r).at x := by
      unfold sigmaC Tc nplus
      rw [hT,hq]
      dsimp [beta,Aff.at]
      push_cast
      norm_num [Hc]
      ring
    rw [he]
    cases hp : r.positive
    · rw [hp] at hmax
      have hh := affine_nonneg _ _ _ hmax x hl.le hr.le
      dsimp [Aff.at] at hh
      push_cast at hh
      have hh' : (beta r).at x ≤ 0 := by dsimp [Aff.at]; linarith
      rw [max_eq_right hh']
      simp [maxAff,hp,Aff.at]
    · rw [hp] at hmax
      have hh := affine_nonneg _ _ _ hmax x hl.le hr.le
      rw [max_eq_left hh]
      simp [maxAff,hp]
  unfold innerR innerGamma
  rw [hG,hM]
  unfold sigmaC Tc innerN Jfun
  rw [hT,hx,halpha,hq,hL]
  have hresult : (resultAff r).at x = (r.a : ℝ)+(r.b : ℝ)*x := by
    simp only [Aff.at,ha,hb]
  rw [←hresult]
  dsimp [resultAff,Aff.at]
  push_cast
  norm_num [Hc]
  ring

theorem row_integral (r : Row) (hv : r.Valid) :
    IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume (r.l : ℝ) (r.r : ℝ) ∧
    (∫ x in (r.l : ℝ)..(r.r : ℝ), innerR 7 6 (3/40) x / x^3) =
      (r.b : ℝ)*(1/(r.l : ℝ)-1/(r.r : ℝ))+
      (r.a : ℝ)/2*(1/(r.l : ℝ)^2-1/(r.r : ℝ)^2) := by
  apply MarginPieces.affine_cube_piece (innerR 7 6 (3/40))
  · exact_mod_cast hv.1
  · exact_mod_cast hv.2.1.le
  · intro x hx
    exact row_affine r hv x hx.1 hx.2

#print axioms row_affine
#print axioms row_integral
end SplitCells
