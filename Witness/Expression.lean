import Witness.Bounds

namespace U11
noncomputable section
open Finset

def alpha : ℝ := 3/40
def lam : ℝ := 37/40

def mass : Fin 15 → ℝ := ![
  1033/10000,1160/10000,1032/10000,917/10000,813/10000,
  719/10000,633/10000,555/10000,484/10000,420/10000,
  361/10000,308/10000,260/10000,216/10000,339/10000]

theorem mass_pos (j : Fin 15) : 0<mass j := by
  fin_cases j <;> norm_num [mass]

theorem mass_sum : (∑ j : Fin 15, mass j)=lam := by
  norm_num [Fin.sum_univ_succ,mass,lam]

def width (j : Fin 15) : ℝ := (25/36)*(49/64)^j.val

def rootWidth (j : Fin 15) : ℝ := (5/6)*(7/8)^j.val

def T (a b : ℝ) : ℝ :=
  2*a*Real.log ((a+Real.sqrt (a^2+b))/2)-2*Real.sqrt (a^2+b)+2*Real.sqrt b

def W (b : ℝ) : ℝ := 4*Real.sqrt b+T 1 b-6*T alpha b

def C6 : ℝ := -2*lam+12*alpha*lam*(1-Real.log alpha)+3*lam^2-2*lam^2*Real.log (2*lam)

def lb6Square15 : ℝ :=
  lam^2*Real.log (25/144)+(233486993/100000000)*Real.log (49/64)
  - ∑ j : Fin 15, mass j*W (width j)+C6

theorem rootWidth_sq (j : Fin 15) : rootWidth j ^2=width j := by
  fin_cases j <;> norm_num [rootWidth, width]

theorem sqrt_width (j : Fin 15) : Real.sqrt (width j)=rootWidth j := by
  rw [←rootWidth_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg]
  unfold rootWidth
  positivity

theorem W_upper (b s l1 u1 la ua log1hi logalo : ℝ)
    (hs : Real.sqrt b=s)
    (h1 : l1≤Real.sqrt (1+b) ∧ Real.sqrt (1+b)≤u1)
    (ha : la≤Real.sqrt (alpha^2+b) ∧ Real.sqrt (alpha^2+b)≤ua)
    (hlog1 : Real.log ((1+Real.sqrt (1+b))/2)≤log1hi)
    (hloga : logalo≤Real.log ((alpha+Real.sqrt (alpha^2+b))/2)) :
    W b ≤ -6*s+2*log1hi-2*l1+12*ua-(9/10)*logalo := by
  unfold W T alpha at *
  norm_num at *
  rw [hs]
  linarith [h1.1,ha.2]

end
end U11
