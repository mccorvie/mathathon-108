#!/usr/bin/env python3
"""COMPUTED proof proposals; every generated function identity is re-proved in Lean.
Codex U18/E213. Reads theta.py, never stored A200 endpoints.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,math
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'margin'))
import theta as TH
P=TH.Pkg(7,6,'S')
pcs=TH.pieces(P.R,TH.inner_breaks(P,F(3),F(200)))

def q(v):
 v=F(v)
 return (f'(-({-v.numerator}/{v.denominator}:ℝ))' if v.numerator<0 else f'({v.numerator}/{v.denominator}:ℝ)') if v.denominator!=1 else f'({v.numerator}:ℝ)'

def aff(c,b=F(0)):
 return f'({q(c)} + {q(b)} * x)' if b else q(c)

def fix(expr,n):
 return f'  have : (⌊{expr}⌋ : ℤ) = ({n}:ℤ) := by\n    apply Int.floor_eq_iff.mpr\n    constructor <;> norm_num [Hc] <;> linarith\n'

meta=[]

def leaf(k,cell):
 l,r,a,b=cell;x=(l+r)/2
 nx=math.floor(x);na=math.floor(F(3,40)*x)
 bounds=[(F(0),F(0)),(F(1,2),F(0))]
 fx=x-nx;fa=F(3,40)*x-na
 bounds.append((-F(nx),F(1)) if fx<F(1,2) else (F(nx+1),F(-1)))
 bounds.append((-F(na),F(3,40)) if fa<F(1,2) else (F(na+1),-F(3,40)))
 bounds=sorted(set(bounds),key=lambda cb:cb[0]+cb[1]*x)
 T=math.floor(2*P.H*x);qx=math.floor(2*x);nl=math.floor(2*TH.LAM*x)
 code=f'''-- CONJECTURE: generated proof from exact root definitions, parent gate pending.
lemma r_{k} (x : ℝ) (hl : {q(l)} < x) (hr : x < {q(r)}) :
    innerR 7 6 (3/40) x = {q(a)} + {q(b)} * x := by
'''
 floors=[('hT','2 * Hc 6 (3/40) * x',T),('hx','x',nx),('ha','(3/40:ℝ) * x',na),('hq','2 * x',qx),('hL','2 * ((1-(3/40:ℝ))*x)',nl)]
 for name,e,n in floors:
  code+=fix(e,n).replace('  have :','  have '+name+' :')
 ints=[]
 for j,((c0,b0),(c1,b1)) in enumerate(zip(bounds,bounds[1:])):
  z=((c0+b0*x)+(c1+b1*x))/2
  zfloors=[('hz0','x-z',math.floor(x-z)),('hz1','x+z',math.floor(x+z)),('hz2','(3/40:ℝ)*x-z',math.floor(F(3,40)*x-z)),('hz3','(3/40:ℝ)*x+z',math.floor(F(3,40)*x+z))]
  ellx=TH.ell(x,z);ella=TH.ell(F(3,40)*x,z);g=(T-3*ella)*(T+3*ella-ellx-7)
  lo,hi=aff(c0,b0),aff(c1,b1)
  val=f'{q(g)} * ({hi}-{lo})'
  code+=f'  have hI{j} := const_piece_open (gammaIntegrand 7 6 (3/40) x) {lo} {hi} {q(g)} (by linarith) (by\n    intro z hz\n    obtain ⟨hzl,hzr⟩ := hz\n'
  for name,e,n in zfloors:
   code+='  '+fix(e,n).replace('  have :','  have '+name+' :').replace('\n','\n  ').rstrip()+'\n'
  code+=f'    norm_num [gammaIntegrand, Tc, ell, hT, hz0, hz1, hz2, hz3])\n'
  ints.append(val)
 if len(ints)==1: code+='  have hG := hI0.2\n'
 else:
  code+='  have hc1 := integral_concat (gammaIntegrand 7 6 (3/40) x) '+aff(*bounds[0])+' '+aff(*bounds[1])+' '+aff(*bounds[2])+' ('+ints[0]+') ('+ints[1]+') hI0 hI1\n'
  for j in range(2,len(ints)):
   code+=f'  have hc{j} := integral_concat (gammaIntegrand 7 6 (3/40) x) '+aff(*bounds[0])+' '+aff(*bounds[j])+' '+aff(*bounds[j+1])+' ('+'+'.join(ints[:j])+') ('+ints[j]+f') hc{j-1} hI{j}\n'
  code+=f'  have hG := hc{len(ints)-1}.2\n'
 code+='  unfold innerR innerGamma\n  rw [hG]\n  unfold innerN Jfun sigmaC Tc nplus\n  simp only [hT,hx,ha,hq,hL]\n  norm_num [Hc]\n'
 sl=P.H*x-F(T,2);np=(2*x-qx)/2
 side='left' if sl-np>=0 else 'right'
 code+=f'  try (rw [max_eq_{side}]; rotate_left; linarith)\n  ring\n'
 v=b*(1/l-1/r)+a/2*(1/l**2-1/r**2)
 code+=f'''lemma i_{k} : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume {q(l)} {q(r)} ∧
    ∫ x in {q(l)}..{q(r)}, innerR 7 6 (3/40) x / x^3 = {q(v)} := by
  have h := affine_cube_piece (innerR 7 6 (3/40)) {q(l)} {q(r)} {q(a)} {q(b)} (by norm_num) (by norm_num)
    (fun x hx => r_{k} x hx.1 hx.2)
  norm_num at h ⊢
  exact h
'''
 return code,v

out=HERE/'MarginPieces';out.mkdir(exist_ok=True)
chunk=int(sys.argv[1]) if len(sys.argv)>1 else 20
limit=int(sys.argv[2]) if len(sys.argv)>2 else len(pcs)
for start in range(0,min(limit,len(pcs)),chunk):
 text='import MarginPieces\n/- All mathematical declarations generated in this module have status CONJECTURE pending the parent gate and human comparison. -/\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nopen MeasureTheory Set Mathathon.P108\nnamespace MarginPieces\n'
 total=F(0)
 for k in range(start,min(start+chunk,limit,len(pcs))):
  code,v=leaf(k,pcs[k]);text+=code;total+=v
 stop=min(start+chunk,limit,len(pcs))
 left,right=pcs[start][0],pcs[stop-1][1]
 text+=f'lemma chunk_{start//chunk} : IntervalIntegrable (fun x => innerR 7 6 (3/40) x / x^3) volume {q(left)} {q(right)} ∧\n    ∫ x in {q(left)}..{q(right)}, innerR 7 6 (3/40) x / x^3 = {q(total)} := by\n'
 text+=f'  have h := i_{start}\n'
 accum=pcs[start][3]*(1/pcs[start][0]-1/pcs[start][1])+pcs[start][2]/2*(1/pcs[start][0]**2-1/pcs[start][1]**2)
 for k in range(start+1,stop):
  l0,r0,a0,b0=pcs[k]
  val=b0*(1/l0-1/r0)+a0/2*(1/l0**2-1/r0**2)
  text+=f'  have h := integral_concat (fun x => innerR 7 6 (3/40) x / x^3) {q(left)} {q(l0)} {q(r0)} {q(accum)} {q(val)} h i_{k}\n  norm_num at h\n'
  accum+=val
 text+='  norm_num at h ⊢\n  exact h\n'
 text+='end MarginPieces\n'
 (out/f'Chunk{start//chunk:03}.lean').write_text(text)
 meta.append({'chunk':start//chunk,'first':start,'last':min(start+chunk,limit,len(pcs))-1,'sum':str(total)})
(HERE/'generated.json').write_text(json.dumps({'status':'COMPUTED proof proposals, not certification','pieces':len(pcs),'chunks':meta,'total_generated_integral':str(sum((F(x['sum']) for x in meta),F(0)))},indent=2)+'\n')
print('generated',limit,'of',len(pcs),'pieces in',len(meta),'chunks')
