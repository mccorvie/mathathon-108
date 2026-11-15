#!/usr/bin/env python3
"""COMPUTED exact finite period checks and proposed polynomial ranges, Codex U18.
This scouts a tail proof; it is not a Lean theorem or proof of the global decomposition.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'margin'))
import theta as TH
P=TH.Pkg(7,6,'S');pcs=TH.pieces(P.R,TH.inner_breaks(P,F(200),F(240)))
def ev(c,x):return sum((a*x**k for k,a in enumerate(c)),F(0))
def ran(c,l,r):
 xs=[l,r]
 if len(c)>2 and c[2]:
  v=-c[1]/(2*c[2])
  if l<=v<=r:xs.append(v)
 return min(ev(c,x) for x in xs),max(ev(c,x) for x in xs)
G0=F(0);gr=[];qr=[];fr=[];mean=F(0);checks=0;cells=[]
for l,r,a,b in pcs:
 mid=(l+r)/2;nx=TH.fl(mid);na=TH.fl(F(3,40)*mid)
 f0=F(37,40)*(6-2*nx+12*na);f1=F(37,40)*(2-F(36,40))
 for i,j in [(1,7),(1,2),(5,7)]:
  x=l+(r-l)*F(i,j)
  for k in [1,2,3]:
   assert P.R(x+40*k)-P.R(x)==40*k*(f0+f1*x);checks+=1
 Q=[a,b-f0,-f1];qr.append(ran(Q,l,r));fr.append(ran([f0,f1],l,r))
 G=[G0-(f0-F(37,40))*l-f1*l*l/2,f0-F(37,40),f1/2]
 gr.append(ran(G,l,r));G0=ev(G,r);mean+=(f0*(r-l)+f1*(r*r-l*l)/2)/40
 cells.append({'l':str(l),'r':str(r),'R':[str(a),str(b)],'F':[str(f0),str(f1)],'Q':list(map(str,Q)),'G':list(map(str,G)),'Q_range':list(map(str,qr[-1])),'G_range':list(map(str,gr[-1]))})
res={'status':'COMPUTED finite exact checks and polynomial ranges of proposed piece formulas; global identity not Lean-proved',
'F_definition':'(37/40)*(6+2*(x-floorx)-12*((3/40)*x-floor((3/40)*x)))',
'Q_definition':'R(x)-x*F(x)','G_definition':'integral_200^x(F(t)-37/40)dt',
'baseline':[200,240],'pieces':len(pcs),'period_checks':checks,'F_mean':str(mean),'G_end':str(G0),
'F_min':str(min(a for a,b in fr)),'F_max':str(max(b for a,b in fr)),
'G_min':str(min(a for a,b in gr)),'G_max':str(max(b for a,b in gr)),
'Q_min':str(min(a for a,b in qr)),'Q_max':str(max(b for a,b in qr)),'cells':cells}
(HERE/'tail-scout.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k!='cells'},indent=2))
