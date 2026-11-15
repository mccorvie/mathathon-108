import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..", "scope_alpha_beta")   # read-only import of the E42 package code
sys.path.insert(0, PKG); sys.path.insert(0, HERE)
import sys, random, time
from fractions import Fraction as Fr

import pkg_ab as P
import bounds as B
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
def valid_outer(s, nu, al, be):
    pk = P.PkgAB(s, nu, al, be)
    if not pk.rank_icpt < pk.rho_r: return None
    try:
        if pk.zmin() < 0: return None
        return pk.I_out()
    except ValueError:
        return None
N = int(sys.argv[2]) if len(sys.argv) > 2 else 250
done = viol = 0; worst = {}; t0 = time.time(); minlo = None
while done < N:
    s = random.choice([3, 5, 5, 5, 7, 7, 9, 11])
    nu = random.randint(1, 22)
    al = Fr(random.randint(1, 239), 1440)            # (0, 1/6)
    be = Fr(random.randint(8, 160), 80)              # [0.1, 2]
    i0 = valid_outer(s, nu, al, be)
    if i0 is None: continue
    i2 = valid_outer(s + 2, nu, al, be)
    if i2 is None: continue
    step = 2 * be / 3 + i2 - i0
    lo, up = B.lower(s, nu, al, be), B.upper(be)
    done += 1
    if not (lo <= step <= up):
        viol += 1; print('VIOLATION', s, nu, al, be, float(lo), float(step), float(up))
    k = s
    rat = float(lo / step)
    w = worst.get(k)
    if w is None or rat < w[0]: worst[k] = (rat, nu, str(al), str(be), float(step), float(lo))
    if minlo is None or step < minlo[0]: minlo = (float(step), s, nu, str(al), str(be), float(lo))
print(f'{done} valid random points, {viol} violations, {time.time()-t0:.0f}s')
for k in sorted(worst): print(f'  step {k}->{k+2}: min lower/step {worst[k][0]:.3f} at nu={worst[k][1]} a={worst[k][2]} b={worst[k][3]} step={worst[k][4]:.4f} lower={worst[k][5]:.4f}')
print('smallest true step seen:', minlo)
