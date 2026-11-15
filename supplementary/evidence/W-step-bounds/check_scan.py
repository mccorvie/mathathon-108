import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..", "scope_alpha_beta")   # read-only import of the E42 package code
sys.path.insert(0, PKG); sys.path.insert(0, HERE)
import json, sys
from fractions import Fraction as Fr

import bounds as B
base = PKG
rows = {}
for f in ['scan_coarse.json', 'scan_fine.json', 'scan_lowbeta.json', 'scan_fine2.json']:
    try: d = json.load(open(f'{base}/out/{f}'))
    except Exception: continue
    if isinstance(d, dict): d = d.get('rows', list(d.values()))
    for r in d:
        if isinstance(r, dict) and r.get('admissible') and 'I_out5' in r:
            rows[(r['alpha'], r['beta'], r['nu'])] = r
viol_lo = viol_up = 0; n = 0; ratios = []; ratiosW = []; tight = None
for (a, b, nu), r in rows.items():
    al, be = Fr(a), Fr(b)
    if not al < Fr(1, 6): continue
    Aic = 2 * be - 1 + nu * al
    if not Aic < 2: continue        # s = 5 domain, condition (iii)
    n += 1
    step = 2 * be / 3 + Fr(r['I_out7']) - Fr(r['I_out5'])   # exact
    lo, up = B.lower(5, nu, al, be), B.upper(be)
    if lo > step: viol_lo += 1; print('LOWER VIOLATION', a, b, nu, float(lo), float(step))
    if up < step: viol_up += 1; print('UPPER VIOLATION', a, b, nu, float(up), float(step))
    ratios.append(float(lo / step)); ratiosW.append(float(B.laneW(5, nu, al, be) / step))
    if tight is None or step - lo < tight[0]: tight = (step - lo, a, b, nu, float(step), float(lo))
    if abs(float(step) - r['sstep']) > 1e-9: print('sstep mismatch', a, b, nu)
print(f'cells (alpha<1/6, A<2): {n}; lower violations {viol_lo}; upper violations {viol_up}')
print(f'lower/step: min {min(ratios):.3f} median {sorted(ratios)[len(ratios)//2]:.3f} max {max(ratios):.3f}')
print(f'laneW/step: min {min(ratiosW):.3f} median {sorted(ratiosW)[len(ratiosW)//2]:.3f} max {max(ratiosW):.3f}')
print('tightest lower (gap, a, b, nu, step, lower):', tight)
print('template (3/40, 37/40, 6): lower', float(B.lower(5, 6, Fr(3,40), Fr(37,40))), 'upper', float(B.upper(Fr(37,40))), 'uniform', float(B.uniform(Fr(3,40))), 'true', 751/768)
