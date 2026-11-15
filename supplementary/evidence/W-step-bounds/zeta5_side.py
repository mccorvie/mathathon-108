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
        if isinstance(r, dict) and r.get('admissible') and 'floor5' in r:
            rows[(r['alpha'], r['beta'], r['nu'])] = r
cells = [r for (a, b, nu), r in rows.items() if Fr(a) < Fr(1, 6) and 2*Fr(b) - 1 + nu*Fr(a) < 2]
neg = [r for r in cells if r['floor5'] < 0]
lo = lambda r: float(B.lower(5, r['nu'], Fr(r['alpha']), Fr(r['beta'])))
print(f'cells with both s=5 and s=7 in the derived region: {len(cells)}; floor5 < 0 (zeta(5) not excluded) at {len(neg)}')
print(f'min floor5 (deepest point of the zeta(5) floor): {min(r["floor5"] for r in cells):+.4f}')
print(f'min explicit lower bound where floor5 < 0: {min(lo(r) for r in neg):.4f};  min true step there: {min(r["sstep"] for r in neg):.4f}')
w = min(cells, key=lambda r: r['floor5'] + lo(r))
print(f'step-based floor7 bound  min(floor5 + lower) = {w["floor5"] + lo(w):+.4f} at a={w["alpha"]} b={w["beta"]} nu={w["nu"]} (true floor7 {w["floor7"]:+.4f})')
print(f'with the uniform 7/54 only: min(floor5) + 7/54 = {min(r["floor5"] for r in cells) + 7/54:+.4f}')
nus = sorted({r['nu'] for r in neg}); print('nu values with floor5 < 0:', nus)
for nu in nus:
    sub = [r for r in neg if r['nu'] == nu]
    print(f'  nu={nu}: {len(sub)} cells, alpha in [{min(float(Fr(r["alpha"])) for r in sub):.4f},{max(float(Fr(r["alpha"])) for r in sub):.4f}], beta in [{min(float(Fr(r["beta"])) for r in sub):.4f},{max(float(Fr(r["beta"])) for r in sub):.4f}], deepest {min(r["floor5"] for r in sub):+.4f}')
