import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..", "scope_alpha_beta")   # read-only import of the E42 package code
sys.path.insert(0, PKG); sys.path.insert(0, HERE)
import sys, json, time
from fractions import Fraction as Fr
from multiprocessing import Pool
WK = os.path.join(HERE, 'out')
import pkg_ab as P
import bounds as B
def job(nu):
    best = None; cnt = 0; bestLa = None
    for k in range(0, 40):            # alpha = k/240 < 1/6
        al = Fr(k, 240)
        for m in range(1, 161):       # beta = m/80 in (0, 2]
            be = Fr(m, 80)
            if not 2 * be - 1 + nu * al < 2: continue
            try:
                if P.PkgAB(5, nu, al, be).zmin() < 0 or P.PkgAB(7, nu, al, be).zmin() < 0: continue
            except Exception:
                continue
            cnt += 1
            lo = B.lower(5, nu, al, be)
            if best is None or lo < best[0]: best = (lo, str(al), str(be))
    return nu, cnt, best
if __name__ == '__main__':
    t0 = time.time()
    with Pool(8) as pool:
        res = pool.map(job, range(0, 25))
    out = []
    for nu, cnt, best in res:
        if best: out.append((nu, cnt, float(best[0]), best[1], best[2]))
        print(f'nu={nu:2d} outer-valid points {cnt:5d}  min lower bound {float(best[0]) if best else None!s:>8.6} at a={best[1] if best else "-"} b={best[2] if best else "-"}')
    g = min(out, key=lambda t: t[2])
    print('GLOBAL min of explicit lower bound over the outer-valid superset (s=5,7):', g, f'{time.time()-t0:.0f}s')
    json.dump(out, open(WK + '/min_lower.json', 'w'))
