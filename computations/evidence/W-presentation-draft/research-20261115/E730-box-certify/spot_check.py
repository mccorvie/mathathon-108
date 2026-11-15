"""[108/N E730] Spot check: exact package values (scope_alpha_beta/scan.cell) at 23 points off the scan grid vs the cover.
Run from any folder: python3 spot_check.py (imports scope_alpha_beta/scan.py and pkg_ab.py read-only)."""
import sys, json, os
from fractions import Fraction as Fr
from multiprocessing import Pool
sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'scope_alpha_beta')))
import scan
E = os.path.dirname(os.path.abspath(__file__)) + '/'
pts = [("3/20", b, 10) for b in ("3/20", "7/40", "1/5", "1/4", "3/10", "2/5")] + \
      [("3/20", b, 8) for b in ("7/20", "3/8", "2/5", "9/20", "1/2")] + \
      [("1/40", b, 2) for b in ("13/10", "8/5", "19/10")] + [("1/20", b, 6) for b in ("13/10", "8/5", "17/10")] + \
      [("1/40", b, 10) for b in ("13/10", "3/2", "17/10")] + [("1/10", b, 4) for b in ("6/5", "3/2", "17/10")]
if __name__ == "__main__":
    with Pool(10) as p:
        res = p.map(scan.cell, pts)
    out = []
    for (a, b, nu), r in zip(pts, res):
        a_, b_ = Fr(a), Fr(b)
        boxes = [x for x in json.load(open(E + f'cover-nu{nu}.json')) if Fr(x['alpha'][0]) <= a_ <= Fr(x['alpha'][1]) and Fr(x['beta'][0]) <= b_ <= Fr(x['beta'][1])]
        bl = [(x['status'], round(x.get('floor_lo', float('nan')), 4)) for x in boxes]
        iii = 2 * b_ + nu * a_ - 1 < 3
        line = dict(nu=nu, alpha=a, beta=b, admissible=r['admissible'], iii=iii, zmin=r['zmin'], La_min=r['La_min'], floor7=r.get('floor7'), boxes=bl, seconds=r['seconds'])
        ok = r.get('floor7') is None or all(s != 'certified' or lo <= r['floor7'] for s, lo in bl)
        line['consistent'] = ok
        print(line, flush=True); out.append(line)
    json.dump(out, open(E + 'spot-check.json', 'w'), indent=1)
