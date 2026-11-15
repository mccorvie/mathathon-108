#!/usr/bin/env python3
"""rv_real_nu.py -- is the hypothesis "nu integer" used?  Search for violations of the theorem's bounds at NON-integer nu
(outside the stated domain), with pkg_ab's own formulas (PkgAB accepts a Fraction nu) and rv_core.
Usage: python3 -B rv_real_nu.py [n=400] [seed=1]"""
import os, random, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(1, os.path.join(HERE, "..", "..", "scope_alpha_beta"))
import pkg_ab as PA  # noqa: E402
import rv_core as C  # noqa: E402
n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
viol_lo = viol_up = tested = 0
worst = None
for _ in range(n):
    s = rng.choice([3, 5, 7, 9])
    nu = Fr(rng.randint(1, 300), 10)
    if nu.denominator == 1:
        continue
    al = Fr(rng.randint(1, 1666), 10000)
    r = Fr(s - 1, 2)
    bmax = (r + 1 - nu * al) / 2
    bsat = max(-C.zmin(C.Out(s + 2, nu, al, 0)), Fr(1, 10 ** 4))
    if bsat >= bmax:
        continue
    be = rng.choice([bsat, bsat + (bmax - bsat) * Fr(rng.randint(1, 999), 1000)])
    try:
        st = 2 * be / 3 + PA.PkgAB(s + 2, nu, al, be).I_out() - PA.PkgAB(s, nu, al, be).I_out()
    except ValueError:
        continue
    assert st == 2 * be / 3 + C.step_outer(s, nu, al, be)
    tested += 1
    lo, up = C.lower(s, nu, al, be), C.upper(be)
    if st < lo:
        viol_lo += 1
        if worst is None or lo - st > worst[0]:
            worst = (lo - st, s, nu, al, be, st, lo)
    if st > up:
        viol_up += 1
print(f"{tested} points with non-integer nu (other domain conditions hold): lower violated at {viol_lo}, upper at {viol_up}")
if worst:
    g, s, nu, al, be, st, lo = worst
    print(f"largest lower violation {float(g):.6f} at s={s} nu={nu} alpha={al} beta={be}: step {st} ({float(st):.6f}) < lower {lo} ({float(lo):.6f})")
