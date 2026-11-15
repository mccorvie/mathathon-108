#!/usr/bin/env python3
"""Self-tests of rv_window.py against team code and known points (COMPUTED).
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import os, sys, random, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "E732-odd-nu")))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..")))
import rv_window as RW
import window as W          # E732 (read-only import)
import check_window3 as CW  # E733 (read-only import; defines feasible())
from window import PA
rng = random.Random(20261115)
# 1. feasibility near x = 3 vs E733's feasible (different algorithm)
dis = n = 0
for _ in range(1500):
    nu = rng.randint(1, 30); a = Fr(rng.randint(1, 1599), 9600); b = Fr(rng.randint(1, 3999), 2000)
    if 2*b + nu*a - 1 >= 3: continue
    for x in (3 + Fr(1, 10**6), 3 + Fr(rng.randint(1, 10**5), 10**4)):
        n += 1
        if RW.feasible_at(x, a, b, nu) != CW.feasible(PA.PkgAB(7, nu, a, b), x): dis += 1
print(f"feasible_at vs E733 check_window3.feasible: {n} (point, x) pairs, {dis} disagreements")
# 2. window cost vs E732 window.R_window and pkg_ab.R (even nu must be exact)
de = do = 0; dmin, dmax = Fr(9), Fr(-9); ne = no = 0
for _ in range(300):
    nu = rng.randint(1, 24); a = Fr(rng.randint(1, 39), 240); b = Fr(rng.randint(12, 239), 120)
    P = PA.PkgAB(7, nu, a, b)
    for _ in range(4):
        x = 3 + Fr(rng.randint(0, 10**6), rng.choice([997, 1009, 4801]))
        rw = RW.R_window(x, a, b, nu)
        if rw != W.R_window(P, x): do += 1
        if nu % 2 == 0:
            ne += 1
            if rw != P.R(x): de += 1
        else:
            no += 1; d = rw - P.R(x); dmin, dmax = min(dmin, d), max(dmax, d)
print(f"R_window (mine) vs E732 window.R_window: {do} mismatches; even nu vs pkg_ab.R: {de} mismatches of {ne}; odd nu R_win - R_rel in [{float(dmin):+.5f}, {float(dmax):+.5f}] ({no} pts)")
# 3. known points from E732's review (gap.json / disc_gap): valid at all x?
for nu, a, b, expect in ((23, Fr(1,240), Fr(9,5), True), (17, Fr(1,240), Fr(53,40), True), (23, Fr(7,240), Fr(3,2), False),
                         (25, Fr(1,240), Fr(19,10), False), (24, Fr(1,240), Fr(9,5), True)):
    t = time.time(); ok, bad, ne_ = RW.valid_all(a, b, nu)
    print(f"  nu={nu} ({a},{b}) valid_all={ok} first_bad={bad} evals={ne_} expect={expect} ({time.time()-t:.1f}s)")
