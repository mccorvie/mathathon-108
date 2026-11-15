#!/usr/bin/env python3
"""selftest.py -- soundness checks of run.py's cell bounds against dense float sampling (not part of the proof;
a bug detector).  Fixed seed 108.  python3 selftest.py -> out/selftest.log"""
import random, sys, os
import numpy as np
import run
from run import L, mpf, Fr, TH
random.seed(108)
lines = []
for nu in (2, 6, 10):
    ent, rho = run.load_rho(nu)
    comps = [run.Comp(a, b, c) for a, b, c in rho]
    fl = lambda t: 2 * sum(float(c) * TH.np_Uarc(float(a), float(b), t) for a, b, c in rho) - TH.np_V(nu, t)
    worst, worst_pt = -1, 0.0
    for trial in range(300):
        t0 = random.choice([random.uniform(0, 1.2), random.uniform(0, 0.02), random.uniform(0, 4)])
        w = 10 ** random.uniform(-7, -1)
        if trial % 10 == 0:
            t0 = 0.0
        a, b = mpf(t0), mpf(t0 + w)
        D0, D1, Dc = run.point_data(a, comps, nu), run.point_data(b, comps, nu), run.point_data((a + b) / 2, comps, nu)
        ub = float(run.cell_ub(D0, D1, Dc, comps))
        ts = np.linspace(t0, t0 + w, 401)
        fm = float(fl(ts).max())
        worst = max(worst, fm - ub)
        v = run.fsum_val(Dc)
        worst_pt = max(worst_pt, abs(float(v.lo) - float(fl(np.array([float((a + b) / 2)]))[0])))
    lines.append(f"nu={nu}: 300 random cells, max(float sample max - certified cell ub) = {worst:.3e} (must be <= ~1e-13); "
                 f"max |iv point value - theta float| = {worst_pt:.2e}")
    print(lines[-1], flush=True)
open(os.path.join(run.OUT, "selftest.log"), "w").write("\n".join(lines) + "\n")
