#!/usr/bin/env python3
"""Check 3 of the E733 review: does E730's bound apply on the window region OUTSIDE the derived region? (COMPUTED, exact)
(a) even nu, points with La_check < 0: my window cost R_window (rv_window, no L >= 0 constraint, non-greedy up-assignment)
    must equal pkg_ab.PkgAB.R exactly (Fauzan's allocation, (5.4)-(5.6)), at 40 x per point incl. x near 3 and breakpoints;
    separately at points that are also window-VALID (rv_window.valid_all).
(b) odd nu, points with La_check < 2: R_window - R_relaxed in [-1/8, 1/8], Q_true = R_window - x F >= -3/8.
(c) the alpha = 0 column of the E730 nu = 2 cover: every box [0, 1/48] x [b0, b1] with b1 > 2/3 certified (E730's nu-free
    argument that E733 relies on at alpha = 0, including nu >= 25).
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import json, os, random, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "scope_alpha_beta")))
import rv_window as RW, coverage as CV
import pkg_ab as PA
rng = random.Random(3108)

def xs(al, be, nu):
    out = [3 + Fr(1, 10**7), 3 + Fr(1, 1000)]
    out += [3 + Fr(rng.randint(0, 10**6), rng.choice([997, 1009, 4801, 9973])) for _ in range(30)]
    for c in (Fr(2), 2 * al, 1 - al, 1 + al):
        k = int(3 * c) + 1
        for _ in range(4):
            out += [Fr(k) / c + Fr(1, 10**6), Fr(k) / c - Fr(1, 10**6)]; k += 1
    return [x for x in out if x > 3]

res = {}
# (a)
n_pts = n_x = mism = n_valid = 0
while n_pts < 120:
    nu = rng.choice(range(2, 25, 2)); a = Fr(rng.randint(1, 39), 240); b = Fr(rng.randint(12, 239), 120)
    if 2 * b + nu * a - 1 >= 3 or PA.La_check(nu, a, b)[0] >= 0: continue
    n_pts += 1
    P = PA.PkgAB(7, nu, a, b)
    v = RW.valid_all(a, b, nu)[0]; n_valid += v
    for x in xs(a, b, nu):
        n_x += 1
        if RW.R_window(x, a, b, nu) != P.R(x): mism += 1
res["a"] = dict(points=n_pts, window_valid_points=n_valid, x_evals=n_x, mismatches=mism)
print(f"(a) even nu, La_check < 0: {n_pts} points ({n_valid} window-valid), {n_x} x values, R_window != pkg_ab.R at {mism}")
# (b)
n_pts = n_x = 0; dmin, dmax, qmin = Fr(9), Fr(-9), Fr(9)
while n_pts < 120:
    nu = rng.choice(range(1, 24, 2)); a = Fr(rng.randint(1, 39), 240); b = Fr(rng.randint(12, 239), 120)
    if 2 * b + nu * a - 1 >= 3 or PA.La_check(nu, a, b)[0] >= 2: continue
    n_pts += 1
    P = PA.PkgAB(7, nu, a, b)
    for x in xs(a, b, nu):
        n_x += 1
        rw = RW.R_window(x, a, b, nu); d = rw - P.R(x)
        dmin, dmax = min(dmin, d), max(dmax, d); qmin = min(qmin, rw - x * P.F(x))
res["b"] = dict(points=n_pts, x_evals=n_x, diff_min=float(dmin), diff_max=float(dmax), Qtrue_min=float(qmin))
print(f"(b) odd nu, La_check < 2: {n_pts} points, {n_x} x; R_window - R_rel in [{float(dmin):+.5f}, {float(dmax):+.5f}] (|.| <= 1/8?), min Q_true {float(qmin):+.5f} (>= -3/8?)")
# (c)
c2 = json.load(open(os.path.join(CV.E730, "cover-nu2.json")))
col = [x for x in c2 if Fr(x["alpha"][0]) == 0 and Fr(x["beta"][1]) > Fr(2, 3)]
st = {}
for x in col: st[x["status"]] = st.get(x["status"], 0) + 1
mn = min(x["floor_lo"] for x in col if x["status"] == "certified")
res["c"] = dict(boxes=len(col), statuses=st, min_floor_lo=mn)
print(f"(c) nu = 2 cover, column alpha in [0, 1/48] with beta1 > 2/3: {len(col)} boxes {st}, min floor_lo {mn:.4f}")
res["reviewer"] = "Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"
json.dump(res, open(os.path.join(HERE, "check3.json"), "w"), indent=1)
