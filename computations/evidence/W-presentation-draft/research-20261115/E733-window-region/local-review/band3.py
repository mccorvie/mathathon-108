#!/usr/bin/env python3
"""Supplement to hunt_holes.py (c): direct feasibility at x = 3 + 10^-9 on both sides of the line
6 beta = (1 - 6 alpha)(ceil(nu/2) - 1), and at the flagged corner points of extend.json (COMPUTED, exact).
(hunt_holes' 'first_bad' is the first evaluation point of valid_all, i.e. the midpoint of the first constant-feasibility
sub-interval (3, x1); failure there means failure on all of (3, x1).)
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import json, random
from fractions import Fraction as Fr
import rv_window as RW, coverage as CV
x3 = 3 + Fr(1, 10**9)
rng = random.Random(31)
kk = lambda nu: -((-nu)//2) - 1
below_feas = above_infeas = nb = na = 0
for _ in range(1500):
    nu = rng.randint(3, 30); a = Fr(rng.randint(1, 1599), 9600)
    line = (1 - 6*a)*kk(nu)/6; d = Fr(rng.randint(1, 2000), 10**6)
    for b, s in ((line - d, 'below'), (line + d, 'above')):
        if b <= 0 or 2*b + nu*a - 1 >= 3: continue
        f = RW.feasible_at(x3, a, b, nu)
        if s == 'below': nb += 1; below_feas += f
        else: na += 1; above_infeas += (not f)
print(f"band at x = 3 + 1e-9: below the line {nb} points, feasible {below_feas} (must be 0); above {na}, infeasible {above_infeas}")
ext = json.load(open('../extend.json'))
cf = n = 0
for x in ext:
    if x['status'] == 'invalid' and x['why'].startswith('window'):
        a0, a1, b0, b1 = CV.box(x)
        n += 1; cf += RW.feasible_at(x3, a1, b1, x['nu'])
print(f"extend.json window(x=3) boxes: {n}; upper corner feasible at x = 3 + 1e-9: {cf} (must be 0)")
print("example nu=24 (13/96, 3/40) feasible at 3+1e-9:", RW.feasible_at(x3, Fr(13,96), Fr(3,40), 24))
