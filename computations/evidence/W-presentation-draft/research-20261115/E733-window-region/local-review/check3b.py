#!/usr/bin/env python3
"""check3 (b) follow-up: exact extremes of R_window - R_relaxed at odd nu, La_check < 2 (same sampler as check3.py, seed 3108,
after part (a)); is |diff| <= 1/8 exactly, and where is it attained? (COMPUTED, exact)
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import os, random, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "scope_alpha_beta")))
import rv_window as RW, pkg_ab as PA
rng = random.Random(77)
best = (Fr(0), None); n = over = 0
while n < 150:
    nu = rng.choice(range(1, 24, 2)); a = Fr(rng.randint(1, 39), 240); b = Fr(rng.randint(12, 239), 120)
    if 2 * b + nu * a - 1 >= 3 or PA.La_check(nu, a, b)[0] >= 2: continue
    n += 1; P = PA.PkgAB(7, nu, a, b)
    for _ in range(40):
        x = 3 + Fr(rng.randint(0, 10**6), rng.choice([997, 1009, 4801, 9973]))
        d = RW.R_window(x, a, b, nu) - P.R(x)
        over += abs(d) > Fr(1, 8)
        if abs(d) > best[0]: best = (abs(d), (nu, str(a), str(b), str(x), str(d)))
print(f"{n} points x 40 x: max |R_window - R_rel| = {best[0]} (= 1/8: {best[0] == Fr(1, 8)}), exceeding 1/8: {over}; at {best[1]}")
