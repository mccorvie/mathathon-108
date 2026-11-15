import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..", "scope_alpha_beta")   # read-only import of the E42 package code
sys.path.insert(0, PKG); sys.path.insert(0, HERE)
import sys, random
from fractions import Fraction as Fr

import pkg_ab as P
import bounds as B
random.seed(7)
def Pfun(al, y):
    k = P.fl(1 / y); v = 1 - k * y; u = max(Fr(0), al + v - y); mv = min(al, v)
    dens = {2 * k: al - mv, 2 * k + 1: mv - u, 2 * k + 2: u}
    return (1 - y) - sum(d * (l - 2) for l, d in dens.items())
bad = [0, 0, 0]; n = 0
for _ in range(40000):
    s = random.choice([3, 5, 7, 9, 11, 13]); nu = random.randint(0, 30)
    al = Fr(random.randint(0, 239), 1440); be = Fr(random.randint(1, 200), 80)
    y = Fr(1, 3) + Fr(random.randint(1, 10**6), 10**6) * Fr(2, 3)
    p0, p2 = P.PkgAB(s, nu, al, be), P.PkgAB(s + 2, nu, al, be)
    c0, z0, r0 = p0.outer_parts(y); c2, z2, r2 = p2.outer_parts(y)
    n += 1
    if c2 - c0 > 2 * (1 - y): bad[0] += 1
    if min(r2, z2) > min(r0, z0): bad[1] += 1
    if (c2 - c0) + (min(r2, z2) - min(r0, z0)) < 2 * Pfun(al, y) - (r0 - r2): bad[2] += 1; print('lower pw fail', s, nu, al, be, y)
print(n, 'samples; failures [cost-step<=2(1-y), rank-term nonincreasing, pointwise lower]:', bad)
# closed form of int P
for al in [Fr(0), Fr(1, 40), Fr(3, 40), Fr(1, 8), Fr(1, 6) - Fr(1, 1000)]:
    m = 6000; h = Fr(2, 3) / m
    num = sum(Pfun(al, Fr(1, 3) + (i + Fr(1, 2)) * h) for i in range(m)) * h
    print(f'alpha={al}: midpoint int P = {float(num):.7f}   closed form 2/9 - a + a^2/3 = {float(B.Pi(al)):.7f}')
