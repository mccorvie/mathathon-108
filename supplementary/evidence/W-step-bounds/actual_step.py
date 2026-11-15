"""The ACTUAL 5 -> 7 step at finite K, from the team's exact determinants (no new computation).

e_n(s, nu) := log Q^prim_K(zeta(s)) / K^2, K = 40n, N = 3n, h = 37n (alpha = 3/40, beta = 37/40), where
Q^prim_K = Delta_K / content(Delta_K). By Gauss's lemma every integer polynomial proportional to Delta_K is an integer
multiple of Q^prim_K, so e_n is the best that any integer normalisation of this determinant can reach at this n.
Values are read from ../witness/out, ../obstacles/out and ../boundary5/out (E16, E19, E20, E25, E35, E38); duplicates
must agree. The package step 2*lam/3 + I_out(7) - I_out(5) is recomputed exactly with ../scope_alpha_beta/pkg_ab.py.
"""
import glob
import json
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
EV = os.path.join(HERE, "..")
sys.path.insert(0, os.path.join(EV, "scope_alpha_beta"))
import pkg_ab as P  # noqa: E402  (read-only)

vals, src = {}, {}
for folder in ("witness", "obstacles", "boundary5"):
    for f in sorted(glob.glob(os.path.join(EV, folder, "out", "delta_s*_nu*_n*.json"))):
        m = re.search(r"delta_s(\d+)_nu(\d+)_n(\d+)\.json$", f)
        s, nu, n = map(int, m.groups())
        v = json.load(open(f)).get("log_Qprim_zeta_over_K2")
        if not v:
            continue
        x = float(v[0])
        key = (s, nu, n)
        if key in vals:
            assert abs(vals[key] - x) < 1e-9, (key, vals[key], x, src[key], f)
            src[key] += ", " + folder
        else:
            vals[key], src[key] = x, folder

al, be = Fr(3, 40), Fr(37, 40)
print("Actual 5 -> 7 step at finite K (alpha = 3/40, beta = 37/40); e_n = log Q^prim_K(zeta(s)) / K^2")
print(f"{'nu':>3} {'n':>2} {'K':>4} {'e_n(5)':>10} {'e_n(7)':>10} {'actual step':>12} {'package step':>13}   sources (s=5 | s=7)")
for nu in sorted({k[1] for k in vals}):
    pk = None
    for n in sorted({k[2] for k in vals if k[1] == nu}):
        a, b = vals.get((5, nu, n)), vals.get((7, nu, n))
        if a is None or b is None:
            continue
        if pk is None:
            pk = 2 * be / 3 + P.PkgAB(7, nu, al, be).I_out() - P.PkgAB(5, nu, al, be).I_out()
        print(f"{nu:>3} {n:>2} {40 * n:>4} {a:+10.5f} {b:+10.5f} {b - a:12.5f} {float(pk):13.5f}   "
              f"{src[(5, nu, n)]} | {src[(7, nu, n)]}")
    if pk is not None:
        print(f"    nu={nu}: package step = {pk} exactly")
