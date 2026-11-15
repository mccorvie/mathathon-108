#!/usr/bin/env python3
"""rv_zmin_probe.py -- PkgAB.zmin (sampled at l + (r-l)/10^6 inside each piece) vs the exact infimum (rv_core.zmin),
just below the saturation edge beta*.  Shows whether a point outside the domain can pass pkg_ab's own saturation test,
and what the theorem's bounds do there.  Usage: python3 -B rv_zmin_probe.py"""
import os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(1, os.path.join(HERE, "..", "..", "scope_alpha_beta"))
import pkg_ab as PA  # noqa: E402
import rv_core as C  # noqa: E402
for s, nu, al in [(5, 6, Fr(3, 40)), (3, 9, Fr(1, 10)), (5, 8, Fr(11, 80)), (9, 14, Fr(3, 40))]:
    bstar = -C.zmin(C.Out(s + 2, nu, al, 0))
    for eps in (Fr(0), Fr(1, 10 ** 9), Fr(1, 10 ** 7), Fr(1, 10 ** 5)):
        be = bstar - eps
        exact = C.zmin(C.Out(s + 2, nu, al, be))
        pz = PA.PkgAB(s + 2, nu, al, be).zmin()
        try:
            st = 2 * be / 3 + PA.PkgAB(s + 2, nu, al, be).I_out() - PA.PkgAB(s, nu, al, be).I_out()
            res = f"I_out runs; lower<=step<=upper: {C.lower(s, nu, al, be) <= st <= C.upper(be)}"
        except ValueError:
            res = "I_out raises ValueError"
        print(f"s={s} nu={nu} alpha={al} beta=beta*-{eps}: exact zmin(s+2) = {float(exact):+.3e}  PkgAB.zmin = {float(pz):+.3e}"
              f"  pkg_ab test {'passes' if pz >= 0 else 'fails'};  {res}")
