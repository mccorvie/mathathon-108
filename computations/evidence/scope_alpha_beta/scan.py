#!/usr/bin/env python3
"""scan.py -- zeta(7) dual floor and zeta(5) brackets over (alpha, beta, nu) (EVENT WORK, advocate:scope-alpha-beta,
Claude Opus 5.5).  Package: pkg_ab.py (derivation_beta.md, PROOF-DRAFT), M -> oo.

Per cell (alpha, beta, nu):
  A*(5) = I_out(5) + int_3^X0 R_5/x^3 (exact rationals) + periodic tail beyond X0 (float64, exact pieces);
  A*(7) = A*(5) + I_out(7) - I_out(5) + 2 beta/3      (exact identity R_7 = R_5 + 2 beta x, check_e13 C3);
  LB    = I(sigma) - int V dsigma + C*(nu, alpha, beta) for the best sigma of 56 nested arcsine measures of mass
          beta (float; certified at the decisive cells by certify_min.py);
  U     = beta M0(sigma) - I(sigma) + C*  with M0 a float grid sup (HEURISTIC upper end, achievable value).
  floor7 = A*(7) + LB  (no comparison measure gives zeta(7) a smaller margin);  zeta(5) bracket [A*(5)+LB, A*(5)+U].
Admissibility flags: La >= 0 (inner allocation), z_beta >= 0 (outer saturation), alpha < 1/6 (2N < p, one removed
pole per outer class; outside it the outer formula is not derived), nu even.
Usage: python3 scan.py coarse|fine|<file of cells>  [workers=4]  -> out/scan_<tag>.json, out/scan_<tag>.log
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def cell(args):
    al, be, nu = Fr(args[0]), Fr(args[1]), int(args[2])
    import pkg_ab as PA
    t0 = time.time()
    out = dict(alpha=str(al), beta=str(be), nu=nu, alpha_f=float(al), beta_f=float(be))
    la = PA.La_check(nu, al, be)
    out["La_min"] = str(la[0])
    P5 = PA.PkgAB(5, nu, al, be)
    P7 = PA.PkgAB(7, nu, al, be)
    try:
        zm = min(P5.zmin(), P7.zmin())
    except Exception as e:  # noqa: BLE001
        zm = None
        out["err"] = repr(e)
    out["zmin"] = float(zm) if zm is not None else None
    out["valid_alpha"] = al < Fr(1, 6)
    out["admissible"] = bool(la[0] >= 0 and zm is not None and zm >= 0)
    if zm is None or zm < 0:
        out["seconds"] = round(time.time() - t0, 1)
        return out
    X0 = P5.X0()
    inn5 = P5.int_R_x3(3, X0)
    io5, io7 = P5.I_out(), P7.I_out()
    A5, Fb = P5.A_star_float(io5, inn5)
    A7 = A5 + float(io7 - io5) + float(2 * be / 3)
    LB, sig, info = PA.lb_opt(nu, al, be)
    U, M0 = PA.U_float(nu, al, be, sig)
    out.update(I_out5=str(io5), I_out7=str(io7), inner5_3_X0=str(inn5), X0=str(X0), P=P5.P, Fbar5=str(Fb),
               A5=A5, A7=A7, LB=LB, U=U, M0=M0, floor7=A7 + LB, top7=A7 + U, floor5=A5 + LB, top5=A5 + U,
               sstep=float(io7 - io5 + 2 * be / 3), lb_info=info,
               sigma=[[str(a), str(b), str(c)] for a, b, c in sig])
    out["seconds"] = round(time.time() - t0, 1)
    return out


def grid(tag):
    if tag == "coarse":
        als = [Fr(k, 40) for k in range(1, 9)]
        bes = [Fr(m, 40) for m in range(26, 46)]           # 0.65 .. 1.125
        nus = [2, 4, 6, 8, 10]
        return [(str(a), str(b), n) for a in als for b in bes for n in nus]
    if tag.startswith("file:"):
        return [tuple(x) for x in json.load(open(tag[5:]))]
    raise ValueError(tag)


def main():
    tag = sys.argv[1] if len(sys.argv) > 1 else "coarse"
    workers = 4
    for a in sys.argv[2:]:
        if a.startswith("workers="):
            workers = min(4, int(a.split("=")[1]))
    cells = grid(tag)
    name = tag.replace("file:", "").replace("/", "_").replace(".json", "")
    outp = os.path.join(HERE, "out", f"scan_{os.path.basename(name)}.json")
    done = {}
    if os.path.exists(outp):
        for r in json.load(open(outp)):
            done[(r["alpha"], r["beta"], r["nu"])] = r
    todo = [c for c in cells if (str(Fr(c[0])), str(Fr(c[1])), int(c[2])) not in done]
    print(f"{len(cells)} cells, {len(todo)} to do, {workers} workers", flush=True)
    t0 = time.time()
    res = list(done.values())
    with Pool(workers) as pool:
        for i, r in enumerate(pool.imap_unordered(cell, todo, chunksize=1)):
            res.append(r)
            if i % 20 == 0 or i == len(todo) - 1:
                json.dump(res, open(outp, "w"), indent=0)
                print(f"  {i + 1}/{len(todo)}  {time.time() - t0:.0f}s  last: a={r['alpha']} b={r['beta']} nu={r['nu']}"
                      f" floor7={r.get('floor7', float('nan')):+.4f} ({r['seconds']}s)", flush=True)
    json.dump(res, open(outp, "w"), indent=0)
    print("wrote", outp)


if __name__ == "__main__":
    main()
