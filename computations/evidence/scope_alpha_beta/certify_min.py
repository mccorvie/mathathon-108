#!/usr/bin/env python3
"""certify_min.py -- interval-arithmetic certification of the zeta(7) dual floor at chosen (alpha, beta, nu) cells
(EVENT WORK, advocate:scope-alpha-beta, Claude Opus 5.5).  Reuses ../certify/ by import (ivlib: 113-bit mpmath.iv,
own atan; run.py: J_iv, Vinc_iv, padd/pint/pev/pdef/prange), never edits it.  The method is certify/run.py's
(astar: exact periods + rigorous remainder; cmd_LB: Jensen cells for the concave part, chord cells for the convex
part), with the period 40 replaced by pkg_ab's period P and alpha, beta as parameters.

  A*(7) enclosure: I_out(7) + int_3^X0 R_7/x^3 exact (X0 = 200 rounded up to a multiple of P), Pn exact periods
         summed in iv, remainder Fbar/X + (Gbar + Qbar/2)/X^2 + [2 minH + minP1, 2 maxH + maxP1]/X^3.
  LB enclosure: I(sigma) (ivlib.I_rho, nested) - upper bound of int V dsigma + C*(nu, alpha, beta) (ivlib.Cstar with
         lam -> beta, which is Xu's C*(q, alpha, beta)).
  floor7 >= A*.lo + LB.lo  (exact rational endpoints).
Usage: python3 certify_min.py <cells.json: [[alpha, beta, nu], ...]> [N=1000]  -> out/certified.json, .log
The trial measures sigma are recomputed by pkg_ab.lb_opt (deterministic) and stored with the result.
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "certify"))
import pkg_ab as PA  # noqa: E402
import ivlib as L    # noqa: E402  (sets iv.prec = 113)
from ivlib import iv, ivq, to_fr, nonneg  # noqa: E402
import run as CR     # noqa: E402  (certify/run.py, read-only import; its main is guarded)

LOG = []


def log(s=""):
    print(s, flush=True)
    LOG.append(s)


def astar_cert(P, Pn=45):
    io = P.I_out()
    X0 = P.X0(200)
    Pp = P.P
    inX0 = P.int_R_x3(3, X0)
    base = PA.pieces(P.R, P.inner_breaks(X0, X0 + Pp))
    assert base[0][0] == X0 and base[-1][1] == X0 + Pp and all(x[1] == y[0] for x, y in zip(base, base[1:]))
    pcs = []
    for l, r, a, b in base:
        a1, b1 = PA.affine_fit(lambda x: P.R(x + Pp), l, r)
        f0, f1 = (a1 - a) / Pp, (b1 - b) / Pp
        for k in (1, 2, 3, 1000):
            for i, j in PA._TEST[:7]:
                x = l + (r - l) * Fr(i, j)
                assert P.R(x + Pp * k) == a + b * x + Pp * k * (f0 + f1 * x), "periodic identity fails"
        pcs.append((l, r, a, b, f0, f1))
    S = iv.mpf(0)
    for k in range(Pn):
        c = Pp * k
        for l, r, a, b, f0, f1 in pcs:
            be_ = b + c * f1
            A0 = a + c * f0 - be_ * c
            Lk, Rk = l + c, r + c
            S = S + ivq(be_ * (1 / Lk - 1 / Rk) + A0 / 2 * (1 / Lk ** 2 - 1 / Rk ** 2))
    X = X0 + Pp * Pn
    Fp = [[f0, f1] for _, _, _, _, f0, f1 in pcs]
    Qp = [[a, b - f0, -f1] for _, _, a, b, f0, f1 in pcs]
    ivs = [(l, r) for l, r, *_ in pcs]

    def mean(polys):
        return sum((CR.pdef(p, l, r) for p, (l, r) in zip(polys, ivs)), Fr(0)) / Pp

    def integ(polys):
        out, acc = [], Fr(0)
        for p, (l, r) in zip(polys, ivs):
            Pq = CR.pint(p)
            q = CR.padd(Pq, [acc - CR.pev(Pq, l)])
            out.append(q)
            acc = CR.pev(q, r)
        return out, acc
    Fbar = mean(Fp)
    G, g1 = integ([CR.padd(p, [-Fbar]) for p in Fp])
    assert g1 == 0
    Gbar = mean(G)
    H, h1 = integ([CR.padd(p, [-Gbar]) for p in G])
    assert h1 == 0
    Qbar = mean(Qp)
    P1, p1 = integ([CR.padd(p, [-Qbar]) for p in Qp])
    assert p1 == 0
    Hr = [CR.prange(p, l, r) for p, (l, r) in zip(H, ivs)]
    Pr = [CR.prange(p, l, r) for p, (l, r) in zip(P1, ivs)]
    Hmin, Hmax = min(x[0] for x in Hr), max(x[1] for x in Hr)
    Pmin, Pmax = min(x[0] for x in Pr), max(x[1] for x in Pr)
    assert Fbar == (P.s - P.nu) * P.be
    main = Fbar / X + (Gbar + Qbar / 2) / X ** 2
    rem_lo = main + (2 * Hmin + Pmin) / X ** 3
    rem_hi = main + (2 * Hmax + Pmax) / X ** 3
    tail = S + iv.mpf([L.q_down(rem_lo), L.q_up(rem_hi)])
    A = ivq(io + inX0) + tail
    return A, dict(I_out=str(io), X0=str(X0), P=Pp, Fbar=str(Fbar), pieces=len(pcs))


def lb_cert(nu, al, be, sig, N=1000):
    dth = iv.pi / N
    C = [iv.cos(iv.pi * k / N) for k in range(N + 1)]
    Sn = [iv.sin(iv.pi * k / N) for k in range(N + 1)]
    C[0], Sn[0], C[N], Sn[N] = iv.mpf(1), iv.mpf(0), iv.mpf(-1), iv.mpf(0)
    cbar = [(Sn[k + 1] - Sn[k]) / dth for k in range(N)]
    mu = [(cbar[k] - C[k + 1]) / (C[k] - C[k + 1]) for k in range(N)]
    rho = sorted(sig, key=lambda r: r[1] - r[0])
    assert sum(c for _, _, c in rho) == Fr(be)
    Isig = L.I_rho(rho)
    intV = iv.mpf(0)
    for a, b, c in rho:
        m, h = ivq((a + b) / 2), ivq((b - a) / 2)
        tk = [nonneg(m + h * C[k]) for k in range(N + 1)]
        psi = [-nu * CR.J_iv(Fr(al), T) for T in tk]
        inc = iv.mpf(0)
        dec = iv.mpf(0)
        for k in range(N):
            inc = inc + CR.Vinc_iv(nonneg(m + h * cbar[k]))
            dec = dec + mu[k] * psi[k] + (1 - mu[k]) * psi[k + 1]
        intV = intV + ivq(c) * (inc + dec) / N
    return Isig - intV + L.Cstar(nu, Fr(al), Fr(be))


def main():
    cells = json.load(open(sys.argv[1]))
    N = 1000
    for a in sys.argv[2:]:
        if a.startswith("N="):
            N = int(a[2:])
    tag = os.path.splitext(os.path.basename(sys.argv[1]))[0]
    outp = os.path.join(HERE, "out", f"certified_{tag}.json")
    res = json.load(open(outp)) if os.path.exists(outp) else {}
    for al, be, nu in cells:
        al, be, nu = Fr(al), Fr(be), int(nu)
        key = f"{al}:{be}:{nu}"
        t0 = time.time()
        P7 = PA.PkgAB(7, nu, al, be)
        A, info = astar_cert(P7)
        LBf, sig, linfo = PA.lb_opt(nu, al, be)
        LBi = lb_cert(nu, al, be, sig, N)
        lo = to_fr(A.lo) + to_fr(LBi.lo)
        P5 = PA.PkgAB(5, nu, al, be)
        A5, _ = astar_cert(P5)
        res[key] = dict(alpha=str(al), beta=str(be), nu=nu, Astar7=[float(A.lo), float(A.hi)],
                        Astar5=[float(A5.lo), float(A5.hi)], LB=[float(LBi.lo), float(LBi.hi)], LB_float=LBf,
                        floor7_lower=float(lo), floor7_lower_exact=str(lo), floor5_lower=float(to_fr(A5.lo) + to_fr(LBi.lo)),
                        certified_positive=lo > 0, N=N, lb_family=linfo, sigma=[[str(x) for x in s] for s in sig],
                        astar_info=info, seconds=round(time.time() - t0, 1))
        log(f"  alpha={al} beta={be} nu={nu}: A*(7) in [{float(A.lo):.10f}, {float(A.hi):.10f}]  LB >= {float(LBi.lo):+.9f}"
            f" (float {LBf:+.9f})  => zeta(7) floor >= {float(lo):+.6f}  CERTIFIED > 0: {lo > 0};  "
            f"A*(5) in [{float(A5.lo):.8f}, {float(A5.hi):.8f}]  ({res[key]['seconds']} s)")
        json.dump(res, open(outp, "w"), indent=1)
    open(os.path.join(HERE, "out", f"certified_{tag}.log"), "w").write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
