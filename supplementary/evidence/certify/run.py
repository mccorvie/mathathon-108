#!/usr/bin/env python3
"""run.py -- interval-arithmetic certification of the decisive #108 margin signs (evidence/certify).

EVENT WORK, experimenter:Claude Opus 5.5, Fri Nov 13 2026 (started 23:41 PT).
Imports ../margin/theta.py (exact arithmetic side, comparison measures in out/U_cache.json) read-only.
Interval primitives: ivlib.py (mpmath.iv, 113 bits, own rigorous atan).  No randomness, no seeds.

  python3 run.py M0 [nu ...]     certified upper bound on sup_{t>=0} 2U^rho(t) - V_nu(t)  -> out/M0.json
  python3 run.py LB [nu ...]     certified dual lower bound LB(nu) <= U*(nu)               -> out/LB.json
  python3 run.py A  [s:nu ...]   certified enclosure of A*(s,nu) = I_out + int_3^oo R/x^3  -> out/A.json
  python3 run.py margins         combine: signs and brackets                               -> out/margins.json/.log
  python3 run.py figure          out/certified_brackets.svg
Default nu list: 2 4 6 8 10; default (s, nu): s in {3,5,7,9} x nu in {2,4,6,8,10}.
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "margin"))
import ivlib as L                 # noqa: E402  (sets iv.prec = mp.prec = 113)
from ivlib import iv, mpf, ivq, pt, to_fr, nonneg   # noqa: E402
import theta as TH                # noqa: E402  (read-only import)

AL, LAM = Fr(3, 40), Fr(37, 40)
NUS = [2, 4, 6, 8, 10]
UC = os.path.join(HERE, "..", "margin", "out", "U_cache.json")


def jload(name):
    p = os.path.join(OUT, name)
    return json.load(open(p)) if os.path.exists(p) else {}


def jsave(name, d):
    json.dump(d, open(os.path.join(OUT, name), "w"), indent=1, sort_keys=True)


def s_iv(X):
    return f"[{mpmath_str(X.lo)}, {mpmath_str(X.hi)}]"


def mpmath_str(x, n=15):
    import mpmath
    return mpmath.nstr(x, n)


def load_rho(nu):
    ent = json.load(open(UC))[str(nu)]
    rho = [(Fr(a), Fr(b), Fr(c)) for a, b, c in ent["rho"]]
    rho.sort(key=lambda r: r[1] - r[0])            # nested: innermost first (I_rho checks nesting exactly)
    assert sum(c for _, _, c in rho) == LAM and all(c > 0 and 0 <= a < b for a, b, c in rho)
    return ent, rho


# =============================================================================================
# 1. M0: certified upper bound on sup_{t >= 0} f(t),  f = 2 sum_j c_j U_j - V_inc + nu J_alpha
# =============================================================================================
class Comp:
    def __init__(self, a, b, c):
        self.a, self.b, self.c = a, b, c
        self.aI, self.bI, self.mI = ivq(a), ivq(b), ivq((a + b) / 2)
        self.k = ivq(2 * c)
        self.agcap = iv.log(ivq((b - a) / 4))


class Point:
    __slots__ = ("p", "F", "val", "dR", "dL", "vinc", "vJ", "dinc", "dJ")


def point_data(p, comps, nu):
    """values and one-sided derivative enclosures of every component at the point p (mpf)."""
    D = Point()
    D.p, D.F = p, to_fr(p)
    P = pt(p)
    D.val, D.dR, D.dL = [], [], []
    for cp in comps:
        dr = dl = None
        if D.F >= cp.b:                     # right of the support: U = log((t-m+sqrt((t-a)(t-b)))/2)
            sq = iv.sqrt(nonneg((P - cp.aI) * (P - cp.bI)))
            v = cp.k * iv.log((P - cp.mI + sq) / 2)
            if D.F > cp.b and sq.lo > 0:
                dr = cp.k / sq                # (2c) U' = 2c / sqrt((t-a)(t-b)), decreasing in t
        elif D.F <= cp.a:                   # left of the support
            sq = iv.sqrt(nonneg((cp.aI - P) * (cp.bI - P)))
            v = cp.k * iv.log((cp.mI - P + sq) / 2)
            if D.F < cp.a and sq.lo > 0:
                dl = -cp.k / sq               # (2c) U' = -2c / sqrt((a-t)(b-t)), decreasing in t
        else:
            v = cp.k * cp.agcap
        D.val.append(v)
        D.dR.append(dr)
        D.dL.append(dl)
    D.vinc = -L.Vinc_point(p)                                 # -V_inc, decreasing
    D.vJ = nu * L.J_point(AL, p)                              # nu J_alpha, increasing
    if p == 0:
        D.dinc = D.dJ = None
    else:
        S = iv.sqrt(P)
        D.dinc = -(iv.pi / S) - L.Jd_point(Fr(1), p)          # increasing in t
        D.dJ = nu * L.Jd_point(AL, p)                         # decreasing in t
    return D


def fsum_val(D):
    tot = D.vinc + D.vJ
    for v in D.val:
        tot = tot + v
    return tot


def cell_ub(D0, D1, Dc, comps):
    """two rigorous upper bounds for sup f on [t0, t1]; returns the smaller (mpf).
    mono: every U_j is quasi-convex (decreasing, constant, increasing), so its sup is at an endpoint;
          -V_inc is decreasing (sup at t0), nu J_alpha increasing (sup at t1).
    hybrid: components with a finite derivative enclosure on the cell are bounded together by the mean value
          theorem around the midpoint c: g(c) + (w/2) max(0, Hi, -Lo); the others by their mono bound."""
    w = D1.p - D0.p
    t0F, t1F = D0.F, D1.F
    mono = iv.mpf(0)
    sing = iv.mpf(0)
    hyb = iv.mpf(0)
    Lo = iv.mpf(0)
    Hi = iv.mpf(0)
    for j, cp in enumerate(comps):
        m = iv.mpf(max(D0.val[j].hi, D1.val[j].hi))
        mono = mono + m
        if t0F >= cp.a and t1F <= cp.b:
            hyb = hyb + Dc.val[j]
            continue
        if t0F >= cp.b:
            d0, d1 = D0.dR[j], D1.dR[j]
        elif t1F <= cp.a:
            d0, d1 = D0.dL[j], D1.dL[j]
        else:
            d0 = d1 = None
        if d0 is None or d1 is None:
            sing = sing + m
        else:
            hyb = hyb + Dc.val[j]
            Lo = Lo + iv.mpf(d1.lo)
            Hi = Hi + iv.mpf(d0.hi)
    m_inc, m_J = iv.mpf(D0.vinc.hi), iv.mpf(D1.vJ.hi)
    mono = mono + m_inc + m_J
    if D0.dinc is None:
        sing = sing + m_inc + m_J
    else:
        hyb = hyb + Dc.vinc + Dc.vJ
        Lo = Lo + iv.mpf(D0.dinc.lo) + iv.mpf(D1.dJ.lo)
        Hi = Hi + iv.mpf(D1.dinc.hi) + iv.mpf(D0.dJ.hi)
    slope = max(mpf(0), Hi.hi, -Lo.lo)
    ubh = (sing + hyb + iv.mpf(w) / 2 * iv.mpf(slope)).hi
    return min(mono.hi, ubh)


def mono_ub(D0, D1, comps):
    """the monotone bound alone (no midpoint needed)."""
    mono = iv.mpf(D0.vinc.hi) + iv.mpf(D1.vJ.hi)
    for j in range(len(comps)):
        mono = mono + iv.mpf(max(D0.val[j].hi, D1.val[j].hi))
    return mono.hi


def tail_bound(T, nu):
    """for t >= T >= max(1, max b_j): f(t) <= B(t) = (2 lam - 1) log t + nu al log(t + al^2) - 2 pi sqrt t,
    decreasing on [1, oo) for nu <= 10 (since (2lam - 1 + nu al)/t <= 1.6/sqrt t < pi/sqrt t).  Returns B(T)."""
    Ti = ivq(T)
    return (ivq(2 * LAM - 1) * iv.log(Ti) + nu * ivq(AL) * iv.log(Ti + ivq(AL * AL)) - 2 * iv.pi * iv.sqrt(Ti)).hi


def certify_M0(nu, tau, budget=400000, Tcut=Fr(4), log=print):
    ent, rho = load_rho(nu)
    comps = [Comp(a, b, c) for a, b, c in rho]
    assert max(b for _, b, _ in rho) < Tcut and nu <= 10
    tb = tail_bound(Tcut, nu)
    assert tb < L.q_down(tau), "tail bound fails"
    pts = {mpf(0), L.q_down(Tcut), L.q_up(Tcut)}
    for a, b, _ in rho:
        for q in (a, b):
            pts |= {L.q_down(q), L.q_up(q)}
    pts = sorted(p for p in pts if p >= 0)
    if to_fr(pts[-1]) < Tcut:
        raise RuntimeError("partition does not reach Tcut")
    cache = {}

    def data(p):
        key = p.man_exp
        if key not in cache:
            cache[key] = point_data(p, comps, nu)
        return cache[key]
    stack = [(p0, p1) for p0, p1 in zip(pts, pts[1:]) if p1 > p0][::-1]
    n_cells, n_acc, max_ub, best_lo, arg_lo = 0, 0, mpf("-inf"), mpf("-inf"), None
    t_start = time.time()
    tau_lo = L.q_down(tau)        # accept a cell iff ub <= tau_lo <= tau
    while stack:
        t0, t1 = stack.pop()
        n_cells += 1
        c = (t0 + t1) / 2
        if not (t0 < c < t1):            # adjacent 113-bit numbers (a cell around a rational a_j or b_j)
            ub = mono_ub(data(t0), data(t1), comps)
            if ub <= tau_lo:
                n_acc += 1
                max_ub = max(max_ub, ub)
                continue
            return dict(ok=False, why=f"unsplittable cell at {t0} has ub {float(ub)}", cells=n_cells,
                        best_lower=float(best_lo))
        D0, D1, Dc = data(t0), data(t1), data(c)
        flo = fsum_val(Dc).lo
        if flo > best_lo:
            best_lo, arg_lo = flo, c
        if best_lo > L.q_up(tau):        # a certified point value above tau: sup > tau
            return dict(ok=False, why=f"f(c) > tau at t = {mpmath_str(c)}: sup exceeds tau", cells=n_cells,
                        best_lower=float(best_lo), arg=float(arg_lo))
        ub = cell_ub(D0, D1, Dc, comps)
        if ub <= tau_lo:
            n_acc += 1
            if ub > max_ub:
                max_ub = ub
            continue
        if n_cells > budget:
            return dict(ok=False, why="cell budget exhausted", cells=n_cells, best_lower=float(best_lo))
        stack.append((c, t1))
        stack.append((t0, c))
    res = dict(ok=True, nu=nu, measure=ent["measure"], n_components=len(rho), tau=str(tau), tau_float=float(tau),
               max_cell_ub=float(max_ub), best_lower=float(best_lo), argmax_approx=float(arg_lo),
               cells=n_acc, Tcut=str(Tcut), tail_B_Tcut=float(tb), seconds=round(time.time() - t_start, 1),
               M0_theta=ent["M0"], sup_grid_theta=ent["sup_grid"])
    log(f"  nu={nu:2d} {ent['measure']:8s} CERTIFIED sup_[0,oo) 2U-V <= {float(max_ub):.12f} <= tau = {tau} "
        f"({float(tau):.9f});  lower (point value) {float(best_lo):.12f} at t~{float(arg_lo):.6f};  "
        f"{n_acc} cells, tail B(4) = {float(tb):.3f}, {res['seconds']} s")
    return res


def cmd_M0(args):
    nus = [int(a) for a in args] or NUS
    out = jload("M0.json")
    logf = open(os.path.join(OUT, "M0.log"), "a")

    def log(s):
        print(s, flush=True)
        logf.write(s + "\n")
        logf.flush()
    log(f"== M0 run {time.strftime('%Y-%m-%d %H:%M:%S')} (iv prec {L.PREC} bits)")
    for nu in nus:
        ent, rho = load_rho(nu)
        tau0 = Fr(ent["M0"]).limit_denominator(10 ** 6)
        assert float(tau0) == ent["M0"]
        tries = [tau0, tau0 + Fr(1, 10 ** 6), tau0 + Fr(1, 10 ** 5)]
        for tau in tries:
            r = certify_M0(nu, tau, log=log)
            if r["ok"]:
                out[str(nu)] = r
                break
            log(f"  nu={nu:2d} tau={tau} ({float(tau):.9f}) NOT certified: {r['why']} (cells {r['cells']}, "
                f"best lower {r['best_lower']:.12f})")
        else:
            out[str(nu)] = dict(ok=False, nu=nu)
        jsave("M0.json", out)


# =============================================================================================
# 2. LB(nu) = I(sigma) - int V_nu d sigma + C*(nu) <= U(nu; rho) for every comparison measure rho
# =============================================================================================
def cmd_LB(args):
    N = 2000
    nus = [int(a) for a in args if not a.startswith("N=")] or NUS
    for a in args:
        if a.startswith("N="):
            N = int(a[2:])
    out = jload("LB.json")
    # theta nodes, cell means of cos, chord weights mu_k (independent of the component)
    dth = iv.pi / N
    C = [iv.cos(iv.pi * k / N) for k in range(N + 1)]
    S = [iv.sin(iv.pi * k / N) for k in range(N + 1)]
    C[0], S[0], C[N], S[N] = iv.mpf(1), iv.mpf(0), iv.mpf(-1), iv.mpf(0)
    cbar = [(S[k + 1] - S[k]) / dth for k in range(N)]
    mu = [(cbar[k] - C[k + 1]) / (C[k] - C[k + 1]) for k in range(N)]
    for nu in nus:
        t_start = time.time()
        ent, rho = load_rho(nu)
        Isig = L.I_rho(rho)
        intV = iv.mpf(0)
        for a, b, c in rho:
            m, h = ivq((a + b) / 2), ivq((b - a) / 2)
            tk = [nonneg(m + h * C[k]) for k in range(N + 1)]
            psi = [-nu * J_iv(AL, T) for T in tk]                     # -nu J_alpha: convex in t
            inc = iv.mpf(0)
            dec = iv.mpf(0)
            for k in range(N):
                inc = inc + Vinc_iv(nonneg(m + h * cbar[k]))           # Jensen: V_inc concave in t
                dec = dec + mu[k] * psi[k] + (1 - mu[k]) * psi[k + 1]   # chord: -nu J_alpha convex
            intV = intV + ivq(c) * (inc + dec) / N
        LBv = Isig - intV + L.Cstar(nu)
        out[str(nu)] = dict(nu=nu, measure=ent["measure"], N=N, I_sigma=[float(Isig.lo), float(Isig.hi)],
                            intV_upper=float(intV.hi), LB_lower=float(LBv.lo),
                            LB_lower_exact=str(to_fr(LBv.lo)), LB_upper_of_bound=float(LBv.hi),
                            LB_criterion5=json.load(open(os.path.join(HERE, "..", "criterion5", "dual_bound.json")))[str(nu)]["LB"],
                            seconds=round(time.time() - t_start, 1))
        print(f"  nu={nu:2d} {ent['measure']:8s} N={N}: CERTIFIED LB(nu) >= {float(LBv.lo):+.9f}   "
              f"(criterion5 float N=12000: {out[str(nu)]['LB_criterion5']:+.9f}; {out[str(nu)]['seconds']} s)", flush=True)
        jsave("LB.json", out)


def J_iv(a, T):
    """J_a over an interval T (T.lo >= 0): interval extension if T.lo > 0, else monotone endpoints."""
    if T.lo > 0:
        A = ivq(a)
        Sq = iv.sqrt(T)
        return A * iv.log(T + A * A) - 2 * A + 2 * Sq * atan_ext(A / Sq)
    return L.J_enc(a, T)


def Vinc_iv(T):
    if T.lo > 0:
        return 2 * iv.pi * iv.sqrt(T) + J_iv(Fr(1), T)
    return L.Vinc_enc(T)


def atan_ext(X):
    """interval extension of atan (X.lo >= 0), no endpoint splitting when X is on one side of 1."""
    if X.hi <= 1:
        return L._atan_red(X)
    if X.lo >= 1:
        return iv.pi / 2 - L._atan_red(1 / X)
    return L.atan_iv(X)


# =============================================================================================
# 3. A*(s, nu) = I_out + int_3^200 R/x^3 (exact, theta.py) + int_200^oo R/x^3 (enclosure)
# =============================================================================================
def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(p, s):
    return [s * c for c in p]


def pint(p):            # antiderivative with zero constant term
    return [Fr(0)] + [c / (i + 1) for i, c in enumerate(p)]


def pev(p, x):
    return sum((c * x ** i for i, c in enumerate(p)), Fr(0))


def pdef(p, l, r):
    P = pint(p)
    return pev(P, r) - pev(P, l)


def prange(p, l, r):
    """rigorous [lo, hi] of polynomial p on [l, r]: Taylor coefficients at l, |sum_{i>=1} d_i y^i| <= sum |d_i| d^i."""
    n = len(p)
    d = []
    q = list(p)
    fact = 1
    for i in range(n):
        d.append(pev(q, l) / fact)
        q = [c * j for j, c in enumerate(q)][1:]
        fact *= (i + 1)
    dl = r - l
    e = sum((abs(d[i]) * dl ** i for i in range(1, n)), Fr(0))
    return d[0] - e, d[0] + e


def astar(s, nu, Pn=45, log=print):
    t_start = time.time()
    P = TH.Pkg(s, nu, "S")
    io = TH.I_out(P)
    in200 = TH.int_R_x3(P, 3, 200)
    A200 = TH.A_M(P, 200, io, in200)
    base = TH.pieces(P.R, TH.inner_breaks(P, 200, 240))
    assert base[0][0] == 200 and base[-1][1] == 240 and all(x[1] == y[0] for x, y in zip(base, base[1:]))
    pcs = []
    for l, r, a, b in base:
        a1, b1 = TH.affine_fit(lambda x: P.R(x + 40), l, r)
        f0, f1 = (a1 - a) / 40, (b1 - b) / 40
        # R(x + 40k) is a polynomial of degree <= 2 in k (README section 3); equality with a + b x + 40k F(x)
        # at k = 0 (fit), 1 (fit), 2, 3 at 7 points per piece proves it for every k >= 0; k = 1000, 10^6 as sanity.
        for k in (1, 2, 3, 1000, 10 ** 6):
            for i, j in TH._TEST[:7]:
                x = l + (r - l) * Fr(i, j)
                assert P.R(x + 40 * k) == a + b * x + 40 * k * (f0 + f1 * x), "periodic identity fails"
        for k in (1, 2, 3, 4):        # negative shifts: the same identity on [40, 200] (used for finite M >= 40)
            for i, j in TH._TEST[:7]:
                x = l + (r - l) * Fr(i, j)
                assert P.R(x - 40 * k) == a + b * x - 40 * k * (f0 + f1 * x), "periodic identity fails (k<0)"
        pcs.append((l, r, a, b, f0, f1))
    # exact periods k = 0 .. Pn-1, each term a rational, summed in iv
    S = iv.mpf(0)
    for k in range(Pn):
        c = 40 * k
        for l, r, a, b, f0, f1 in pcs:
            be = b + c * f1
            A0 = a + c * f0 - be * c
            Lk, Rk = l + c, r + c
            S = S + ivq(be * (1 / Lk - 1 / Rk) + A0 / 2 * (1 / Lk ** 2 - 1 / Rk ** 2))
    X = Fr(200 + 40 * Pn)
    # remainder: int_X^oo R/w^3 in Fbar/X + (Gbar + Qbar/2)/X^2 + (2 [minH, maxH] + [minP1, maxP1])/X^3
    Fp = [[f0, f1] for _, _, _, _, f0, f1 in pcs]
    Qp = [[a, b - f0, -f1] for _, _, a, b, f0, f1 in pcs]
    iv_ = [(l, r) for l, r, *_ in pcs]

    def mean(polys):
        return sum((pdef(p, l, r) for p, (l, r) in zip(polys, iv_)), Fr(0)) / 40

    def integ(polys):     # piecewise antiderivative vanishing at 200 (continuous)
        out, acc = [], Fr(0)
        for p, (l, r) in zip(polys, iv_):
            Pp = pint(p)
            q = padd(Pp, [acc - pev(Pp, l)])
            out.append(q)
            acc = pev(q, r)
        return out, acc
    Fbar = mean(Fp)
    G, g240 = integ([padd(p, [-Fbar]) for p in Fp])
    assert g240 == 0
    Gbar = mean(G)
    H, h240 = integ([padd(p, [-Gbar]) for p in G])
    assert h240 == 0
    Qbar = mean(Qp)
    P1, p240 = integ([padd(p, [-Qbar]) for p in Qp])
    assert p240 == 0
    Hr = [prange(p, l, r) for p, (l, r) in zip(H, iv_)]
    Pr = [prange(p, l, r) for p, (l, r) in zip(P1, iv_)]
    Hmin, Hmax = min(x[0] for x in Hr), max(x[1] for x in Hr)
    Pmin, Pmax = min(x[0] for x in Pr), max(x[1] for x in Pr)
    # finite M: for every real M >= 40, int_M^oo R/w^3 <= Fbar/M + K2/M^2 with K2 = (maxG - minG) + max(Q, 0)/2
    # (integration by parts with the periodic G), so A_M - A* >= c/M - K2/M^2, c = c_cr lam - Fbar.
    Gr = [prange(p, l, r) for p, (l, r) in zip(G, iv_)]
    Qr = [prange(p, l, r) for p, (l, r) in zip(Qp, iv_)]
    K2 = (max(x[1] for x in Gr) - min(x[0] for x in Gr)) + max(Fr(0), max(x[1] for x in Qr)) / 2
    cM = P.c_cr * LAM - Fbar
    assert Fbar == (s - nu) * LAM and cM == (nu + 1) * LAM
    gmin = Fr(0) if K2 <= 40 * cM else -cM * cM / (4 * K2)
    main = Fbar / X + (Gbar + Qbar / 2) / X ** 2
    rem_lo = main + (2 * Hmin + Pmin) / X ** 3
    rem_hi = main + (2 * Hmax + Pmax) / X ** 3
    tail = S + iv.mpf([L.q_down(rem_lo), L.q_up(rem_hi)])
    A = ivq(io + in200) + tail
    theta_Ainf, _ = TH.A_inf(P, io, in200)
    res = dict(s=s, nu=nu, I_out=str(io), int_3_200=str(in200), A200=str(A200), A200_float=float(A200),
               tail_200_inf=[float(tail.lo), float(tail.hi)], Astar=[float(A.lo), float(A.hi)],
               Astar_width=float(A.hi - A.lo), X=str(X), Fbar=str(Fbar), Gbar=str(Gbar), Qbar=str(Qbar),
               H_range=[float(Hmin), float(Hmax)], P1_range=[float(Pmin), float(Pmax)], pieces=len(pcs),
               theta_A_inf_float=theta_Ainf, K2=str(K2), K2_float=float(K2), cM=str(cM),
               AM_minus_Astar_lower_all_M_ge_40=str(gmin), M_threshold=float(K2 / cM),
               seconds=round(time.time() - t_start, 1))
    res["Astar_exact"] = [str(to_fr(A.lo)), str(to_fr(A.hi))]     # exact endpoints of the enclosure
    res["Astar_lo_repr"] = mpmath_str(A.lo, 25)
    res["Astar_hi_repr"] = mpmath_str(A.hi, 25)
    log(f"  s={s} nu={nu:2d}: A* in [{float(A.lo):.12f}, {float(A.hi):.12f}] (width {float(A.hi - A.lo):.1e});  "
        f"theta float A_inf {theta_Ainf:.12f};  A_200 = {float(A200):.12f} exact;  {res['seconds']} s")
    return res


def cmd_A(args):
    pairs = [tuple(int(z) for z in a.split(":")) for a in args] or [(s, nu) for s in (5, 7, 3, 9) for nu in NUS]
    out = jload("A.json")
    for s, nu in pairs:
        out[f"{s}:{nu}"] = astar(s, nu)
        jsave("A.json", out)


# =============================================================================================
# 4. margins
# =============================================================================================
def cmd_margins(args):
    A, M0, LBd = jload("A.json"), jload("M0.json"), jload("LB.json")
    lines, res = [], {}

    def log(s):
        print(s)
        lines.append(s)
    log(f"# certified margins (run.py margins, {time.strftime('%Y-%m-%d %H:%M')}); intervals are rigorous enclosures")
    Ucert = {}
    log("## analytic side: U(nu; rho_theta) = lam*M0bar - I(rho) + C*(nu)  (upper bound), LB(nu) (lower bound)")
    for nu in NUS:
        k = str(nu)
        if k not in M0 or not M0[k].get("ok"):
            log(f"  nu={nu}: M0 not certified")
            continue
        ent, rho = load_rho(nu)
        tau = Fr(M0[k]["tau"])
        Irho = L.I_rho(rho)
        Cs = L.Cstar(nu)
        U = ivq(LAM * tau) - Irho + Cs
        Ucert[nu] = U
        lbv = LBd.get(k, {}).get("LB_lower")
        res[f"U{nu}"] = dict(M0bar=str(tau), I_rho=[float(Irho.lo), float(Irho.hi)], Cstar=[float(Cs.lo), float(Cs.hi)],
                             U_upper=float(U.hi), U_upper_exact=str(to_fr(U.hi)), U_theta=ent["U"], LB_lower=lbv)
        log(f"  nu={nu:2d} {ent['measure']:8s}: M0bar = {tau} ({float(tau):.6f}; theta grid sup {ent['sup_grid']:.10f});"
            f" I(rho) in {s_iv(Irho)}; C* in {s_iv(Cs)}")
        log(f"           U <= {float(U.hi):+.10f}  (theta float {ent['U']:+.10f});   LB >= {lbv:+.10f}" if lbv is not None
            else f"           U <= {float(U.hi):+.10f}")
    log("## decisive signs")
    allok = True
    for nu in NUS:
        key = f"7:{nu}"
        if key in A and str(nu) in LBd:
            loF = Fr(A[key]["Astar_exact"][0]) + Fr(LBd[str(nu)]["LB_lower_exact"])   # exact sum of rigorous ends
            lo = float(loF)
            ok = loF > 0
            allok &= ok
            res[f"zeta7_nu{nu}"] = dict(lower=lo, certified_positive=ok)
            log(f"  zeta(7), nu={nu:2d}:  A*(7,nu) + U >= A* + LB >= {lo:+.6f}   {'CERTIFIED > 0' if ok else 'NOT certified'}")
        else:
            allok = False
            log(f"  zeta(7), nu={nu:2d}: missing inputs")
    if "5:6" in A and 6 in Ucert:
        upF = Fr(A["5:6"]["Astar_exact"][1]) + to_fr(Ucert[6].hi)                  # exact sum of rigorous ends
        up = float(upF)
        a200 = Fr(A["5:6"]["A200"])
        up200 = (ivq(a200) + Ucert[6]).hi
        ok = upF < 0 and up200 < 0
        allok &= ok
        res["zeta5_nu6"] = dict(upper_Mstar=up, upper_M200=float(up200), certified_negative=ok)
        log(f"  zeta(5), nu= 6:  A*(5,6) + U(6; Fauzan rho) <= {up:+.6f};  A_200(5,6) + U <= {float(up200):+.6f}   "
            f"{'CERTIFIED < 0' if ok else 'NOT certified'}")
    log("## brackets [A* + LB, A* + U(rho_theta)] (M -> oo), certified ends")
    for s in (3, 5, 7, 9):
        cells = []
        for nu in NUS:
            key = f"{s}:{nu}"
            if key in A and str(nu) in LBd and nu in Ucert:
                lo = float(Fr(A[key]["Astar_exact"][0]) + Fr(LBd[str(nu)]["LB_lower_exact"]))
                hi = float(Fr(A[key]["Astar_exact"][1]) + to_fr(Ucert[nu].hi))
                res[f"bracket_{s}_{nu}"] = [lo, hi]
                cells.append(f"nu={nu}: [{lo:+.4f},{hi:+.4f}]")
        log(f"  s={s}: " + "  ".join(cells))
    log("## finite M (A_M = I_out + c_cr lam/M + int_3^M R/x^3): A_M - A* >= c/M - K2/M^2, c = (nu+1) lam")
    thr = [(k, v["M_threshold"], v["AM_minus_Astar_lower_all_M_ge_40"]) for k, v in sorted(A.items())]
    ok_m = all(Fr(g) == 0 for _, _, g in thr)
    log(f"  max over the {len(thr)} (s,nu) pairs of K2/c = {max(t for _, t, _ in thr):.4f} < 40, so A_M >= A* for every "
        f"real M >= 40: {ok_m}.  Hence every 'zeta(7) > 0' line above holds for every M >= 40 as well.")
    res["A_M_ge_Astar_all_M_ge_40"] = ok_m
    res["all_decisive_certified"] = allok
    log(f"ALL DECISIVE SIGNS CERTIFIED: {allok}")
    jsave("margins.json", res)
    open(os.path.join(OUT, "margins.log"), "w").write("\n".join(lines) + "\n")


# =============================================================================================
# 5. figure (SVG, no matplotlib on this machine)
# =============================================================================================
def cmd_figure(args):
    m = jload("margins.json")
    W, Hh = 1110, 420
    x0, x1, y0, y1 = 70, 690, 40, 360
    vmin, vmax = -1.0, 2.3

    def X(nu):
        return x0 + (nu - 1) / 10 * (x1 - x0)

    def Y(v):
        return y1 - (v - vmin) / (vmax - vmin) * (y1 - y0)
    col = {3: "#7a7a7a", 5: "#1f5fbf", 7: "#c0392b", 9: "#2e8b57"}
    off = {3: -12, 5: -4, 7: 4, 9: 12}
    el = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{Hh}" font-family="Helvetica" font-size="12">',
          f'<rect width="{W}" height="{Hh}" fill="white"/>',
          f'<text x="{W/2}" y="20" text-anchor="middle" font-size="14">Certified margin brackets [A* + LB(nu), A* + U(nu)] '
          f'(interval arithmetic; closes iff &lt; 0)</text>']
    for v in [-1, -0.5, 0, 0.5, 1, 1.5, 2]:
        el.append(f'<line x1="{x0}" x2="{x1}" y1="{Y(v):.1f}" y2="{Y(v):.1f}" stroke="{"black" if v == 0 else "#ddd"}" '
                  f'stroke-width="{1.5 if v == 0 else 1}"/>')
        el.append(f'<text x="{x0-8}" y="{Y(v)+4:.1f}" text-anchor="end">{v:+.1f}</text>')
    for nu in NUS:
        el.append(f'<text x="{X(nu):.1f}" y="{y1+18}" text-anchor="middle">nu = {nu}</text>')
    for s in (3, 5, 7, 9):
        for nu in NUS:
            b = m.get(f"bracket_{s}_{nu}")
            if not b:
                continue
            xx = X(nu) + off[s]
            el.append(f'<line x1="{xx:.1f}" x2="{xx:.1f}" y1="{Y(b[0]):.1f}" y2="{Y(b[1]):.1f}" stroke="{col[s]}" '
                      f'stroke-width="6"/>')
        el.append(f'<rect x="{x1-120}" y="{y0 + 18*[3,5,7,9].index(s)}" width="12" height="10" fill="{col[s]}"/>'
                  f'<text x="{x1-102}" y="{y0 + 9 + 18*[3,5,7,9].index(s)}">zeta({s})</text>')
    el.append(f'<text x="{x0}" y="{Hh-12}" font-size="11">zeta(7): every bracket lies above 0 (lower ends = A* + dual bound, '
              f'valid for every comparison measure); zeta(5), nu = 6: below 0.</text>')
    # zoom panel: zeta(5) only, on [-0.1, +0.32]
    zx0, zx1, zy0, zy1, zmin, zmax = 760, 1060, 40, 360, -0.10, 0.32

    def ZX(nu):
        return zx0 + (nu - 1) / 10 * (zx1 - zx0)

    def ZY(v):
        return zy1 - (v - zmin) / (zmax - zmin) * (zy1 - zy0)
    el.append(f'<text x="{(zx0+zx1)/2}" y="34" text-anchor="middle">zoom: zeta(5) only</text>')
    for v in [-0.1, -0.05, 0, 0.05, 0.1, 0.2, 0.3]:
        el.append(f'<line x1="{zx0}" x2="{zx1}" y1="{ZY(v):.1f}" y2="{ZY(v):.1f}" stroke="{"black" if v == 0 else "#ddd"}" '
                  f'stroke-width="{1.5 if v == 0 else 1}"/>')
        el.append(f'<text x="{zx0-6}" y="{ZY(v)+4:.1f}" text-anchor="end">{v:+.2f}</text>')
    for nu in NUS:
        b = m.get(f"bracket_5_{nu}")
        el.append(f'<text x="{ZX(nu):.1f}" y="{zy1+18}" text-anchor="middle">nu={nu}</text>')
        if b:
            el.append(f'<line x1="{ZX(nu):.1f}" x2="{ZX(nu):.1f}" y1="{ZY(b[0]):.1f}" y2="{ZY(b[1]):.1f}" stroke="{col[5]}" '
                      f'stroke-width="8"/>')
            el.append(f'<text x="{ZX(nu)+8:.1f}" y="{ZY((b[0]+b[1])/2)+4:.1f}" font-size="10">[{b[0]:+.3f}, {b[1]:+.3f}]</text>')
    el.append("</svg>")
    p = os.path.join(OUT, "certified_brackets.svg")
    open(p, "w").write("\n".join(el))
    print("wrote", p)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else "help"
    {"M0": cmd_M0, "LB": cmd_LB, "A": cmd_A, "margins": cmd_margins, "figure": cmd_figure}.get(
        cmd, lambda a: print(__doc__))(sys.argv[2:])
