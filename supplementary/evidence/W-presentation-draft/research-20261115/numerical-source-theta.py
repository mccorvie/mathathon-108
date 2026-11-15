#!/usr/bin/env python3
"""theta.py -- ONE-bound-package margin tool for the Fauzan/Lai Hankel template (problem #108).

EVENT WORK, Fri Nov 13 2026 (started 21:04 PT).  Owner: experimenter (Claude Opus 5.5).
Other agents may import or run this file; never edit it (dossier event rule 4).

Template (Lai, ai.vixra 2609.0080v1, eq. (7) p. 3): K = 40n, N = 3n, h = 37n,
alpha = 3/40, lambda = 37/40.  Hankel entries mu_X(D_N(t)^nu t^(i+j) / D_K(t)).
nu = numerator power (6 in Fauzan's zeta(5), 8 in Anand's zeta(7), 2 in Lai's zeta(7) claim).

THE PACKAGE (one set of bounds, evaluated for every (s, nu)):
  arithmetic, Lai Thm 9.3 (p. 13, eq. (78)) WITHOUT the E_M correction:
      A_M   = I_out + c_cr*lambda/M + int_3^M R(x)/x^3 dx     exact rational, M integer >= 40
      A_inf = I_out + int_3^oo R(x)/x^3 dx                     float64 sum over exact pieces
    R = -Gamma - N  (Lai (72)-(79), p. 12-13), I_out = int_{1/3}^{2 lambda} T_out(y) dy (Lai (84), p. 14;
    Fauzan Sect. 4.2), written as in mo271/Zeta5@7fe73676 scripts/appendixB.py (zeta(5)) and
    [team handle]/zeta7-irrational@be55b3a4 ZetaSeven/InnerLimiting.lean, OuterLimiting.lean (zeta(7)).
  analytic, Lai Lemma 11.4 (p. 15): U = lambda*M0 - I(rho) + C*(nu), rho a comparison measure of mass
    lambda (nested arcsine measures, Lai (90)-(92)), M0 >= sup_{t>=0} 2U^rho(t) - V_nu(t),
    V_nu(t) = 2 pi sqrt(t) + J_1(t) - nu*J_alpha(t),  J_a(t) = int_0^a log(t+u^2) du  (Lai (88)-(89)),
    C*(nu) = -2 lambda + 2 nu alpha lambda (1 - log alpha) + 3 lambda^2 - 2 lambda^2 log(2 lambda).
  margin = A_M + U  (the method needs < 0).

WHERE s AND nu ENTER.  nu enters through H = 1 + (nu/2 - 1) alpha, b = (nu/2) l(alpha x, z),
N(x) = 2 lambda x[x] - 2 nu lambda x[alpha x] - 2J(lambda x), the outer t-coefficients nu, nu-1, the term
2 nu alpha, the rank intercept 1 + (nu-2) alpha, and V_nu, C*(nu).  Five constants are NOT fixed by the
two anchors, because both anchors have nu = s+1:
      c_in  (Gamma: (T + b - l - c_in)):      5 at (s,nu)=(5,6), 7 at (7,8)
      c_out (outer leading (1-y) coefficient): 7, 9
      rho_r (outer rank slope r = 1+(nu-2)alpha - rho_r y): 2, 3
      c_cr  (crude range-2 coefficient):       6, 8
READINGS: 'S' (c_in=s, c_out=s+2, rho_r=(s-1)/2, c_cr=s+1), 'N' (c_in=nu-1, c_out=nu+1,
rho_r=(nu-2)/2, c_cr=nu), 'LAI' (Lai's own Programs 06-09 at laichunwing/Zeta7-is-Irrational@c42a984f:
c_in=nu-1, c_out=9, rho_r=2, c_cr=8).  Both 'S' and 'N' reproduce both anchors.
REVISION (Fri 22:00 PT): reading 'S' now uses the outer class sums of evidence/criterion5/derivation.md section 3
(dossier E13): removed-pole class cost sum_i max(0, l+s-1-nu-2i), which caps the numerator's savings; identical to
the old family form on nu = s+1 (checked in `anchors`).  The pre-revision reading is kept as 'S0'.

Usage:  python3 theta.py anchors | lai | table | figure | all
"""
import json
import math
import os
import sys
from fractions import Fraction as Fr

AL = Fr(3, 40)
LAM = Fr(37, 40)
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")


def fl(x):
    return math.floor(x)


def frac(x):
    return x - fl(x)


def d0(u):
    return min(u, 1 - u)


def ell(x, z):
    return fl(x - z) + fl(x + z) + 1


def Jfun(u):
    m = fl(2 * u)
    return m * u - Fr(m * (m + 1), 4)


# ----------------------------------------------------------------------------------------------
# the package's constants
# ----------------------------------------------------------------------------------------------
class Pkg:
    def __init__(self, s, nu, reading="S", **over):
        nu = Fr(nu)
        self.s, self.nu, self.reading = s, nu, reading
        self.H = 1 + (nu / 2 - 1) * AL
        self.bcoef = nu / 2
        self.Ncoef = 2 * nu
        self.rank_icpt = 1 + (nu - 2) * AL
        # outer function: 'classes' = class sums of criterion5/derivation.md section 3 (E13, revision Fri 22:00);
        # 'linear' = the family form c_out(1-y) - nu t ... (exact on nu = s+1 only; Lai's programs; reading N)
        self.outer = "classes" if reading == "S" else "linear"
        if reading in ("S", "S0"):      # 'S0' = reading S before the 22:00 revision (linear outer), kept to compare
            d = dict(c_in=Fr(s), c_out=Fr(s + 2), rho_r=Fr(s - 1, 2), c_cr=Fr(s + 1))
        elif reading == "N":
            d = dict(c_in=nu - 1, c_out=nu + 1, rho_r=(nu - 2) / 2, c_cr=nu)
        elif reading == "LAI":
            d = dict(c_in=nu - 1, c_out=Fr(9), rho_r=Fr(2), c_cr=Fr(8))
        else:
            raise ValueError(reading)
        d.update({k: Fr(v) for k, v in over.items()})
        for k, v in d.items():
            setattr(self, k, v)

    def label(self):
        return (f"s={self.s} nu={self.nu} reading={self.reading} c_in={self.c_in} c_out={self.c_out} "
                f"rho_r={self.rho_r} c_cr={self.c_cr} Ncoef={self.Ncoef}")

    # Lai (72)-(79); Zeta5 appendixB.py Gamma/Nf/R generalised
    def R(self, x):
        H = self.H
        T = fl(2 * H * x)
        sl = H * x - Fr(T, 2)
        q = fl(2 * x)
        nplus = (2 * x - q) / 2
        bps = sorted({Fr(0), Fr(1, 2), d0(frac(x)), d0(frac(AL * x))})
        I = Fr(0)
        for a, b in zip(bps, bps[1:]):
            if b <= a:
                continue
            z = (a + b) / 2
            l = ell(x, z)
            bb = self.bcoef * ell(AL * x, z)
            I += (T - bb) * (T + bb - l - self.c_in) * (b - a)
        G = I + sl * (2 * T - q - self.c_in) + max(sl - nplus, Fr(0))
        N = 2 * LAM * x * fl(x) - self.Ncoef * LAM * x * fl(AL * x) - 2 * Jfun(LAM * x)
        return -G - N

    # general outer function (criterion5/derivation.md section 3, E13): Fauzan (4.12) with harmonic loss s and
    # numerator power nu kept apart.  A class with l poles j <= K and one removed pole (j <= N) has rows i < l-2 of
    # weight min(0, i + nu/2 - (l+s-1)/2): cost c1(l) = sum_i max(0, l+s-1-nu-2i), zero weights z1(l); a class
    # without removed pole costs (s+2)(l-2) and has two zero weights.  The min(0, .) caps the numerator's savings.
    def outer_parts(self, y):
        s, nu = Fr(self.s), self.nu
        k = fl(1 / y)
        v = 1 - k * y
        u = max(Fr(0), AL + v - y)
        mv = min(AL, v)
        dens = {2 * k: AL - mv, 2 * k + 1: mv - u, 2 * k + 2: u}

        def c1(l):
            return sum((max(Fr(0), l + s - 1 - nu - 2 * i) for i in range(l - 2)), Fr(0))

        def z1(l):
            return 1 + sum(1 for i in range(l - 2) if l + s - 1 - nu - 2 * i <= 0)
        cost = self.c_out * ((1 - y) - sum(dn * (l - 2) for l, dn in dens.items())) + \
            sum(dn * c1(l) for l, dn in dens.items())
        zz = (y - 2 * AL) + sum(dn * z1(l) for l, dn in dens.items())
        r = min(LAM, max(Fr(0), self.rank_icpt - self.rho_r * y))
        return cost, zz, r

    # Lai (84); audit OuterLimiting.lean; Zeta5 appendixB.py R0 - d
    def Tout(self, y):
        nu = self.nu
        g = Fr(0)
        if self.outer == "classes":
            if Fr(1, 3) < y <= 1:
                cost, zz, r = self.outer_parts(y)
                g = cost + min(r, zz)
        elif Fr(1, 3) < y <= 1:
            k = fl(1 / y)
            v = 1 - k * y
            u = max(Fr(0), AL + v - y)
            t = min(AL, v) + u
            r = min(LAM, max(Fr(0), self.rank_icpt - self.rho_r * y))
            if y <= Fr(1, 2):
                g = self.c_out * (1 - y) - 2 * nu * AL - (nu - 1) * t + min(r, y + u)
            else:
                g = self.c_out * (1 - y) - nu * t + min(r, y - AL + u)
        scal = -2 * LAM * fl(1 / y) + sum(max(2 * LAM - j * y, Fr(0)) for j in range(1, 7))
        return g + scal


# ----------------------------------------------------------------------------------------------
# exact integration of piecewise-affine functions (every piece verified at 7 interior points)
# ----------------------------------------------------------------------------------------------
_TEST = ((2, 7), (5, 7), (1, 11), (1, 2), (10, 11), (3, 13), (7, 9), (1, 997), (996, 997), (1, 99991),
         (99990, 99991))


def affine_fit(f, l, r):
    pts = [l + (r - l) * Fr(i, j) for i, j in _TEST]
    f1, f2 = f(pts[0]), f(pts[1])
    b = (f2 - f1) / (pts[1] - pts[0])
    a = f1 - b * pts[0]
    for x in pts[2:]:
        if f(x) != a + b * x:
            return None
    return a, b


def _pieces(f, l, r, depth, out):
    fit = affine_fit(f, l, r)
    if fit is not None:
        out.append((l, r, fit[0], fit[1]))
        return
    if depth > 60:
        raise RuntimeError(f"no affine piece found on [{l}, {r}]")
    e = (r - l) / 10 ** 6
    L = affine_fit(f, l, l + 8 * e)
    Rr = affine_fit(f, r - 8 * e, r)
    cut = None
    if L is not None and Rr is not None and L[1] != Rr[1]:
        xs = (Rr[0] - L[0]) / (L[1] - Rr[1])
        if l < xs < r:
            cut = xs
    if cut is None:
        cut = (l + r) / 2
    _pieces(f, l, cut, depth + 1, out)
    _pieces(f, cut, r, depth + 1, out)


def pieces(f, pts):
    out = []
    for l, r in zip(pts, pts[1:]):
        if r > l:
            _pieces(f, l, r, 0, out)
    return out


def inner_breaks(P, lo, hi):
    cs = {Fr(2), 2 * AL, 2 * LAM, 2 * P.H, 2 * (1 - AL), 2 * (1 + AL), 4 * AL, 8 * AL, 2 * (1 + 2 * AL)}
    if P.H != 1:
        cs.add(abs(2 * (P.H - 1)))
    pts = {Fr(lo), Fr(hi)}
    for c in cs:
        k = fl(lo * c)
        while Fr(k) / c <= hi:
            x = Fr(k) / c
            if lo < x < hi:
                pts.add(x)
            k += 1
    return sorted(pts)


def int_R_x3(P, lo, hi):
    """exact int_lo^hi R(x)/x^3 dx (rational)."""
    tot = Fr(0)
    for l, r, a, b in pieces(P.R, inner_breaks(P, lo, hi)):
        tot += b * (1 / l - 1 / r) + a / 2 * (1 / l ** 2 - 1 / r ** 2)
    return tot


def outer_kinks(P):
    """every point where an argument of max/min in T_out changes sign (solved branch by branch)."""
    I, rho, a, lam = P.rank_icpt, P.rho_r, AL, LAM
    c = {Fr(1, 3), Fr(1, 2), Fr(1), 2 * lam, (1 + a) / 3, (1 - a) / 2, (1 + a) / 2, 1 - a, (1 + a - lam) / 2, lam,
         a, lam + a} | {2 * lam / j for j in range(1, 7)}
    if rho != 0:
        c |= {I / rho, (I - lam) / rho, I / (rho + 1), (I + a) / (rho + 1)}
    if rho != 2:
        c.add((I - 1 - a) / (rho - 2))
    if rho != 1:
        c.add((I - 1) / (rho - 1))
    return c


def I_out(P):
    pts = sorted(p for p in outer_kinks(P) if Fr(1, 3) <= p <= 2 * LAM)
    if P.outer == "classes":   # add every crossing r = zz (zz is affine between the kinks of dens)
        extra = set()
        for l, r in zip(pts, pts[1:]):
            if r > 1 or l < Fr(1, 3):
                continue
            y1, y2 = l + (r - l) / 3, l + 2 * (r - l) / 3
            z1, z2 = P.outer_parts(y1)[1], P.outer_parts(y2)[1]
            bz = (z2 - z1) / (y2 - y1)
            az = z1 - bz * y1
            for ar, br in ((LAM, Fr(0)), (P.rank_icpt, -P.rho_r), (Fr(0), Fr(0))):
                if bz != br:
                    yc = (ar - az) / (bz - br)
                    if l < yc < r:
                        extra.add(yc)
        pts = sorted(set(pts) | extra)
    return sum((a * (r - l) + b * (r * r - l * l) / 2 for l, r, a, b in pieces(P.Tout, pts)), Fr(0))


def A_M(P, M, iout=None, inner=None):
    """Lai Thm 9.3 RHS without E_M: I_out + c_cr*lambda/M + int_3^M R/x^3 (exact)."""
    iout = I_out(P) if iout is None else iout
    inner = int_R_x3(P, 3, M) if inner is None else inner
    return iout + P.c_cr * LAM / M + inner


def A_inf(P, iout=None, inner200=None, periods=20000):
    """I_out + int_3^oo R/x^3.  Exact on [3,200]; beyond 200 R(x+40k) = R(x) + 40k F(x) (identity checked
    exactly for k = 1..3 at 7 points per piece), summed in float64 (math.fsum) for k < periods, remainder
    approximated by Fbar/X.  Returns (value, F-mean, check)."""
    iout = I_out(P) if iout is None else iout
    inner200 = int_R_x3(P, 3, 200) if inner200 is None else inner200
    base = pieces(P.R, inner_breaks(P, 200, 240))
    Fp = []
    for l, r, a, b in base:
        a1, b1 = affine_fit(lambda x: P.R(x + 40), l, r) or (None, None)
        if a1 is None:
            raise RuntimeError("R(x+40) not affine on a base piece")
        f0, f1 = (a1 - a) / 40, (b1 - b) / 40
        for k in (2, 3):  # check R(x+40k) = R(x) + 40k F(x)
            for i, j in _TEST[:7]:
                x = l + (r - l) * Fr(i, j)
                if P.R(x + 40 * k) != a + b * x + 40 * k * (f0 + f1 * x):
                    raise RuntimeError("periodic extension identity fails")
        Fp.append((l, r, a, b, f0, f1))
    Fbar = sum((f0 * (r - l) + f1 * (r * r - l * l) / 2 for l, r, a, b, f0, f1 in Fp), Fr(0)) / 40
    import numpy as np
    k = np.arange(periods, dtype=np.float64)
    terms = []
    for l, r, a, b, f0, f1 in Fp:
        # on [l+40k, r+40k]: R(w) = a + b x + 40k (f0 + f1 x), x = w - 40k in [l, r]
        c = 40.0 * k
        al_ = float(a) + c * float(f0)
        be_ = float(b) + c * float(f1)
        L, Rr = float(l) + c, float(r) + c
        A0 = al_ - be_ * c
        terms.append(be_ * (1 / L - 1 / Rr) + A0 / 2 * (1 / L ** 2 - 1 / Rr ** 2))
    X = 200 + 40 * periods
    tail = float(Fbar) / X
    val = float(iout) + float(inner200) + math.fsum(np.concatenate(terms).tolist()) + tail
    return val, Fbar


# ----------------------------------------------------------------------------------------------
# analytic side: comparison-measure energy bound (Lai Lemma 11.4)
# ----------------------------------------------------------------------------------------------
# Fauzan's Table 1 (16 nested arcsine components), from mo271/Zeta5@7fe73676 Apery/Measure.lean l. 28-44
# (10^12 a_j, 10^12 b_j, 10^12 c_j)
TABLE1 = [(3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
          (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
          (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
          (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
          (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
          (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
          (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
          (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577)]


def rho_fauzan():
    return [(Fr(a, 10 ** 12), Fr(b, 10 ** 12), Fr(c, 10 ** 12)) for a, b, c in TABLE1]


def mp_setup():
    import mpmath
    mpmath.mp.dps = 50
    return mpmath


def I_rho(rho):
    """Lai (91): sum_j (S_j^2 - S_{j-1}^2) log((b_j - a_j)/4), rho listed inner -> outer (nested)."""
    mp = mp_setup()
    S0, tot = Fr(0), mp.mpf(0)
    for a, b, c in rho:
        S1 = S0 + c
        tot += mp.mpf((S1 * S1 - S0 * S0).numerator) / (S1 * S1 - S0 * S0).denominator * \
            mp.log((mp.mpf(b.numerator) / b.denominator - mp.mpf(a.numerator) / a.denominator) / 4)
        S0 = S1
    return tot


def Cstar(nu):
    mp = mp_setup()
    al, lam = mp.mpf(3) / 40, mp.mpf(37) / 40
    return -2 * lam + 2 * nu * al * lam * (1 - mp.log(al)) + 3 * lam ** 2 - 2 * lam ** 2 * mp.log(2 * lam)


def np_V(nu, t):
    import numpy as np
    al = 3 / 40
    st = np.sqrt(t)
    with np.errstate(divide="ignore", invalid="ignore"):
        J1 = np.log(t + 1) - 2 + 2 * st * np.arctan(np.where(st > 0, 1 / np.where(st > 0, st, 1), 0))
        J1 = np.where(t > 0, J1, -2.0)
        Ja = al * np.log(t + al * al) - 2 * al + 2 * st * np.arctan(np.where(st > 0, al / np.where(st > 0, st, 1), 0))
        Ja = np.where(t > 0, Ja, 2 * al * (math.log(al) - 1))
    return 2 * np.pi * st + J1 - nu * Ja


def np_Uarc(a, b, t):
    import numpy as np
    inside = (t >= a) & (t <= b)
    m = (a + b) / 2
    with np.errstate(invalid="ignore"):
        out = np.log((np.abs(t - m) + np.sqrt(np.abs((t - a) * (t - b)))) / 2)
    return np.where(inside, math.log((b - a) / 4), out)


def tgrid(n=60000, tmax=60.0):
    import numpy as np
    u = np.linspace(0, 1, n)
    return np.unique(np.concatenate([tmax * u ** 3, np.linspace(0, 3, n // 2)]))


def sup_potential(rho, nu, extra_pts=()):
    """float64 sup_t 2U^rho - V_nu on a 90k-point grid on [0,60] plus all endpoints, refined locally.
    HEURISTIC part of U (Lai checks Fauzan's M0 on a 4100-point grid, p. 15)."""
    import numpy as np
    from scipy.optimize import minimize_scalar
    t = tgrid()
    ends = []
    for a, b, c in rho:
        for e in (float(a), float(b)):
            ends += [e, e * (1 - 1e-9), e * (1 + 1e-9)]
    t = np.unique(np.concatenate([t, np.array(ends + list(extra_pts))]))

    def F(tt):
        tt = np.atleast_1d(tt)
        U = sum(float(c) * np_Uarc(float(a), float(b), tt) for a, b, c in rho)
        return 2 * U - np_V(nu, tt)
    vals = F(t)
    best = float(vals.max())
    for i in np.argsort(vals)[-12:]:
        lo, hi = t[max(i - 1, 0)], t[min(i + 1, len(t) - 1)]
        if hi > lo:
            r = minimize_scalar(lambda x: -F(x)[0], bounds=(lo, hi), method="bounded",
                                options={"xatol": 1e-13})
            best = max(best, -r.fun)
    return best


def U_bound(rho, nu, M0):
    mp = mp_setup()
    lam = mp.mpf(37) / 40
    M0m = mp.mpf(M0.numerator) / M0.denominator
    return lam * M0m - I_rho(rho) + Cstar(nu)


def optimize_rho(nu, J=36, Lmin=0.004, Lmax=2.0, seed=0):
    """Comparison measure for V_nu: arcsine measures on [0, L_j] (L_j log-spaced in [Lmin, Lmax]); weights by
    SLSQP on the convex problem  min lambda*m - I(rho)  s.t. 2U^rho(t_k) - V(t_k) <= m, c >= 0, sum c = lambda.
    Deterministic (no random starts); float64; the result is then re-evaluated with sup_potential()."""
    import numpy as np
    from scipy.optimize import minimize
    lam = 37 / 40
    Ls = np.geomspace(Lmin, Lmax, J)
    tk = np.unique(np.concatenate([np.linspace(0, 1, 500) ** 2 * 6, Ls, Ls * 1.001, np.linspace(6, 40, 60)]))
    Umat = np.stack([np_Uarc(0.0, L, tk) for L in Ls], axis=1)        # (k, J)
    Vk = np_V(nu, tk)
    logL = np.log(Ls / 4)
    Imat = logL[np.maximum.outer(np.arange(J), np.arange(J))]          # I = c^T Imat c
    x0 = np.concatenate([np.full(J, lam / J), [float((2 * Umat @ np.full(J, lam / J) - Vk).max())]])

    def obj(x):
        c = x[:J]
        return lam * x[J] - c @ Imat @ c

    def grad(x):
        c = x[:J]
        g = np.zeros(J + 1)
        g[:J] = -2 * Imat @ c
        g[J] = lam
        return g
    cons = [{"type": "ineq", "fun": lambda x: x[J] - (2 * Umat @ x[:J] - Vk),
             "jac": lambda x: np.hstack([-2 * Umat, np.ones((len(tk), 1))])},
            {"type": "eq", "fun": lambda x: x[:J].sum() - lam,
             "jac": lambda x: np.concatenate([np.ones(J), [0.0]])}]
    res = minimize(obj, x0, jac=grad, constraints=cons, bounds=[(0, None)] * J + [(None, None)],
                   method="SLSQP", options={"maxiter": 2000, "ftol": 1e-14})
    c = np.clip(res.x[:J], 0, None)
    # exact rational measure: weights rounded to 1e-12, last nonzero weight absorbs the rounding
    cq = [Fr(round(ci * 1e12), 10 ** 12) for ci in c]
    idx = [i for i, ci in enumerate(cq) if ci > 0]
    cq[idx[-1]] += LAM - sum(cq)
    rho = [(Fr(0), Fr(round(L * 1e9), 10 ** 9), cq[i]) for i, L in enumerate(Ls) if cq[i] > 0]
    return rho, res


def U_for_nu(nu, cache):
    """Comparison-measure U for numerator power nu: best of (optimised arcsine family, Fauzan's rho).
    M0 := grid sup rounded UP to 1e-6."""
    key = str(nu)
    if key in cache:
        return cache[key]
    cands = []
    for name, rho in (("fauzan16", rho_fauzan()), ("opt36", optimize_rho(nu)[0])):
        sup = sup_potential(rho, nu)
        M0 = Fr(math.ceil(sup * 10 ** 6), 10 ** 6)
        U = U_bound(rho, nu, M0)
        cands.append((float(U), name, float(M0), sup, rho))
    cands.sort(key=lambda z: z[0])
    U, name, M0, sup, rho = cands[0]
    cache[key] = dict(U=U, measure=name, M0=M0, sup_grid=sup, n_components=len(rho),
                      I_rho=float(I_rho(rho)), Cstar=float(Cstar(nu)),
                      rho=[[str(a), str(b), str(c)] for a, b, c in rho],
                      alternatives={z[1]: z[0] for z in cands})
    return cache[key]


# ----------------------------------------------------------------------------------------------
# commands
# ----------------------------------------------------------------------------------------------
def fmt(x):
    return f"{float(x):+.10f}"


def cmd_anchors(log):
    res = {}
    # --- anchor 1: Lai (zeta(5), nu = 6) ---------------------------------------------------------
    P5 = Pkg(5, 6, "S")
    io5 = I_out(P5)
    in5 = int_R_x3(P5, 3, 20)
    Astar = io5 + in5 - Fr(2689, 48000)                      # Lai (101)/(103) with his tail bound
    A200_102 = Astar + 7 * LAM / 200 - (Fr(2923, 240) - Fr(1, 4)) / 200 ** 2 + Fr(32, 200 ** 3)
    lai = dict(I_out=Fr(127751, 96000), inner=Fr(322437603634266857629, 7535670527041937280000),
               Astar=Fr(9928298118277006344769, 7535670527041937280000),
               A200=Fr(127125602969131786927559, 94195881588024216000000))
    log("ANCHOR 1  Lai zeta(5), D_N^6  [Lai (84) p.14, (103)-(104) p.17]")
    log(f"  I_out             = {io5}  == 127751/96000: {io5 == lai['I_out']}")
    log(f"  int_3^20 R/x^3    = {in5}  == (103): {in5 == lai['inner']}")
    log(f"  A* (tail <= -2689/48000) == (103): {Astar == lai['Astar']}")
    log(f"  A_200 by (102)    = {A200_102} = {fmt(A200_102)}  == (104): {A200_102 == lai['A200']}")
    rho = rho_fauzan()
    Ir, Cs = I_rho(rho), Cstar(6)
    mp = mp_setup()
    Uval = mp.mpf(37) / 40 * mp.mpf(-1329) / 200 - Ir + Cs
    sup6 = sup_potential(rho, 6)
    log(f"  I(rho_Fauzan)     = {mp.nstr(Ir, 25)}   (Lai p.15: -2.126593445147050403253601)")
    log(f"  C*(6)             = {mp.nstr(Cs, 25)}   (Lai p.15: 2.65303599034048866112925)")
    log(f"  lam*M0-I+C*       = {mp.nstr(Uval, 20)}  with M0=-1329/200 (Lai p.15: -1.366995564512460936)")
    log(f"  <= U = -2733991/2000000 = -1.3669955: {Uval <= mp.mpf(-2733991) / 2000000}")
    log(f"  grid sup 2U^rho - V_6 = {sup6:.8f}  (Lai (93): -6.64989...; M0 = -6.645)  [HEURISTIC, float64 grid]")
    U5 = Fr(-2733991, 2000000)
    log(f"  A_200 + U         = {fmt(A200_102 + U5)}   (Lai (108): -0.0174078)")
    ok1 = (io5 == lai["I_out"] and in5 == lai["inner"] and Astar == lai["Astar"] and A200_102 == lai["A200"]
           and abs(float(Uval) - (-1.366995564512460936)) < 1e-15)
    # Thm 9.3 RHS exactly (the package), zeta(5)
    in5_200 = int_R_x3(P5, 3, 200)
    A200x = A_M(P5, 200, io5, in5_200)
    log(f"  package A_200 (Thm 9.3 RHS, exact, c_cr=6) = {fmt(A200x)}  (<= Lai's (102) by {fmt(A200_102 - A200x)})")
    res["lai_zeta5"] = dict(I_out=str(io5), inner_3_20=str(in5), Astar=str(Astar), A200_102=str(A200_102),
                            U_check=float(Uval), sup_grid=sup6, pkg_A200=str(A200x), ok=ok1)
    # --- anchor 2: audit (Anand zeta(7), nu = 8) -------------------------------------------------
    P7 = Pkg(7, 8, "S")
    io7 = I_out(P7)
    in7 = int_R_x3(P7, 3, 20)
    A0_anand = Fr(9928298118277006344769, 7535670527041937280000)   # Anand's A_0 (= Lai's zeta(5) A*)
    B0 = A0_anand + io7 + in7
    A200_89 = B0 + 9 * LAM / 200 - Fr(11549, 720 * 200 ** 2) + Fr(44, 200 ** 3)
    tgt = Fr(6626902387705935050696033, 1362217364503734816000000)
    log("ANCHOR 2  audit zeta(7), D_N^8  [[team handle]/zeta7-irrational@be55b3a4 FinalMargins.lean l.40-64]")
    log(f"  I_out             = {io7}  == 453803/288000: {io7 == Fr(453803, 288000)}")
    log(f"  int_3^20 R/x^3    = {in7}  == innerIntegral_value: "
        f"{in7 == Fr(120667538150827615739401, 708353029541942104320000)}")
    log(f"  A_200 + 44/25 by Anand (89) = {A200_89 + Fr(44, 25)} = {fmt(A200_89 + Fr(44, 25))}  == audit: "
        f"{A200_89 + Fr(44, 25) == tgt}")
    ok2 = (io7 == Fr(453803, 288000) and A200_89 + Fr(44, 25) == tgt)
    in7_200 = int_R_x3(P7, 3, 200)
    A200x7 = A_M(P7, 200, io7, in7_200)
    tail7 = in7_200 - in7 - 8 * LAM / 200  # just for the record
    log(f"  NOTE Anand's A_0 = {float(A0_anand):.7f} stands where int_20^oo R/x^3 belongs; package value:")
    log(f"  package A_200 (Thm 9.3 RHS, exact, c_cr=8) = {fmt(A200x7)};  package A_200 + 44/25 = "
        f"{fmt(A200x7 + Fr(44, 25))}")
    res["audit_zeta7"] = dict(I_out=str(io7), inner_3_20=str(in7), A200_89_plus_4425=str(A200_89 + Fr(44, 25)),
                              pkg_A200=str(A200x7), ok=ok2)
    # --- anchor 3 (coordinator, 21:20): Zeta5 Lean, M = 400 --------------------------------------
    d_int = sum((a * (r - l) + b * (r * r - l * l) / 2 for l, r, a, b in
                 pieces(lambda y: max(1 + 4 * AL - 3 * y - max(1 + AL - 3 * y, Fr(0)), Fr(0)),
                        [Fr(1, 3), Fr(1, 2)])), Fr(0))
    iout_z5 = io5 + d_int
    in5_400 = int_R_x3(P5, 3, 400)
    A400_z5 = iout_z5 + in5_400 + 6 * LAM / 400
    # Zeta5's own route on [20, 400]: R(x) <= x F(x) + 27/16 (Apery/Growth/TailIntegral.lean l. 26)
    mp = mp_setup()
    lam, al = mp.mpf(37) / 40, mp.mpf(3) / 40

    def intF_x2(lo, hi):  # int_lo^hi F(x)/x^2, F = 4lam + 2lam{x} - 12lam{alpha x}; exact pieces, 50 digits
        pts = sorted({Fr(lo), Fr(hi)} | {Fr(k) for k in range(lo, hi + 1)} |
                     {Fr(40 * k, 3) for k in range(1, 31) if lo < Fr(40 * k, 3) < hi})
        tot = mp.mpf(0)
        for l, r in zip(pts, pts[1:]):
            fx, fa = fl(l), fl(AL * l)          # on (l, r): {x} = x - fx, {al x} = al x - fa
            c0 = 4 * LAM - 2 * LAM * fx + 12 * LAM * fa  # F = c0 + c1 x
            c1 = 2 * LAM - 12 * LAM * AL
            L, Rr = mp.mpf(l.numerator) / l.denominator, mp.mpf(r.numerator) / r.denominator
            tot += mp.mpf(c0.numerator) / c0.denominator * (1 / L - 1 / Rr) + \
                mp.mpf(c1.numerator) / c1.denominator * mp.log(Rr / L)
        return tot
    tailZ5 = intF_x2(20, 400) + mp.mpf(27) / 16 / 2 * (1 / mp.mpf(20) ** 2 - 1 / mp.mpf(400) ** 2)
    A400_route = mp.mpf(iout_z5.numerator) / iout_z5.denominator + mp.mpf(in5.numerator) / in5.denominator + \
        tailZ5 + 6 * lam / 400
    log("ANCHOR 3  mo271/Zeta5 Lean (Comparator-verified d38a2888), cutoff M = 400  [Apery/Constants.lean l.13,33,36]")
    log(f"  int_(1/3)^(1/2) d(y) dy = {d_int}  (Lai Lemma 10.1: 9/640);  Zeta5 outer = I_out + 9/640 = {iout_z5}"
        f"  (Zeta5 scripts/growth/outer_gen.py: 129101/96000: {iout_z5 == Fr(129101, 96000)})")
    log(f"  Zeta5 route: outer + (5.18) + int_20^400 (xF+27/16)/x^3 + 6lam/400 = {mp.nstr(A400_route, 12)}"
        f"  <= Aeff = 136/100: {A400_route <= mp.mpf(136) / 100}")
    log(f"  package A_400 with Zeta5's outer (exact R on [3,400]) = {fmt(A400_z5)}")
    log(f"  Aeff + U = 136/100 - 2733991/2000000 = {Fr(136, 100) + Fr(-2733991, 2000000)}"
        f" = {fmt(Fr(136, 100) + Fr(-2733991, 2000000))}")
    log(f"  slack of the rounded certificate: 1.36 - route = {mp.nstr(mp.mpf(136) / 100 - A400_route, 8)}")
    # the constant growth_mN actually proves (Apery/Growth.lean l. 115-116, hsum): four range constants, the
    # tail one a rational upper bound -6843153/128000000 for int_20^400 (xF+27/16)/x^3 (Lean's own bound)
    tail_lean = Fr(-6843153, 128000000)
    A_Z5 = tail_lean + in5 + iout_z5 + 6 * LAM / 400
    A_Z5_miner = Fr(2031621487545722214389669, 1507134105408387456000000)   # INSIGHTS.md item 1
    A400_102 = Astar + 7 * LAM / 400 - (Fr(2923, 240) - Fr(1, 4)) / 400 ** 2 + Fr(32, 400 ** 3)
    tail_exact = tailZ5
    log(f"  Zeta5 proved sum (Growth.lean:115-116): -6843153/128000000 + (5.18) + 129101/96000 + 22.2/1600 = {A_Z5}"
        f" = {fmt(A_Z5)}  == INSIGHTS A_Z5: {A_Z5 == A_Z5_miner}")
    log(f"  its tail term: exact int_20^400 (xF+27/16)/x^3 = {mp.nstr(tail_exact, 12)} <= -6843153/128000000 = "
        f"{float(tail_lean):.10f}: {tail_exact <= mp.mpf(tail_lean.numerator) / tail_lean.denominator}")
    log(f"  Lai/Fauzan (102) at M=400 = {fmt(A400_102)};  A_Z5 - A_400(102) = {A_Z5 - A400_102}"
        f"  == 9/640 + 40993/128000000: {A_Z5 - A400_102 == Fr(9, 640) + Fr(40993, 128000000)}")
    log(f"  A_Z5 + U = {fmt(A_Z5 + Fr(-2733991, 2000000))}  (unrounded Zeta5 margin; certificate uses 1.36: -0.0069955)")
    res["zeta5_lean_M400"] = dict(d_int=str(d_int), outer=str(iout_z5), route=float(A400_route),
                                  pkg_A400=str(A400_z5), Aeff_plus_U=str(Fr(136, 100) + Fr(-2733991, 2000000)),
                                  A_Z5=str(A_Z5), A400_102=str(A400_102),
                                  ok=(iout_z5 == Fr(129101, 96000) and A400_route <= mp.mpf(136) / 100
                                      and A_Z5 == A_Z5_miner and A_Z5 < Fr(136, 100)
                                      and tail_exact <= mp.mpf(tail_lean.numerator) / tail_lean.denominator))
    res["all_ok"] = ok1 and ok2 and res["zeta5_lean_M400"]["ok"]
    log(f"ALL ANCHORS REPRODUCED: {res['all_ok']}")
    # --- revision Fri 22:00: general outer (criterion5 E13) -- consistency and reported identities --------
    log("REVISION CHECKS  (reading S outer = class sums of criterion5/derivation.md section 3, E13)")
    ys = [Fr(1, 3) + Fr(k, 601) + Fr(1, 100003) for k in range(400)]
    ys = [y for y in ys if y <= 1]
    fam = all(Pkg(s, s + 1, "S").Tout(y) == Pkg(s, s + 1, "S0").Tout(y) for s in (3, 5, 7, 9, 11) for y in ys)
    log(f"  class form == pre-revision linear form on nu = s+1 (s = 3..11, {len(ys)} exact points each): {fam}")
    io76, io56, io72 = I_out(Pkg(7, 6, "S")), I_out(Pkg(5, 6, "S")), I_out(Pkg(7, 2, "S"))
    st = [A_M(Pkg(7, 6, "S"), M, io76) - A_M(Pkg(5, 6, "S"), M, io56) for M in (40, 200)]
    log(f"  Theta(7,6) - Theta(5,6) (U cancels) at M = 40, 200: {st[0]}, {st[1]}  == 751/768: "
        f"{st[0] == st[1] == Fr(751, 768)};  I_out step = {io76 - io56} == 1387/3840: {io76 - io56 == Fr(1387, 3840)}")
    log(f"  I_out(7,2) = {io72}  == 31511/16000: {io72 == Fr(31511, 16000)}")
    res["revision"] = dict(family_equal=fam, sstep_76_56=str(st[1]), I_out_72=str(io72),
                           ok=fam and st[0] == st[1] == Fr(751, 768) and io72 == Fr(31511, 16000))
    log(f"REVISION CHECKS PASS: {res['revision']['ok']}")
    return res


def cmd_lai(log, ucache):
    """Lai's nu = 2 claim (laichunwing/Zeta7-is-Irrational@c42a984f, Programs 06-09)."""
    res = {}
    P_old = Pkg(7, 2, "LAI", Ncoef=2)        # Program 06 as coded: N coefficient nu ("old coeff")
    P_fix = Pkg(7, 2, "LAI")                 # Ncoef = 2 nu (Lai's Program 08 'CORRECTED'; 7-to-49 repo)
    lai = dict(A_0=Fr(-512225151, 10 ** 10), I_out=Fr(20093485686, 10 ** 10),
               I_inner=Fr(-225228508760, 10 ** 12), U_upper=Fr(-2306112885159, 10 ** 12))
    in_old = int_R_x3(P_old, 3, 20)
    in_fix = int_R_x3(P_fix, 3, 20)
    io_lai = I_out(P_fix)                  # Program 07 formula in the limit K -> oo (c_out = 9, rho_r = 2)
    log("LAI nu=2 (09_final_constants.txt inputs vs exact recomputation with Lai's own formulas)")
    log(f"  I_inner (Prog 06, 'old coeff' N = nu*lam*x[ax]) exact = {fmt(in_old)}   Lai: {fmt(lai['I_inner'])}")
    log(f"  I_inner (2*nu coefficient, Prog 08 'CORRECTED')  exact = {fmt(in_fix)}   Lai robustness: -0.18")
    log(f"  I_out (Prog 07 formula, K->oo, exact)                    = {fmt(io_lai)}   Lai (K=4e7 Simpson): "
        f"{fmt(lai['I_out'])}")
    tail_fix = None
    # tail int_20^oo with Lai's corrected formulas: exact to 200, then periodic sum
    v, Fbar = A_inf(P_fix, iout=Fr(0), inner200=int_R_x3(P_fix, 3, 200) - in_fix, periods=20000)
    tail_fix = v
    log(f"  A_0 = int_20^oo R/x^3 (corrected formulas)               = {tail_fix:+.10f}   Lai Prog 08: "
        f"{fmt(lai['A_0'])}   [F-mean {float(Fbar):+.6f}]")
    B0 = lai["A_0"] + lai["I_out"] + lai["I_inner"]

    def A89(B, M):
        return B + 9 * LAM / M - Fr(11549, 720 * M * M) + Fr(44, M ** 3)
    log(f"  Lai's A_200 (his inputs, Anand's polynomial 9lam/M-11549/(720M^2)+44/M^3) = {fmt(A89(B0, 200))};"
        f" + U_upper = {fmt(A89(B0, 200) + lai['U_upper'])}  (Lai: about -0.53)")
    # (a) Lai's own formulas, corrected coefficient, exact: package A_200 with Lai's constants
    A_lai_fix = A_M(P_fix, 200, io_lai, int_R_x3(P_fix, 3, 200))
    res["lai_inputs"] = {k: str(v) for k, v in lai.items()}
    res["I_inner_old"] = float(in_old)
    res["I_inner_fix"] = float(in_fix)
    res["I_out_lai_formula"] = float(io_lai)
    res["A0_fix"] = tail_fix
    res["A200_lai_inputs"] = float(A89(B0, 200))
    U2 = U_for_nu(2, ucache)
    log(f"  U for nu=2 (this tool, best comparison measure found: {U2['measure']}) = {U2['U']:+.6f}"
        f"   Lai Prog 04: {fmt(lai['U_upper'])}")
    rows = []
    for name, P in (("LAI-formulas, 'old coeff' (as run)", P_old), ("LAI-formulas, 2nu fixed", P_fix),
                    ("LAI-formulas, 2nu fixed, c_in=7 only", Pkg(7, 2, "LAI", c_in=7)),
                    ("LAI-formulas, 2nu fixed, rho_r=3 only", Pkg(7, 2, "LAI", rho_r=3)),
                    ("reading N (all nu-attributed)", Pkg(7, 2, "N")), ("reading S (s-attributed)", Pkg(7, 2, "S"))):
        io = I_out(P)
        inn = int_R_x3(P, 3, 200)
        A200 = A_M(P, 200, io, inn)
        rows.append((name, float(io), float(int_R_x3(P, 3, 20)), float(A200), float(A200) + lai_U(lai),
                     float(A200) + U2["U"], P.label()))
        log(f"  {name:40s} I_out={float(io):+.6f} int3^20={rows[-1][2]:+.6f} A_200={float(A200):+.6f} "
            f"A_200+U_Lai={rows[-1][4]:+.6f} A_200+U_ours={rows[-1][5]:+.6f}")
    res["rows"] = rows
    res["U2"] = {k: v for k, v in U2.items() if k != "rho"}
    return res


def lai_U(lai):
    return float(lai["U_upper"])


def cmd_table(log, ucache, nus=(4, 5, 6, 7, 8, 9, 10), ss=(5, 7, 9), with_inf=True):
    res = {"U": {}, "rows": []}
    for nu in list(nus) + [2]:
        Ui = U_for_nu(nu, ucache)
        res["U"][str(nu)] = {k: v for k, v in Ui.items() if k != "rho"}
        log(f"  U(nu={nu}) = {Ui['U']:+.6f}  [{Ui['measure']}, M0={Ui['M0']:+.6f}, I={Ui['I_rho']:+.6f}, "
            f"C*={Ui['Cstar']:+.6f}; alternatives {Ui['alternatives']}]")
    for reading in ("S", "N"):
        for s in ss:
            if reading == "N" and s != 7:
                continue   # reading N does not depend on s
            for nu in nus:
                P = Pkg(s, nu, reading)
                io = I_out(P)
                in200 = int_R_x3(P, 3, 200)
                A200 = A_M(P, 200, io, in200)
                Ainf = A_inf(P, io, in200)[0] if with_inf else float("nan")
                U = ucache[str(nu)]["U"]
                dio = float(io - I_out(Pkg(s, nu, "S0"))) if reading == "S" else 0.0
                row = dict(reading=reading, s=s if reading == "S" else "any", nu=nu, I_out=float(io),
                           inner_3_200=float(in200), A200=float(A200), A200_exact=str(A200), Ainf=Ainf, U=U,
                           margin200=float(A200) + U, margin_inf=Ainf + U, odd_nu=(nu % 2 == 1),
                           change_vs_pre_revision=dio)
                res["rows"].append(row)
                log(f"  {reading} s={row['s']} nu={nu:2d}{'*' if nu % 2 else ' '} I_out={row['I_out']:+.6f} "
                    f"A_200={row['A200']:+.6f} A_inf={Ainf:+.6f} U={U:+.6f} "
                    f"A_200+U={row['margin200']:+.6f} A_inf+U={row['margin_inf']:+.6f}")
    return res


def svg_figure(table, lai, path):
    """margin A_200 + U against nu: reading S for s = 5, 7, 9, reading N (s-independent); anchors and Lai."""
    rows = table["rows"]
    W, Hh, ml, mr, mt, mb = 760, 470, 70, 210, 40, 60
    xs = [4, 5, 6, 7, 8, 9, 10]
    allv = [r["margin200"] for r in rows] + [0.0, -0.6]
    lo, hi = math.floor(min(allv) * 2) / 2, math.ceil(max(allv) * 2) / 2

    def X(nu):
        return ml + (nu - 2) / (10 - 2) * (W - ml - mr)

    def Y(v):
        return mt + (hi - v) / (hi - lo) * (Hh - mt - mb)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{Hh}" font-family="Helvetica,Arial" '
           f'font-size="12"><rect width="100%" height="100%" fill="white"/>']
    out.append(f'<text x="{ml}" y="22" font-size="14" font-weight="bold">Margin A_200 + U (one package: Lai Thm 9.3 '
               f'at M=200, comparison-measure U) vs numerator power nu</text>')
    v = lo
    while v <= hi + 1e-9:
        out.append(f'<line x1="{ml}" x2="{W - mr}" y1="{Y(v):.1f}" y2="{Y(v):.1f}" stroke="#ddd"/>'
                   f'<text x="{ml - 8}" y="{Y(v) + 4:.1f}" text-anchor="end">{v:+.1f}</text>')
        v += 0.5
    out.append(f'<line x1="{ml}" x2="{W - mr}" y1="{Y(0):.1f}" y2="{Y(0):.1f}" stroke="black" stroke-width="1.5"/>')
    out.append(f'<text x="{W - mr + 4}" y="{Y(0) + 4:.1f}">0: method closes below</text>')
    for nu in range(2, 11):
        out.append(f'<text x="{X(nu):.1f}" y="{Hh - mb + 18}" text-anchor="middle">{nu}</text>')
    out.append(f'<text x="{(ml + W - mr) / 2}" y="{Hh - 15}" text-anchor="middle">numerator power nu '
               f'(exponent of D_N); odd nu: formula continuation</text>')
    styles = {("S", 5): "#1f77b4", ("S", 7): "#d62728", ("S", 9): "#2ca02c", ("N", "any"): "#7f7f7f"}
    names = {("S", 5): "reading S, s = 5", ("S", 7): "reading S, s = 7", ("S", 9): "reading S, s = 9",
             ("N", "any"): "reading N (any s)"}
    ly = mt + 10
    for key, col in styles.items():
        pts = [(r["nu"], r["margin200"]) for r in rows if (r["reading"], r["s"]) == key]
        if not pts:
            continue
        dash = ' stroke-dasharray="6,4"' if key[0] == "N" else ""
        out.append('<polyline fill="none" stroke="%s" stroke-width="2"%s points="%s"/>' % (
            col, dash, " ".join(f"{X(n):.1f},{Y(m):.1f}" for n, m in pts)))
        for n, m in pts:
            out.append(f'<circle cx="{X(n):.1f}" cy="{Y(m):.1f}" r="3" fill="{col}"/>')
        out.append(f'<line x1="{W - mr + 10}" x2="{W - mr + 34}" y1="{ly}" y2="{ly}" stroke="{col}" '
                   f'stroke-width="2"{dash}/><text x="{W - mr + 40}" y="{ly + 4}">{names[key]}</text>')
        ly += 18
    # anchors and Lai
    an = [(6, -0.0174078, "Lai zeta(5) (108)"), (8, 4.8648, "audit zeta(7) A_200+44/25")]
    for n, m, t in an:
        if lo <= m <= hi:
            out.append(f'<rect x="{X(n) - 5:.1f}" y="{Y(m) - 5:.1f}" width="10" height="10" fill="none" '
                       f'stroke="black"/><text x="{X(n) + 8:.1f}" y="{Y(m) - 8:.1f}">{t}</text>')
    lc = lai["A200_lai_inputs"] + float(Fr(-2306112885159, 10 ** 12))
    out.append(f'<path d="M {X(2) - 6:.1f} {Y(lc):.1f} l 6 -9 l 6 9 z" fill="orange"/>'
               f'<text x="{X(2) + 9:.1f}" y="{Y(lc) - 4:.1f}" font-size="11">Lai claim nu=2 (his inputs): {lc:+.2f}</text>')
    show = {"LAI-formulas, 2nu fixed": ("orange", "Lai's formulas, exact, 2nu fixed", 16),
            "LAI-formulas, 2nu fixed, c_in=7 only": ("#d62728", "same, inner offset c_in = s = 7", -10),
            "reading S (s-attributed)": ("#d62728", "reading S", 12)}
    for name, io, i320, A200, mLai, mOurs, lab in lai["rows"]:
        if name in show and lo <= mOurs <= hi:
            col, txt, dy = show[name]
            out.append(f'<circle cx="{X(2):.1f}" cy="{Y(mOurs):.1f}" r="4" fill="none" stroke="{col}" '
                       f'stroke-width="2"/><text x="{X(2) + 9:.1f}" y="{Y(mOurs) + dy:.1f}" font-size="11">'
                       f'nu=2, {txt}: {mOurs:+.2f}</text>')
    out.append(f'<text x="{W - mr + 10}" y="{ly + 14}" font-size="11">squares: published anchors</text>')
    out.append('</svg>')
    with open(path, "w") as f:
        f.write("\n".join(out))


def main():
    os.makedirs(OUT, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    lines = []

    def log(s):
        print(s, flush=True)
        lines.append(s)
    ucache_path = os.path.join(OUT, "U_cache.json")
    ucache = json.load(open(ucache_path)) if os.path.exists(ucache_path) and cmd != "all" else {}
    result = {}
    if cmd in ("anchors", "all"):
        result["anchors"] = cmd_anchors(log)
        if not result["anchors"]["all_ok"]:
            log("ANCHORS FAILED: stopping before any new value")
            sys.exit(1)
    if cmd in ("lai", "all"):
        result["lai"] = cmd_lai(log, ucache)
    if cmd in ("table", "all"):
        result["table"] = cmd_table(log, ucache)
    json.dump(ucache, open(ucache_path, "w"), indent=1)
    if cmd in ("figure", "all"):
        if "table" not in result:
            result = json.load(open(os.path.join(OUT, "results.json")))
        svg_figure(result["table"], result["lai"], os.path.join(OUT, "margin_vs_nu.svg"))
    with open(os.path.join(OUT, f"{cmd}.log"), "w") as f:
        f.write("\n".join(lines) + "\n")
    if cmd == "all":
        with open(os.path.join(OUT, "results.json"), "w") as f:
            json.dump(result, f, indent=1, default=str)


if __name__ == "__main__":
    main()
