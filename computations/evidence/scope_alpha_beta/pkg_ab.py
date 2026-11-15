#!/usr/bin/env python3
"""pkg_ab.py -- Fauzan's bound package with a FREE Hankel size H = beta*K (problem #108, scope widening).

EVENT WORK, Sat Nov 14 2026 (04:17-05:08 PT), advocate:scope-alpha-beta (Claude Opus 5.5).
Derivation: derivation_beta.md (PROOF-DRAFT).  This file evaluates it; it imports ../margin/theta.py read-only
(pure helpers only: pieces, affine_fit, _TEST) and never edits it.

Parameters: s odd, nu even (exponent of D_N), alpha = N/K, beta = H/K (Hankel size), lam := 1 - alpha = r/K
(r = K - N = number of X-dependent poles).  At beta = lam everything below is theta.py reading 'S' (= E13):
check_e13.py verifies that as an exact identity.

What changes with beta (derivation_beta.md section 2):
  inner   H_L := beta + (nu/2) alpha replaces Lai's H = lam + (nu/2) alpha in T = floor(2 H_L x), sigma = H_L x - T/2
          (Fauzan (4.4) with h -> H); the normaliser part N uses beta: 2 beta x[x] - 2 nu beta x[alpha x] - 2 J(beta x)
  outer   class costs unchanged; zero-weight rows z -> z + (beta - lam); rank intercept 1 + (nu-2) alpha ->
          2 beta - 1 + nu alpha, clamp lam -> beta; normaliser -2 beta [1/y] + sum_j (2 beta - j y)_+; upper limit 2 beta
  crude   (s+1) beta / M   (irrelevant at M -> oo)
  analytic V_{nu,alpha} unchanged; comparison measure of mass beta; C*(nu, alpha, beta) (Xu (11) with lam -> beta).
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "margin"))
import theta as TH  # noqa: E402  (read-only import: pieces, affine_fit, _TEST are pure functions)

pieces, affine_fit, _TEST = TH.pieces, TH.affine_fit, TH._TEST


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


def period(al, be, nu):
    """smallest integer P with P*alpha, 2*beta*P, 2*H_L*P integers (then R(x+P) - R(x) = P F(x))."""
    al, be = Fr(al), Fr(be)
    HL = be + Fr(nu, 2) * al
    P = 1
    for q in (al, 2 * be, 2 * HL, 1 - al, 1 + al, 2 * (HL - 1) if HL != 1 else Fr(1)):
        P = P * q.denominator // math.gcd(P, q.denominator)
    return P


class PkgAB:
    def __init__(self, s, nu, al, be):
        self.s, self.nu, self.al, self.be = s, Fr(nu), Fr(al), Fr(be)
        self.lam = 1 - self.al
        self.HL = self.be + self.nu / 2 * self.al
        self.c_in, self.c_out, self.rho_r, self.c_cr = Fr(s), Fr(s + 2), Fr(s - 1, 2), Fr(s + 1)
        self.rank_icpt = 2 * self.be - 1 + self.nu * self.al
        self.P = period(self.al, self.be, nu)

    # ---------------- inner range: Fauzan (4.4)-(4.8), (5.4)-(5.6) with h -> H ----------------
    def R(self, x):
        AL, H = self.al, self.HL
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
            bb = self.nu / 2 * ell(AL * x, z)
            I += (T - bb) * (T + bb - l - self.c_in) * (b - a)
        G = I + sl * (2 * T - q - self.c_in) + max(sl - nplus, Fr(0))
        N = 2 * self.be * x * fl(x) - 2 * self.nu * self.be * x * fl(AL * x) - 2 * Jfun(self.be * x)
        return -G - N

    def F(self, x):
        """Prop. 1': R = x F + Q with F = (s-1) beta + 2 beta {x} - 2 nu beta {alpha x}."""
        return (self.s - 1) * self.be + 2 * self.be * frac(x) - 2 * self.nu * self.be * frac(self.al * x)

    def Q(self, x):
        """Prop. 1' (s-free): [tau(tau-s') - (tau-s')_+ + eta(1-eta)]/2 + (nu/2)^2 int B^2 - (nu/2) int A B."""
        tau, sp, eta = frac(2 * self.HL * x), frac(2 * x), frac(2 * self.be * x)
        bps = sorted({Fr(0), Fr(1, 2), d0(frac(x)), d0(frac(self.al * x))})
        IB2 = IAB = Fr(0)
        for a, b in zip(bps, bps[1:]):
            if b <= a:
                continue
            z = (a + b) / 2
            A = ell(x, z) - 2 * x
            B = ell(self.al * x, z) - 2 * self.al * x
            IB2 += B * B * (b - a)
            IAB += A * B * (b - a)
        return (tau * (tau - sp) - max(tau - sp, Fr(0)) + eta * (1 - eta)) / 2 + (self.nu / 2) ** 2 * IB2 - \
            self.nu / 2 * IAB

    # ---------------- outer range: Fauzan (4.10)-(4.14) + Lemma 4.2, H free ----------------
    def outer_parts(self, y):
        s, nu, AL = Fr(self.s), self.nu, self.al
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
        zz = (y - 2 * AL) + sum(dn * z1(l) for l, dn in dens.items()) + (self.be - self.lam)
        r = min(self.be, max(Fr(0), self.rank_icpt - self.rho_r * y))
        return cost, zz, r

    def Tout(self, y):
        g = Fr(0)
        if Fr(1, 3) < y <= 1:
            cost, zz, r = self.outer_parts(y)
            if zz < 0:
                raise ValueError(f"beta below the outer saturation bound at y={y} (z = {zz})")
            g = cost + min(r, zz)
        jmax = fl(2 * self.be / y) + 2
        scal = -2 * self.be * fl(1 / y) + sum(max(2 * self.be - j * y, Fr(0)) for j in range(1, jmax + 1))
        return g + scal

    def zmin(self):
        """min over y in (1/3, 1] of the zero-row count z_beta(y) (affine between kinks; checked at kinks)."""
        pts = sorted(p for p in self.outer_kinks() if Fr(1, 3) <= p <= 1)
        vals = []
        for l, r in zip(pts, pts[1:]):
            for yy in (l + (r - l) / 10 ** 6, r - (r - l) / 10 ** 6, (l + r) / 2):
                vals.append(self.outer_parts(yy)[1])
        return min(vals)

    def outer_kinks(self):
        a, be = self.al, self.be
        I, rho = self.rank_icpt, self.rho_r
        c = {Fr(1, 3), Fr(1, 2), Fr(1), 2 * be, max(Fr(1), 2 * be)}
        for k in (1, 2, 3):
            c |= {Fr(1, k), (1 - a) / k, (1 + a) / (k + 1), Fr(1, k + 1), (1 + a) / k}
        c |= {2 * be / j for j in range(1, 12)} | {Fr(1, j) for j in range(1, 12)}
        if rho != 0:
            c |= {I / rho, (I - be) / rho}
        return {x for x in c if x > 0}

    # ---------------- exact integrals ----------------
    def inner_breaks(self, lo, hi):
        AL, be, H = self.al, self.be, self.HL
        cs = {Fr(1), Fr(2), AL, 2 * AL, 2 * be, 2 * H, 1 - AL, 1 + AL, 2 * (1 - AL), 2 * (1 + AL), 4 * AL, 8 * AL,
              2 * (1 + 2 * AL)}
        if H != 1:
            cs.add(abs(2 * (H - 1)))
        pts = {Fr(lo), Fr(hi)}
        for c in cs:
            k = fl(lo * c)
            while Fr(k) / c <= hi:
                x = Fr(k) / c
                if lo < x < hi:
                    pts.add(x)
                k += 1
        return sorted(pts)

    def int_R_x3(self, lo, hi):
        tot = Fr(0)
        for l, r, a, b in pieces(self.R, self.inner_breaks(lo, hi)):
            tot += b * (1 / l - 1 / r) + a / 2 * (1 / l ** 2 - 1 / r ** 2)
        return tot

    def I_out(self):
        top = max(Fr(1), 2 * self.be)
        pts = sorted(p for p in self.outer_kinks() if Fr(1, 3) <= p <= top)
        extra = set()
        for l, r in zip(pts, pts[1:]):
            if r > 1 or l < Fr(1, 3):
                continue
            y1, y2 = l + (r - l) / 3, l + 2 * (r - l) / 3
            z1, z2 = self.outer_parts(y1)[1], self.outer_parts(y2)[1]
            bz = (z2 - z1) / (y2 - y1)
            az = z1 - bz * y1
            for ar, br in ((self.be, Fr(0)), (self.rank_icpt, -self.rho_r), (Fr(0), Fr(0))):
                if bz != br:
                    yc = (ar - az) / (bz - br)
                    if l < yc < r:
                        extra.add(yc)
        pts = sorted(set(pts) | extra)
        return sum((a * (r - l) + b * (r * r - l * l) / 2 for l, r, a, b in pieces(self.Tout, pts)), Fr(0))

    def X0(self, start=40):
        """base point of the periodic tail: the smallest multiple of P that is >= start (R(x + Pk) = R(x) + Pk F(x)
        holds for every x >= 3, since every floor in R shifts by an integer; checked on the base period)."""
        return Fr(-(-start // self.P) * self.P)

    def periodic_base(self):
        """affine pieces of R on [X0, X0 + P] with F's pieces; the identity R(x + Pk) = R(x) + Pk F(x) is checked
        exactly at k = 1, 2, 3 (R(x+Pk) is quadratic in k, so this proves it for every k >= 0)."""
        X0, P = self.X0(), self.P
        base = pieces(self.R, self.inner_breaks(X0, X0 + P))
        out = []
        for l, r, a, b in base:
            a1, b1 = affine_fit(lambda x: self.R(x + P), l, r) or (None, None)
            if a1 is None:
                raise RuntimeError("R(x+P) not affine on a base piece")
            f0, f1 = (a1 - a) / P, (b1 - b) / P
            for k in (2, 3):
                for i, j in _TEST[:7]:
                    x = l + (r - l) * Fr(i, j)
                    if self.R(x + P * k) != a + b * x + P * k * (f0 + f1 * x):
                        raise RuntimeError("periodic identity fails")
            out.append((l, r, a, b, f0, f1))
        Fbar = sum((f0 * (r - l) + f1 * (r * r - l * l) / 2 for l, r, a, b, f0, f1 in out), Fr(0)) / P
        return out, Fbar

    def A_star_float(self, iout=None, innerX0=None, periods=4000):
        """I_out + int_3^oo R/x^3: exact on [3, X0], float64 periodic sum beyond (theta.A_inf's method, period P)."""
        import numpy as np
        iout = self.I_out() if iout is None else iout
        innerX0 = self.int_R_x3(3, self.X0()) if innerX0 is None else innerX0
        Fp, Fbar = self.periodic_base()
        P = self.P
        k = np.arange(periods, dtype=np.float64)
        terms = []
        for l, r, a, b, f0, f1 in Fp:
            c = P * k
            al_ = float(a) + c * float(f0)
            be_ = float(b) + c * float(f1)
            L, Rr = float(l) + c, float(r) + c
            A0 = al_ - be_ * c
            terms.append(be_ * (1 / L - 1 / Rr) + A0 / 2 * (1 / L ** 2 - 1 / Rr ** 2))
        X = float(self.X0()) + P * periods
        val = float(iout) + float(innerX0) + math.fsum(np.concatenate(terms).tolist()) + float(Fbar) / X
        return val, Fbar

    def A_M(self, M, iout, inner_3_M):
        return iout + self.c_cr * self.be / M + inner_3_M


# ---------------- La >= 0 (Fauzan p. 10 after (4.4), h -> H) ----------------
def lmax(y):
    pts = sorted({Fr(0), Fr(1, 2)} | {d0(frac(y))})
    return max(ell(y, (a + b) / 2) for a, b in zip(pts, pts[1:]) if b > a)


def La_check(nu, al, be, slack=Fr(21, 20)):
    """min over x >= 3 of floor(2 H_L x - slack) + 1 - (nu/2) lmax(alpha x)  (param_scan.La_check with lam -> beta
    in H_L; exact step function).  Admissible iff >= 0."""
    al, be = Fr(al), Fr(be)
    H = be + Fr(nu, 2) * al
    X0 = max((Fr(nu, 2) + slack) / (2 * be) + 2, Fr(4))
    br = {Fr(3), X0}
    k = math.floor(2 * H * 3 - slack)
    while (k + slack) / (2 * H) <= X0:
        x = (k + slack) / (2 * H)
        if x > 3:
            br.add(x)
        k += 1
    k = 0
    while Fr(k, 2) / al <= X0:
        x = Fr(k, 2) / al
        if x > 3:
            br.add(x)
        k += 1
    br = sorted(br)
    best = None
    for a, b in zip(br, br[1:]):
        for x in (a, (a + b) / 2):
            v = math.floor(2 * H * x - slack) + 1 - Fr(nu, 2) * lmax(al * x)
            if best is None or v < best[0]:
                best = (v, x)
    return best


# ---------------- analytic side (Xu (6)-(12) with mass beta; Lai Lemma 11.4; derivation.md Lemma 2) ----------------
def V_np(nu, al, t):
    import numpy as np
    st = np.sqrt(t)
    with np.errstate(divide="ignore", invalid="ignore"):
        J1 = np.log(t + 1) - 2 + 2 * st * np.arctan(np.where(st > 0, 1 / np.where(st > 0, st, 1), 0))
        J1 = np.where(t > 0, J1, -2.0)
        Ja = al * np.log(t + al * al) - 2 * al + 2 * st * np.arctan(np.where(st > 0, al / np.where(st > 0, st, 1), 0))
        Ja = np.where(t > 0, Ja, 2 * al * (math.log(al) - 1))
    return 2 * np.pi * st + J1 - nu * Ja


def Cstar_f(nu, al, be):
    al, be = float(al), float(be)
    return -2 * be + 2 * nu * al * be * (1 - math.log(al)) + 3 * be ** 2 - 2 * be ** 2 * math.log(2 * be)


def intV_arcsine(nu, al, Ls, n=400):
    """int V d omega_[0,L] for each L (Gauss-Chebyshev midpoints in theta; V smooth in theta)."""
    import numpy as np
    th = (np.arange(n) + 0.5) * np.pi / n
    out = []
    for L in Ls:
        t = L / 2 * (1 - np.cos(th))
        out.append(V_np(nu, float(al), t).mean())
    return np.array(out)


def _qp(nu, al, be, comps):
    """max over c >= 0, sum c = beta of c^T I c - v.c for nested arcsine components [(a_j, b_j)] (inner -> outer)."""
    import numpy as np
    from scipy.optimize import minimize
    bf = float(be)
    J = len(comps)
    v = []
    n = 400
    th = (np.arange(n) + 0.5) * np.pi / n
    for a, b in comps:
        m, h = (float(a) + float(b)) / 2, (float(b) - float(a)) / 2
        v.append(V_np(nu, float(al), m + h * np.cos(th)).mean())
    v = np.array(v)
    logw = np.log(np.array([(float(b) - float(a)) / 4 for a, b in comps]))
    Im = logw[np.maximum.outer(np.arange(J), np.arange(J))]
    res = minimize(lambda c: -(c @ Im @ c - v @ c), np.full(J, bf / J), jac=lambda c: -(2 * Im @ c - v),
                   bounds=[(0, None)] * J,
                   constraints=[{"type": "eq", "fun": lambda c: c.sum() - bf, "jac": lambda c: np.ones(J)}],
                   method="SLSQP", options={"maxiter": 3000, "ftol": 1e-15})
    c = np.clip(res.x, 0, None)
    cq = [Fr(round(ci * 1e12), 10 ** 12) for ci in c]
    idx = [i for i, ci in enumerate(cq) if ci > 0]
    cq[idx[-1]] += Fr(be) - sum(cq)
    sig = [(comps[i][0], comps[i][1], cq[i]) for i in range(J) if cq[i] > 0]
    cf = np.array([float(x) for x in cq])
    return float(cf @ Im @ cf - v @ cf + Cstar_f(nu, al, be)), sig, bool(res.success)


FAMILIES = tuple([("zero", 0, 0, Fr(2, 1000))] +
                 [("nest", r, g, bm) for r in (Fr(9, 10), Fr(3, 4), Fr(6, 10), Fr(45, 100))
                  for g in (Fr(15, 100), Fr(3, 10), Fr(1, 2), Fr(9, 10)) for bm in (Fr(2, 1000),)] +
                 [("nest", Fr(9, 10), g, Fr(1, 100)) for g in (Fr(15, 100), Fr(3, 10))])


def family(name, r, g, J=40, bmin=Fr(2, 1000), bmax=Fr(4)):
    """nested intervals: b_j geometric in [bmin, bmax] (rounded to 1e-9); a_j = 0 ('zero') or
    a_j = r b_1 (b_1/b_j)^g rounded to 1e-12 ('nest'; decreasing, so the intervals are nested)."""
    import numpy as np
    bs = [Fr(round(b * 1e9), 10 ** 9) for b in np.geomspace(float(bmin), float(bmax), J)]
    if name == "zero":
        return [(Fr(0), b) for b in bs]
    b1 = float(bs[0])
    return [(Fr(round(float(r) * b1 * (b1 / float(b)) ** float(g) * 1e12), 10 ** 12), b) for b in bs]


def lb_opt(nu, al, be, fams=FAMILIES):
    """best dual bound LB = I(sigma) - int V dsigma + C*(nu, alpha, beta) over the nested arcsine families above
    (float; Lemma 2 makes ANY sigma of mass beta a valid trial measure)."""
    best = None
    for name, r, g, bm in fams:
        val, sig, ok = _qp(nu, al, be, family(name, r, g, bmin=bm))
        if best is None or val > best[0]:
            best = (val, sig, dict(family=f"{name}:{r}:{g}:{bm}", success=ok, n_comp=len(sig)))
    return best


def U_float(nu, al, be, sig):
    """HEURISTIC upper end: U(sigma) = beta M0 - I(sigma) + C* with M0 = float grid sup of 2U^sigma - V on [0, 60]."""
    import numpy as np
    t = np.unique(np.concatenate([60 * np.linspace(0, 1, 40000) ** 3, np.linspace(0, 4, 20000),
                                  np.array([float(L) for _, L, _ in sig] + [float(a) for a, _, _ in sig])]))
    U = np.zeros_like(t)
    I = 0.0
    for a, L, c in sig:
        U += float(c) * TH.np_Uarc(float(a), float(L), t)
    w = [float(L) - float(a) for a, L, _ in sig]
    for i, (a, L, c) in enumerate(sig):
        for j, (a2, L2, c2) in enumerate(sig):
            I += float(c) * float(c2) * math.log(w[max(i, j)] / 4)
    M0 = float((2 * U - V_np(nu, float(al), t)).max())
    return float(be) * M0 - I + Cstar_f(nu, al, be), M0
