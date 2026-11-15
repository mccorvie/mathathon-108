#!/usr/bin/env python3
"""[108/N E730] Centred-form (mean-value) lower bound of the zeta(7) floor on a box of (alpha, beta), fixed nu.

EVENT WORK, lane N (Claude Opus 5.5). Imports read-only: scope_alpha_beta/pkg_ab.py, certify/{ivlib,run}.py, box.py.
Labels: COMPUTED (mpmath interval arithmetic, 113 bits, plus exact rationals); the reductions are PROOF-DRAFT (README.md).

On the derived region, for every (alpha, beta) in the box B with centre m = (alpha_m, beta_m):
  floor7 >= f(alpha, beta) := I~(alpha, beta) - 5/144 + S(alpha, beta), where
  I~ = int_{1/3}^{Y} T~(y) dy, T~ = T_out with min(r, zz) -> min(r, max(zz, 0)) (equal where zz >= 0, i.e. on the region),
       Y = max(1, 2 beta_1) fixed on the box (T~ = 0 for y > max(1, 2 beta));
  S = 2 beta c1 + 2 nu beta alpha (gamma + ln 3) + 3 beta^2 - 2 beta^2 ln(2 beta) + t^2 I_c - t W(alpha),  t = beta/beta_m,
      I_c = I(sigma_c), W(alpha) = int V_{nu,alpha} d sigma_c, sigma_c = lb_opt(nu, alpha_m, beta_m) (mass beta_m).
      (S = F-part + C* + LB(t sigma_c) - C*... : the F-part 2b + 2b c1 - 2 nu b g(a) plus C* = -2b + 2 nu a b (1 - ln a) +
      3b^2 - 2b^2 ln 2b collapse to the first three terms; the ln a terms and the 2b terms cancel exactly.)
  Mean value form: f(p) >= f(m) - (da/2) max|Ga + Da| - (db/2) max|Gb + Db|, with Ga, Gb enclosures of the gradient of I~
  over B (forward mode through T~'s min/max, summed over y-cells) and Da, Db enclosures of the gradient of S over B:
      dS/da = 2 nu b (gamma + ln 3) + t nu sum_i w_i U_i(a),  U_i(a) = int ln(s + a^2) d mu_i(s)
            = ln((c_i + a^2 + sqrt((c_i + a^2)^2 - h_i^2)) / 2)   (arcsine mu_i on [c_i - h_i, c_i + h_i]; increasing in a);
      dS/db = 2 c1 + 2 nu a (gamma + ln 3) + 4b - 4b ln(2b) + 2 t I_c / b_m - W(a) / b_m,
      W(a) in [W_lo(a_m), W_hi(a_m)] - nu (a - a_m) sum_i w_i U_i(xi).
  W_hi by certify_min.lb_cert's quadrature (Jensen for the concave part, chords for the convex part); W_lo by the mirror
  (chords for the concave part, Jensen for the convex part).
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import box as BX     # noqa: E402  (sets up the paths and the interval library)
from box import iv, ivq, I, PA, L, CR  # noqa: E402

S7 = 7
LN3 = iv.log(3)
GL = BX.GAMMA + LN3


class PkgT(PA.PkgAB):
    """pkg_ab's package with T~: min(r, max(zz, 0)) and no exception below saturation."""

    def Tout(self, y):
        g = Fr(0)
        if Fr(1, 3) < y <= 1:
            cost, zz, r = self.outer_parts(y)
            g = cost + min(r, max(zz, Fr(0)))
        jmax = PA.fl(2 * self.be / y) + 2
        scal = -2 * self.be * PA.fl(1 / y) + sum(max(2 * self.be - j * y, Fr(0)) for j in range(1, jmax + 1))
        return g + scal


# ---------------- forward mode: interval value + exact gradient hull (d/dalpha, d/dbeta) ----------------
class Du:
    __slots__ = ("v", "ga", "gb")

    def __init__(self, v, ga=(Fr(0), Fr(0)), gb=(Fr(0), Fr(0))):
        self.v, self.ga, self.gb = v, ga, gb

    def __add__(self, o):
        o = o if isinstance(o, Du) else Du(cst(o))
        return Du(self.v + o.v, (self.ga[0] + o.ga[0], self.ga[1] + o.ga[1]), (self.gb[0] + o.gb[0], self.gb[1] + o.gb[1]))
    __radd__ = __add__

    def __neg__(self):
        return Du(-self.v, (-self.ga[1], -self.ga[0]), (-self.gb[1], -self.gb[0]))

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Du) else Du(cst(o))))

    def __rsub__(self, o):
        return (-self) + o

    def scale(self, c):
        c = Fr(c)
        lo_a, hi_a = sorted((self.ga[0] * c, self.ga[1] * c))
        lo_b, hi_b = sorted((self.gb[0] * c, self.gb[1] * c))
        return Du(self.v * ivq(c), (lo_a, hi_a), (lo_b, hi_b))


def cst(x):
    return x if not isinstance(x, (int, Fr)) else ivq(Fr(x))


def hull(g, h):
    return (min(g[0], h[0]), max(g[1], h[1]))


def dmin(X, Y):
    if X.v.hi <= Y.v.lo:
        return X
    if Y.v.hi <= X.v.lo:
        return Y
    return Du(BX.imin(X.v, Y.v), hull(X.ga, Y.ga), hull(X.gb, Y.gb))


ZERO = Du(iv.mpf(0))


def dmax0(X):
    if X.v.lo >= 0:
        return X
    if X.v.hi <= 0:
        return ZERO
    return Du(BX.imax0(X.v), hull(X.ga, (Fr(0), Fr(0))), hull(X.gb, (Fr(0), Fr(0))))


def tout_dual(y0, y1, A, B, nu):
    """T~ on [y0, y1] x box as Du; also returns the zz interval (or None for y > 1)."""
    Y = Du(I(y0, y1))
    a = Du(A, (Fr(1), Fr(1)), (Fr(0), Fr(0)))
    b = Du(B, (Fr(0), Fr(0)), (Fr(1), Fr(1)))
    k = 2 if y1 <= Fr(1, 2) else (1 if y1 <= 1 else 0)
    g = ZERO
    zz = None
    if k >= 1:
        lam = 1 - a
        v = 1 - Y.scale(k)
        u = dmax0(a + v - Y)
        mv = dmin(a, v)
        dens = {2 * k: a - mv, 2 * k + 1: mv - u, 2 * k + 2: u}
        cost = ((1 - Y) - sum((dn.scale(l - 2) for l, dn in dens.items()), ZERO)).scale(S7 + 2) + \
            sum((dn.scale(BX.c1_fun(l, nu)) for l, dn in dens.items()), ZERO)
        zzd = (Y - a.scale(2)) + sum((dn.scale(BX.z1_fun(l, nu)) for l, dn in dens.items()), ZERO) + (b - lam)
        zz = zzd.v
        rank = b.scale(2) - 1 + a.scale(nu)
        r = dmin(b, dmax0(rank - Y.scale(Fr(S7 - 1, 2))))
        g = cost + dmin(r, dmax0(zzd))
    jmax = int(2 * float(B.hi) / float(Y.v.lo)) + 3
    scal = b.scale(-2 * k) + sum((dmax0(b.scale(2) - Y.scale(j)) for j in range(1, jmax + 1)), ZERO)
    return g + scal, zz


def iout_grad(a0, a1, b0, b1, nu, n=600):
    A, B = I(a0, a1), I(b0, b1)
    top = max(Fr(1), 2 * Fr(b1))
    cuts = [Fr(1, 3), Fr(1, 2), Fr(1)] + ([top] if top > 1 else [])
    Ga, Gb = [Fr(0), Fr(0)], [Fr(0), Fr(0)]
    invalid = False
    for lo, hi in zip(cuts, cuts[1:]):
        m = max(4, int(n * (hi - lo)))
        for i in range(m):
            y0, y1 = lo + (hi - lo) * Fr(i, m), lo + (hi - lo) * Fr(i + 1, m)
            T, zz = tout_dual(y0, y1, A, B, nu)
            w = y1 - y0
            Ga[0] += w * T.ga[0]; Ga[1] += w * T.ga[1]
            Gb[0] += w * T.gb[0]; Gb[1] += w * T.gb[1]
            if zz is not None and zz.hi < 0:
                invalid = True
    return Ga, Gb, invalid


# ---------------- the smooth part S ----------------
def U_arcsine(comp, a):
    """int ln(s + a^2) d mu(s), mu the arcsine (equilibrium) probability measure of [l, r] (a rational, a >= 0)."""
    l, r, _ = comp
    c, h = ivq((Fr(l) + Fr(r)) / 2), ivq((Fr(r) - Fr(l)) / 2)
    z = c + ivq(Fr(a) ** 2)
    return iv.log((z + iv.sqrt(BX.imax0(z * z - h * h))) / 2)


def intV_lower(nu, al, sig, N=100):
    """Rigorous LOWER bound of int V_{nu,al} d sigma: chords for the concave part Vinc, Jensen for the convex part."""
    dth = iv.pi / N
    C = [iv.cos(iv.pi * k / N) for k in range(N + 1)]
    Sn = [iv.sin(iv.pi * k / N) for k in range(N + 1)]
    C[0], Sn[0], C[N], Sn[N] = iv.mpf(1), iv.mpf(0), iv.mpf(-1), iv.mpf(0)
    cbar = [(Sn[k + 1] - Sn[k]) / dth for k in range(N)]
    mu = [(cbar[k] - C[k + 1]) / (C[k] - C[k + 1]) for k in range(N)]
    tot = iv.mpf(0)
    for a, b, c in sig:
        m, h = ivq((a + b) / 2), ivq((b - a) / 2)
        tk = [L.nonneg(m + h * C[k]) for k in range(N + 1)]
        vin = [CR.Vinc_iv(T) for T in tk]
        inc = iv.mpf(0)
        dec = iv.mpf(0)
        for k in range(N):
            inc = inc + mu[k] * vin[k] + (1 - mu[k]) * vin[k + 1]
            dec = dec + (-nu) * CR.J_iv(Fr(al), L.nonneg(m + h * cbar[k]))
        tot = tot + ivq(c) * (inc + dec) / N
    return tot


def absmax(lo, hi):
    return max(abs(lo), abs(hi))


def floor_box(a0, a1, b0, b1, nu, n=600, N=100):
    a0, a1, b0, b1 = Fr(a0), Fr(a1), Fr(b0), Fr(b1)
    if 2 * b0 + nu * a0 - 1 >= 3:
        return {"status": "invalid", "why": "iii"}
    Ga, Gb, invalid = iout_grad(a0, a1, b0, b1, nu, n)
    if invalid:
        return {"status": "invalid", "why": "saturation"}
    am, bm = (a0 + a1) / 2, (b0 + b1) / 2
    Iex = PkgT(S7, nu, am, bm).I_out()
    _, sig, _ = PA.lb_opt(nu, am, bm)
    sig = sorted(sig, key=lambda r: r[1] - r[0])
    assert sum(c for _, _, c in sig) == bm
    Ic = L.I_rho(sig)
    Whi = BX.intV_upper(nu, am, sig, N)
    Wlo = intV_lower(nu, am, sig, N)
    Am, Bm = ivq(am), ivq(bm)
    S_m = 2 * Bm * BX.C1 + 2 * nu * Bm * Am * GL + 3 * Bm * Bm - 2 * Bm * Bm * iv.log(2 * Bm) + iv.mpf(Ic.lo) - iv.mpf(Whi.hi)
    f_m = ivq(Iex) - iv.mpf(5) / 144 + S_m
    # gradient of S over the box
    A, B = I(a0, a1), I(b0, b1)
    t = B / Bm
    Usum = iv.mpf(0)
    for comp in sig:
        Ui = iv.mpf([U_arcsine(comp, a0).lo, U_arcsine(comp, a1).hi])
        Usum = Usum + ivq(comp[2]) * Ui
    Da = 2 * nu * B * GL + t * nu * Usum
    Wbox = iv.mpf([Wlo.lo, Whi.hi]) - nu * (A - Am) * Usum
    Db = 2 * BX.C1 + 2 * nu * A * GL + 4 * B - 4 * B * iv.log(2 * B) + 2 * t * Ic / Bm - Wbox / Bm
    Xa = iv.mpf([ivq(Ga[0]).lo, ivq(Ga[1]).hi]) + Da
    Xb = iv.mpf([ivq(Gb[0]).lo, ivq(Gb[1]).hi]) + Db
    da, db = ivq(a1 - a0), ivq(b1 - b0)
    lo = f_m - da / 2 * absmax(Xa.lo, Xa.hi) - db / 2 * absmax(Xb.lo, Xb.hi)
    return {"status": "certified" if lo.lo > 0 else "open", "floor_lo": float(lo.lo), "f_m": float(f_m.lo),
            "grad_a": [float(Xa.lo), float(Xa.hi)], "grad_b": [float(Xb.lo), float(Xb.hi)],
            "Iout_m": float(Iex), "Ga": [float(Ga[0]), float(Ga[1])], "Da": [float(Da.lo), float(Da.hi)]}
