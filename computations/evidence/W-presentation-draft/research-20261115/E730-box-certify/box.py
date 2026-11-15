#!/usr/bin/env python3
"""[108/N E730] Interval lower bound of the zeta(7) dual floor A*(7) + LB over a BOX of (alpha, beta), fixed nu.

EVENT WORK, lane N (Claude Opus 5.5). Reads the team's code read-only: ../../../scope_alpha_beta/pkg_ab.py (the package:
Tout's formula, lb_opt) and ../../../certify/{ivlib,run}.py (113-bit mpmath intervals, J_iv, Vinc_iv, I_rho, Cstar),
exactly as scope_alpha_beta/certify_min.py does. Labels: the bound is COMPUTED with interval arithmetic; the three
reductions below are PROOF-DRAFT (README.md).

  floor7(alpha, beta) = A*(7) + LB,   A* = I_out + int_3^oo R x^-3 dx  (derivation_beta.md Theorem 3', E716 reviewed).

  (1) R = x F + Q (Prop. 1', reviewed in E716), F = 6 beta + 2 beta {x} - 2 nu beta {alpha x} at s = 7, hence
      int_3^oo F/x^2 = 2 beta + 2 beta c1 - 2 nu beta g(alpha),  c1 = int_3^oo {x}/x^2 = 1 - gamma - ln 3 + 5/6,
      g(alpha) = int_3^oo {alpha x}/x^2 = alpha (1 - gamma - ln 3 alpha)  (u = alpha x; valid for 3 alpha < 1).
      g is increasing on [0, 1/6] (g' = -gamma - ln 3 alpha > 0 for alpha < e^-gamma / 3).
  (2) Q >= -5/8 for all x (first bracket >= -1/8; (nu/2)^2 B^2 - (nu/2) A B = ((nu/2)B - A/2)^2 - A^2/4 and |A| <= 2), so
      int_3^oo Q/x^3 >= -5/144.
  (3) I_out = int_{1/3}^{max(1, 2 beta)} T_out(y) dy >= sum over y-cells of width * (interval lower bound of T_out on the
      cell x box), T_out mirrored from pkg_ab.PkgAB.Tout/outer_parts (checked against it at points: test.py).
  LB: sigma_c = lb_opt(nu, alpha_c, beta_c) of mass beta_c, rescaled to sigma_beta = (beta/beta_c) sigma_c (mass beta, as
      Lemma 2' requires). LB(sigma_beta) = (beta/beta_c)^2 I(sigma_c) - (beta/beta_c) int V_{nu,alpha} d sigma_c + C*(nu,alpha,beta).
      V_{nu,alpha} = V_0 - nu J(alpha, t) with dJ/dalpha = ln(t + alpha^2) < 0 when t + alpha^2 < 1, so on the box
      int V d sigma_c <= int V_{nu,alpha1} d sigma_c, bounded above by certify_min.lb_cert's rigorous quadrature at alpha1.
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
EVID = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(EVID, "scope_alpha_beta"))
sys.path.insert(0, os.path.join(EVID, "certify"))
import pkg_ab as PA  # noqa: E402
import ivlib as L    # noqa: E402  (iv.prec = 113)
from ivlib import iv, ivq  # noqa: E402
import run as CR     # noqa: E402

S = 7


def I(lo, hi=None):
    """Interval from rationals or floats (endpoints rounded outward by ivq)."""
    if hi is None:
        hi = lo
    a, b = ivq(Fr(lo)), ivq(Fr(hi))
    return iv.mpf([a.lo, b.hi])


def imax0(X):
    return iv.mpf([max(X.lo, 0), max(X.hi, 0)])


def imin(X, Y):
    return iv.mpf([min(X.lo, Y.lo), min(X.hi, Y.hi)])


def imax(X, Y):
    return iv.mpf([max(X.lo, Y.lo), max(X.hi, Y.hi)])


def c1_fun(l, nu):
    return sum(max(0, l + S - 1 - nu - 2 * i) for i in range(l - 2))


def z1_fun(l, nu):
    return 1 + sum(1 for i in range(l - 2) if l + S - 1 - nu - 2 * i <= 0)


def tout_cell(y0, y1, A, B, nu):
    """Enclosure of T_out(y) for y in [y0, y1] (inside one of (1/3, 1/2], (1/2, 1], (1, oo)), alpha in A, beta in B.
    Returns (T, zz) intervals; zz is None for y > 1."""
    Y = I(y0, y1)
    k = 2 if y1 <= Fr(1, 2) else (1 if y1 <= 1 else 0)
    zz = None
    g = iv.mpf(0)
    if k >= 1:
        lam = 1 - A
        v = 1 - k * Y
        u = imax0(A + v - Y)
        mv = imin(A, v)
        dens = {2 * k: A - mv, 2 * k + 1: mv - u, 2 * k + 2: u}
        cost = (S + 2) * ((1 - Y) - sum(dn * (l - 2) for l, dn in dens.items())) + \
            sum(dn * c1_fun(l, nu) for l, dn in dens.items())
        zz = (Y - 2 * A) + sum(dn * z1_fun(l, nu) for l, dn in dens.items()) + (B - lam)
        rank = 2 * B - 1 + nu * A
        r = imin(B, imax0(rank - iv.mpf(S - 1) / 2 * Y))
        g = cost + imin(r, imax0(zz))   # = cost + min(r, zz) wherever zz >= 0, i.e. on the derived region (saturation)
    jmax = int(2 * float(B.hi) / float(Y.lo)) + 3
    scal = -2 * B * k + sum((imax0(2 * B - j * Y) for j in range(1, jmax + 1)), iv.mpf(0))
    return g + scal, zz


def iout_lower(A, B, nu, n=600):
    """Lower bound of I_out over the box, and a flag 'invalid' if saturation fails at every point of the box."""
    top = max(Fr(1), 2 * to_fr_up(B))
    cuts = [Fr(1, 3), Fr(1, 2), Fr(1)] + ([top] if top > 1 else [])
    total = iv.mpf(0)
    invalid = False
    for lo, hi in zip(cuts, cuts[1:]):
        m = max(4, int(n * (hi - lo)))
        for i in range(m):
            y0, y1 = lo + (hi - lo) * Fr(i, m), lo + (hi - lo) * Fr(i + 1, m)
            T, zz = tout_cell(y0, y1, A, B, nu)
            total = total + I(y1 - y0) * iv.mpf(T.lo)
            if zz is not None and zz.hi < 0:
                invalid = True
    return total, invalid


def to_fr_up(X):
    return L.to_fr(X.hi)


GAMMA = iv.euler
C1 = 1 - GAMMA - iv.log(3) + iv.mpf(5) / 6


def g_alpha(a):
    """g(alpha) = alpha (1 - gamma - ln 3 alpha) at a rational alpha >= 0 (g(0) = 0)."""
    if a == 0:
        return iv.mpf(0)
    A = ivq(Fr(a))
    return A * (1 - GAMMA - iv.log(3 * A))


def fpart_lower(a0, a1, B, nu):
    """Lower bound of 2 beta + 2 beta c1 - 2 nu beta g(alpha) on the box (g increasing: worst at a1; linear in beta)."""
    kappa = 2 + 2 * C1 - 2 * nu * g_alpha(a1)
    return B * kappa


def astar_lower(a0, a1, b0, b1, nu, n=600):
    A, B = I(a0, a1), I(b0, b1)
    io, invalid = iout_lower(A, B, nu, n)
    return (io + fpart_lower(a0, a1, B, nu) - iv.mpf(5) / 144).lo, invalid, float(io.lo)


def intV_upper(nu, al, sig, N=100):
    """Rigorous upper bound of int V_{nu,al} d sigma: the intV loop of scope_alpha_beta/certify_min.lb_cert, verbatim."""
    dth = iv.pi / N
    C = [iv.cos(iv.pi * k / N) for k in range(N + 1)]
    Sn = [iv.sin(iv.pi * k / N) for k in range(N + 1)]
    C[0], Sn[0], C[N], Sn[N] = iv.mpf(1), iv.mpf(0), iv.mpf(-1), iv.mpf(0)
    cbar = [(Sn[k + 1] - Sn[k]) / dth for k in range(N)]
    mu = [(cbar[k] - C[k + 1]) / (C[k] - C[k + 1]) for k in range(N)]
    intV = iv.mpf(0)
    for a, b, c in sig:
        m, h = ivq((a + b) / 2), ivq((b - a) / 2)
        tk = [L.nonneg(m + h * C[k]) for k in range(N + 1)]
        psi = [-nu * CR.J_iv(Fr(al), T) for T in tk]
        inc = iv.mpf(0)
        dec = iv.mpf(0)
        for k in range(N):
            inc = inc + CR.Vinc_iv(L.nonneg(m + h * cbar[k]))
            dec = dec + mu[k] * psi[k] + (1 - mu[k]) * psi[k + 1]
        intV = intV + ivq(c) * (inc + dec) / N
    return intV


def cstar_box(nu, a0, a1, B):
    """C*(nu, alpha, beta) = -2b + 2 nu a b (1 - ln a) + 3 b^2 - 2 b^2 ln(2b); a(1 - ln a) is increasing on [0, 1]."""
    h = lambda a: iv.mpf(0) if a == 0 else ivq(Fr(a)) * (1 - iv.log(ivq(Fr(a))))
    H = iv.mpf([h(a0).lo, h(a1).hi])
    return -2 * B + 2 * nu * H * B + 3 * B * B - 2 * B * B * iv.log(2 * B)


def lb_lower(a0, a1, b0, b1, nu, N=100):
    ac, bc = (a0 + a1) / 2, (b0 + b1) / 2
    _, sig, _ = PA.lb_opt(nu, ac, bc)
    sig = sorted(sig, key=lambda r: r[1] - r[0])
    assert sum(c for _, _, c in sig) == Fr(bc)
    smax = max(b for _, b, _ in sig)
    assert smax + Fr(a1) ** 2 < 1, "monotonicity of J in alpha needs sup supp(sigma) + alpha1^2 < 1"
    Ic = L.I_rho(sig)
    Uc = intV_upper(nu, a1, sig, N)
    B = I(b0, b1)
    t = B / ivq(bc)
    val = t * t * iv.mpf(Ic.lo) - t * iv.mpf(Uc.hi) + cstar_box(nu, a0, a1, B)
    return val.lo


def floor_lower(a0, a1, b0, b1, nu, n=600, N=100):
    """Returns dict: lower bound of floor7 on the box [a0,a1] x [b0,b1] (rationals), or invalid=True."""
    a0, a1, b0, b1 = Fr(a0), Fr(a1), Fr(b0), Fr(b1)
    if 2 * b0 + nu * a0 - 1 >= 3:           # condition (iii) 2 beta + nu alpha - 1 < r_s = 3 fails on the whole box
        return {"invalid": "iii"}
    Alo, invalid, io = astar_lower(a0, a1, b0, b1, nu, n)
    if invalid:
        return {"invalid": "saturation"}
    LBlo = lb_lower(a0, a1, b0, b1, nu, N)
    return {"invalid": False, "A_lo": float(Alo), "LB_lo": float(LBlo), "floor_lo": float(Alo + LBlo), "Iout_lo": io}
