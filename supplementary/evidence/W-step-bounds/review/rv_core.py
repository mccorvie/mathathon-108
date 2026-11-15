#!/usr/bin/env python3
"""rv_core.py -- independent re-implementation (skeptic review, Claude Opus 5.5, same model family as the author).

Written from the formulas of ../../scope_alpha_beta/derivation_beta.md section 3 (outer function T_out, r_hat_beta,
z_beta = z_lambda + beta - lambda), NOT from ../bounds.py or the W-step-bounds check scripts (not imported, not read for
code).  Everything is exact (fractions.Fraction).  The outer function is evaluated with an explicit k = floor(1/y) so that
one-sided limits at the kinks 1/3 and 1/2 can be taken by passing the k of the adjacent open piece.

Objects (y in (1/3, 1], k = floor(1/y)):
  v = 1 - k y,  m = min(alpha, v),  u = max(0, alpha + v - y)
  densities  d(2k) = alpha - m,  d(2k+1) = m - u,  d(2k+2) = u
  c_s(l)  = sum_{i=0}^{l-3} max(0, l + s - 1 - nu - 2i)
  z1_s(l) = 1 + #{ i in 0..l-3 : l + s - 1 - nu - 2i <= 0 }
  P(y)    = (1 - y) - sum_l d(l)(l - 2)
  g_s(y)  = (s+2) P + sum_l d(l) c_s(l) + min(rhat_s, z_s)            (T_out minus its s-free normaliser terms)
  z_s(y)  = y - 2 alpha + sum_l d(l) z1_s(l) + beta - (1 - alpha)
  rhat_s  = min(beta, max(0, A - r_s y)),  A = 2 beta - 1 + nu alpha,  r_s = (s - 1)/2
"""
import math
from fractions import Fraction as Fr

THIRD, HALF, ONE = Fr(1, 3), Fr(1, 2), Fr(1)


def kof(y):
    return math.floor(1 / y)


def dens(al, y, k):
    v = 1 - k * y
    m = min(al, v)
    u = max(Fr(0), al + v - y)
    return {2 * k: al - m, 2 * k + 1: m - u, 2 * k + 2: u}


def c_s(s, nu, l):
    return sum((max(0, l + s - 1 - nu - 2 * i) for i in range(l - 2)), 0)


def z1_s(s, nu, l):
    return 1 + sum(1 for i in range(l - 2) if l + s - 1 - nu - 2 * i <= 0)


class Out:
    """outer pieces at fixed (s, nu, alpha, beta)."""

    def __init__(self, s, nu, al, be):
        self.s, self.nu, self.al, self.be = s, nu, Fr(al), Fr(be)
        self.A = 2 * self.be - 1 + nu * self.al
        self.r = Fr(s - 1, 2)

    def P(self, y, k):
        d = dens(self.al, y, k)
        return (1 - y) - sum(dn * (l - 2) for l, dn in d.items())

    def cost(self, y, k):
        d = dens(self.al, y, k)
        return (self.s + 2) * self.P(y, k) + sum(dn * c_s(self.s, self.nu, l) for l, dn in d.items())

    def z(self, y, k):
        d = dens(self.al, y, k)
        return y - 2 * self.al + sum(dn * z1_s(self.s, self.nu, l) for l, dn in d.items()) + self.be - (1 - self.al)

    def rhat(self, y):
        return min(self.be, max(Fr(0), self.A - self.r * y))

    def g(self, y, k):
        return self.cost(y, k) + min(self.rhat(y), self.z(y, k))


def zmin(o):
    """inf of z_s over (1/3, 1] (= min over the closure, z is continuous and piecewise affine with the kinks below)."""
    al = o.al
    pts = sorted({THIRD, HALF, ONE, 1 - al, (1 - al) / 2, (1 + al) / 2, (1 + al) / 3})
    pts = [p for p in pts if THIRD <= p <= 1]
    vals = []
    for l, r in zip(pts, pts[1:]):
        k = kof((l + r) / 2)
        vals += [o.z(l, k), o.z(r, k)]
    return min(vals)


def base_kinks(al, rank_lines):
    pts = {THIRD, HALF, ONE}
    for k in (1, 2):
        pts |= {(1 - al) / k, (1 + al) / (k + 1)}
    for A, r, be in rank_lines:
        if r > 0:
            pts |= {(A - be) / r, A / r}
    return sorted(p for p in pts if THIRD <= p <= 1)


def add_crossings(pts, pairs):
    """pairs: list of (f, h) with f(y), h(y, k) affine on each current piece; add the points where f = h."""
    extra = set()
    for l, r in zip(pts, pts[1:]):
        k = kof((l + r) / 2)
        for f, h in pairs:
            a, b = f(l) - h(l, k), f(r) - h(r, k)
            if (a > 0 > b) or (a < 0 < b):
                extra.add(l + (r - l) * a / (a - b))
    return sorted(set(pts) | extra)


def integrate(F, pts):
    """exact integral of F(y, k) over [pts[0], pts[-1]], F affine on every piece (asserted at three interior points)."""
    tot = Fr(0)
    for l, r in zip(pts, pts[1:]):
        if r <= l:
            continue
        k = kof((l + r) / 2)
        fl_, fr_ = F(l, k), F(r, k)
        for t in (Fr(1, 3), Fr(1, 2), Fr(5, 7)):
            y = l + (r - l) * t
            if F(y, k) != fl_ + (fr_ - fl_) * t:
                raise AssertionError(f"not affine on [{l}, {r}] at {y}")
        tot += (r - l) * (fl_ + fr_) / 2
    return tot


def step_outer(s, nu, al, be):
    """exact int_{1/3}^{1} [g_{s+2} - g_s] dy, own breakpoints and crossings."""
    o0, o2 = Out(s, nu, al, be), Out(s + 2, nu, al, be)
    pts = base_kinks(Fr(al), [(o0.A, o0.r, o0.be), (o2.A, o2.r, o2.be)])
    pts = add_crossings(pts, [(o0.rhat, o0.z), (o2.rhat, o2.z)])
    return integrate(lambda y, k: o2.g(y, k) - o0.g(y, k), pts)


def int_P(al):
    o = Out(5, 0, al, 1)
    pts = base_kinks(Fr(al), [])
    return integrate(lambda y, k: o.P(y, k), pts)


def J(s, nu, al, be):
    o = Out(s, nu, al, be)
    pts = base_kinks(Fr(al), [(o.A, o.r, o.be)])
    return integrate(lambda y, k: o.rhat(y), pts)


def J_closed(s, nu, al, be):
    """J_s = int_{1/3}^1 min(beta, (A - r y)_+) dy in closed form (independent of the integrator above)."""
    be = Fr(be)
    A, r = 2 * be - 1 + nu * Fr(al), Fr(s - 1, 2)
    # antiderivative of min(be, (A - r y)_+) on [a, b]
    y1, y0 = (A - be) / r, A / r          # clamp ends at y1, zero from y0 on
    lo, hi = THIRD, ONE
    tot = Fr(0)
    # clamp part on [lo, min(hi, y1)]
    c_hi = min(hi, y1)
    if c_hi > lo:
        tot += be * (c_hi - lo)
    # linear part on [max(lo, y1), min(hi, y0)]
    a, b = max(lo, y1), min(hi, y0)
    if b > a:
        tot += A * (b - a) - r * (b * b - a * a) / 2
    return tot


def lower(s, nu, al, be):
    al, be = Fr(al), Fr(be)
    return 2 * be / 3 + Fr(4, 9) - 2 * al + Fr(2, 3) * al ** 2 - (J_closed(s, nu, al, be) - J_closed(s + 2, nu, al, be))


def upper(be):
    return 2 * Fr(be) / 3 + Fr(4, 9)


def in_domain(s, nu, al, be):
    """README domain: 0 <= alpha < 1/6, beta > 0, integer nu >= 0, (iii) A < r_s, saturation at s and s+2."""
    al, be = Fr(al), Fr(be)
    o0, o2 = Out(s, nu, al, be), Out(s + 2, nu, al, be)
    why = []
    if not (0 <= al < Fr(1, 6)):
        why.append("alpha")
    if not be > 0:
        why.append("beta")
    if not o0.A < o0.r:
        why.append("(iii)")
    z0, z2 = zmin(o0), zmin(o2)
    if z0 < 0:
        why.append("sat_s")
    if z2 < 0:
        why.append("sat_s+2")
    return (not why), why, z0, z2
