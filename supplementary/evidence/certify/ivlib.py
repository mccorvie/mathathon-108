"""ivlib.py -- rigorous interval primitives for evidence/certify (problem #108).

EVENT WORK, experimenter:Claude Opus 5.5, Fri Nov 13 2026 (started 23:41 PT).

Every function returns an mpmath.iv interval that CONTAINS the exact real value.
  * Arithmetic, sqrt, log, cos, pi: mpmath.iv (outward-rounded), working precision PREC = 113 bits.
  * Rationals enter through ivq(): numerator/denominator rounded floor/ceiling by mpmath.libmp.from_rational.
  * atan (mpmath.iv has none): argument reduction atan z = 2 atan(z / (1 + sqrt(1 + z^2))) twice, then the
    alternating Taylor series with its remainder bound |atan y - S_n(y)| <= |y|^(2n+1)/(2n+1) (|y| <= 1),
    all in iv arithmetic; for z > 1, atan z = pi/2 - atan(1/z).  So no non-iv function value is used.
Point arguments are mpmath mpf numbers with at most PREC bits (exactly representable in iv).
"""
from fractions import Fraction as Fr

import mpmath
from mpmath import iv, libmp

PREC = 113
iv.prec = PREC
mpmath.mp.prec = PREC
mpf = mpmath.mpf
_mk = mpmath.mp.make_mpf
# exact mpf endpoints of an interval (X.a / X.b in mpmath.iv return degenerate intervals, not numbers)
mpmath.ctx_iv.ivmpf.lo = property(lambda self: _mk(self._mpi_[0]))
mpmath.ctx_iv.ivmpf.hi = property(lambda self: _mk(self._mpi_[1]))


def ivq(q):
    """interval enclosure of a rational number."""
    q = Fr(q)
    lo = _mk(libmp.from_rational(q.numerator, q.denominator, PREC, libmp.round_floor))
    hi = _mk(libmp.from_rational(q.numerator, q.denominator, PREC, libmp.round_ceiling))
    return iv.mpf([lo, hi])


def q_down(q):
    q = Fr(q)
    return _mk(libmp.from_rational(q.numerator, q.denominator, PREC, libmp.round_floor))


def q_up(q):
    q = Fr(q)
    return _mk(libmp.from_rational(q.numerator, q.denominator, PREC, libmp.round_ceiling))


def to_fr(p):
    """exact Fraction of an mpf."""
    sign, m, e, _ = mpf(p)._mpf_          # raw (sign, mantissa, exponent, bitcount); man_exp drops the sign
    v = Fr(m) * (Fr(2) ** e if e >= 0 else Fr(1, 2 ** (-e)))
    return -v if sign else v


def pt(p):
    """point interval of an mpf (exact at PREC bits; checked)."""
    X = iv.mpf(p)
    assert X.lo == X.hi == p, "point not exactly representable"
    return X


def nonneg(X):
    """intersect with [0, oo) (used only where the exact value is known to be >= 0)."""
    a, b = X.lo, X.hi
    return iv.mpf([a if a > 0 else mpf(0), b if b > 0 else mpf(0)])


def _atan_series(Y, n=30):
    Y2 = Y * Y
    S = iv.mpf(0)
    term = Y
    for k in range(n):
        if k % 2 == 0:
            S = S + term / (2 * k + 1)
        else:
            S = S - term / (2 * k + 1)
        term = term * Y2
    yb = max(abs(Y.lo), abs(Y.hi))
    r = (iv.mpf(yb) ** (2 * n + 1)) / (2 * n + 1)
    assert yb <= 0.25
    return S + iv.mpf([-r.hi, r.hi])


def _atan_red(Z):
    """atan on an interval Z subset [0, 1 + tiny]."""
    Z1 = Z / (1 + iv.sqrt(1 + Z * Z))
    Z2 = Z1 / (1 + iv.sqrt(1 + Z1 * Z1))
    return 4 * _atan_series(Z2)


def _atan_point(p):
    P = pt(p)
    if p > 1:
        return iv.pi / 2 - _atan_red(1 / P)
    return _atan_red(P)


def atan_iv(X):
    """enclosure of atan over the interval X (X.lo >= 0); atan is increasing."""
    assert X.lo >= 0
    lo = _atan_point(X.lo).lo
    hi = _atan_point(X.hi).hi
    return iv.mpf([lo, hi])


# ---------------- J_a(t) = int_0^a log(t + u^2) du  (Lai (88)-(89)) ----------------
def J_point(a, p):
    """a: Fraction > 0, p: mpf >= 0."""
    A = ivq(a)
    if p == 0:
        return 2 * A * (iv.log(A) - 1)
    P = pt(p)
    S = iv.sqrt(P)
    return A * iv.log(P + A * A) - 2 * A + 2 * S * atan_iv(A / S)


def Jd_point(a, p):
    """J_a'(t) = int_0^a du/(t+u^2) = atan(a/sqrt t)/sqrt t; None (= +oo) at t = 0."""
    if p == 0:
        return None
    A = ivq(a)
    S = iv.sqrt(pt(p))
    return atan_iv(A / S) / S


def J_enc(a, T):
    """J_a is increasing in t: enclosure over the interval T (T.lo >= 0)."""
    return iv.mpf([J_point(a, T.lo).lo, J_point(a, T.hi).hi])


def Vinc_point(p):
    """V_inc(t) = 2 pi sqrt t + J_1(t) (increasing, concave)."""
    return 2 * iv.pi * iv.sqrt(pt(p)) + J_point(Fr(1), p)


def Vinc_enc(T):
    return iv.mpf([Vinc_point(T.lo).lo, Vinc_point(T.hi).hi])


def Cstar(nu, al=Fr(3, 40), lam=Fr(37, 40)):
    """C*(nu) = -2 lam + 2 nu al lam (1 - log al) + 3 lam^2 - 2 lam^2 log(2 lam)  (theta.py; Lai p. 15)."""
    A, L = ivq(al), ivq(lam)
    return -2 * L + 2 * nu * A * L * (1 - iv.log(A)) + 3 * L * L - 2 * L * L * iv.log(2 * L)


def I_rho(rho):
    """Lai (91): I(rho) = sum_j (S_j^2 - S_{j-1}^2) log((b_j - a_j)/4), rho NESTED and listed inner -> outer
    (checked exactly here).  rho: list of (a, b, c) Fractions."""
    for (a0, b0, _), (a1, b1, _) in zip(rho, rho[1:]):
        assert a1 <= a0 and b0 <= b1, "measure components are not nested inner -> outer"
    S0, tot = Fr(0), iv.mpf(0)
    for a, b, c in rho:
        S1 = S0 + c
        tot = tot + ivq(S1 * S1 - S0 * S0) * iv.log(ivq((b - a) / 4))
        S0 = S1
    return tot
