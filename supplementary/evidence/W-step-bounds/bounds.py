"""Closed-form two-sided bound on the package s-step (derivation in STEP_BOUND.md).
   lower(s) = 2b/3 + 2*Pi(a) - (J_s - J_{s+2}),  Pi(a) = 2/9 - a + a^2/3
   upper    = 2b/3 + 4/9
   uniform  = 2*Pi(a) = 4/9 - 2a + 2a^2/3  (>= 7/54 for a <= 1/6)
   J_s = int_{1/3}^1 min(b, (A - r_s y)_+) dy,  A = 2b - 1 + nu*a,  r_s = (s-1)/2."""
from fractions import Fraction as Fr

def Pi(al):
    al = Fr(al)
    return Fr(2, 9) - al + al * al / 3

def J(s, nu, al, be):
    """exact int_{1/3}^{1} min(be, (A - r y)_+) dy"""
    al, be = Fr(al), Fr(be)
    A = 2 * be - 1 + nu * al
    r = Fr(s - 1, 2)
    lo, hi = Fr(1, 3), Fr(1)
    y1 = (A - be) / r          # A - r y = be
    y0 = A / r                 # A - r y = 0
    tot = Fr(0)
    # piece 1: y in [lo, min(hi, y1)] -> integrand be
    a1, b1 = lo, min(hi, y1)
    if b1 > a1:
        tot += be * (b1 - a1)
    # piece 2: y in [max(lo, y1), min(hi, y0)] -> A - r y
    a2, b2 = max(lo, y1), min(hi, y0)
    if b2 > a2:
        tot += A * (b2 - a2) - r * (b2 * b2 - a2 * a2) / 2
    return tot

def lower(s, nu, al, be):
    return 2 * Fr(be) / 3 + 2 * Pi(al) - (J(s, nu, al, be) - J(s + 2, nu, al, be))

def upper(be):
    return 2 * Fr(be) / 3 + Fr(4, 9)

def uniform(al):
    return 2 * Pi(al)

def laneW(s, nu, al, be):
    al, be = Fr(al), Fr(be)
    A = 2 * be - 1 + nu * al
    t = max(Fr(0), A - Fr(s - 1, 6))
    return 2 * be / 3 - t * t / (s - 1)
