#!/usr/bin/env python3
"""Reviewer's own continuum window allocation (exact rationals), written from Fauzan's (4.2)-(4.8) and the proof of
Prop. 4.1, not from E732's window.py, E733's check_window3.feasible or the E732 reviewer's my_window.py.

reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)

Classes z = a/p in (0, 1/2), measure dz. l_K(z) = floor(x - z) + floor(x + z) + 1, l_N(z) = same with alpha x,
b = (nu/2) l_N, c = b - l_K/2, Y = Z - l_K/2 = L + c, L >= 0 <=> Y >= c, Y in c + Z (L integer).
Row total: int Z dz = H_L x - shift (shift >= 0 models the finite-K shortfall; shift = 0 is the most generous).
Window rule (Prop. 4.1, ordinary foreign source): all Y in one interval [w, w + 1].

Feasibility (with L >= 0) is decided WITHOUT the greedy/forced-base construction: for each candidate w in (1/2)Z (only those
matter, since every c is in (1/2)Z), class z may take any Y in S_z(w) = (c_z + Z) cap [max(w, c_z), w + 1]; in the continuum
the attainable int Y dz is then the whole interval [int min S, int max S] (measures can be split), so the point is feasible
iff some w has every S_z(w) nonempty and int min S <= target <= int max S.

valid_all(...) decides feasibility for EVERY x in [3, X_hi] exactly: on each x-interval with a fixed class structure the
piece measures and the target are affine in x, so every condition is an affine sign condition; its zeros are added as
breakpoints and feasibility is evaluated at every breakpoint and every sub-interval midpoint. Beyond X_hi = max(8,
(nu + 4)/(4 beta) + 1) the window allocation has L >= 2 beta x - nu/2 - 3/2 - 2 shift > 0 (any window allocation:
Y >= mean(Y) - 1, c <= nu alpha x + nu/2 - x + 1/2, mean(Y) = 2 beta x + nu alpha x - x - 2 shift).
"""
import math
from fractions import Fraction as Fr

HALF = Fr(1, 2)


def fl(q):
    return math.floor(q)


def frc(q):
    return q - fl(q)


def lcnt(y, z):
    return fl(y - z) + fl(y + z) + 1


def pieces(x, al, nu):
    cuts = {Fr(0), HALF}
    for y in (x, al * x):
        f = frc(y)
        for q in (f, 1 - f):
            if 0 < q < HALF:
                cuts.add(q)
    cuts = sorted(cuts)
    out = []
    for z0, z1 in zip(cuts, cuts[1:]):
        zm = (z0 + z1) / 2
        lK, lN = lcnt(x, zm), lcnt(al * x, zm)
        b = Fr(nu, 2) * lN
        out.append((z1 - z0, lK, lN, b, b - Fr(lK, 2)))
    return out


def target_of(x, al, be, nu, P, shift):
    HL = be + Fr(nu, 2) * al
    return HL * x - shift - sum(mu * Fr(lK, 2) for mu, lK, _, _, _ in P)


def sets(P, w, Lpos=True):
    """per piece (ymin, ymax) of S(w), or None if some S is empty."""
    out = []
    for mu, lK, lN, b, c in P:
        lo = max(w, c) if Lpos else w
        ymin = c + math.ceil(lo - c)
        ymax = c + fl(w + 1 - c)
        if ymin > ymax:
            return None
        out.append((ymin, ymax))
    return out


def wcands(tgt):
    m = 2 * tgt                      # mean of Y (total measure 1/2)
    return [Fr(k, 2) for k in range(fl(2 * (m - 1)) - 1, math.ceil(2 * m) + 2)]


def feasible_at(x, al, be, nu, shift=Fr(0)):
    x, al, be = Fr(x), Fr(al), Fr(be)
    P = pieces(x, al, nu)
    tgt = target_of(x, al, be, nu, P, shift)
    for w in wcands(tgt):
        S = sets(P, w)
        if S is None:
            continue
        lo = sum(mu * s[0] for (mu, *_), s in zip(P, S))
        hi = sum(mu * s[1] for (mu, *_), s in zip(P, S))
        if lo <= tgt <= hi:
            return True
    return False


def window_cost(x, al, be, nu, s=7, shift=Fr(0)):
    """Gamma of the window allocation WITHOUT the L >= 0 constraint (the Y-distribution is unique; the up-measure is assigned
    in piece order, deliberately not greedy), computed directly as sum mu * L (L + 2b - l_K - s)."""
    x, al, be = Fr(x), Fr(al), Fr(be)
    P = pieces(x, al, nu)
    tgt = target_of(x, al, be, nu, P, shift)
    for w in wcands(tgt):
        S = sets(P, w, Lpos=False)
        lo = sum(mu * sm[0] for (mu, *_), sm in zip(P, S))
        hi = sum(mu * sm[1] for (mu, *_), sm in zip(P, S))
        if lo <= tgt <= hi:
            up = tgt - lo
            g = Fr(0)
            ys = []
            for (mu, lK, lN, b, c), (ymin, ymax) in zip(P, S):
                if ymax > ymin:
                    u = min(up, mu)
                    up -= u
                    parts = [(u, ymax), (mu - u, ymin)]
                else:
                    parts = [(mu, ymin)]
                for m_, Y in parts:
                    if m_ > 0:
                        L = Y - c
                        g += m_ * L * (L + 2 * b - lK - s)
                        ys.append(Y)
            assert up == 0 and max(ys) - min(ys) <= 1
            return g
    raise RuntimeError("no window")


def Jf(u):
    m = fl(2 * u)
    return m * u - Fr(m * (m + 1), 4)


def R_window(x, al, be, nu, s=7):
    x, al, be = Fr(x), Fr(al), Fr(be)
    N = 2 * be * x * fl(x) - 2 * nu * be * x * fl(al * x) - 2 * Jf(be * x)
    return -window_cost(x, al, be, nu, s) - N


def struct_breaks(al, lo, hi):
    pts = {Fr(lo), Fr(hi)}
    for c in (Fr(2), 2 * al, 1 - al, 1 + al):
        if c <= 0:
            continue
        k = fl(lo * c)
        while Fr(k) / c <= hi:
            v = Fr(k) / c
            if lo < v < hi:
                pts.add(v)
            k += 1
    return sorted(pts)


def X_hi(be, nu, shift=Fr(0)):
    return max(Fr(8), (Fr(nu) + 4 + 8 * shift) / (4 * Fr(be)) + 1)


def valid_all(al, be, nu, shift=Fr(0), xlo=Fr(3), xhi=None, stop=True):
    """(ok, first_bad_x, n_eval): window feasibility at every x in (xlo, xhi], exact (see module doc)."""
    al, be = Fr(al), Fr(be)
    xhi = X_hi(be, nu, shift) if xhi is None else Fr(xhi)
    sb = struct_breaks(al, Fr(xlo), xhi)
    n = 0
    bad = None
    for x0, x1 in zip(sb, sb[1:]):
        t1, t2 = x0 + (x1 - x0) / 3, x0 + 2 * (x1 - x0) / 3
        P1, P2 = pieces(t1, al, nu), pieces(t2, al, nu)
        assert [p[1:] for p in P1] == [p[1:] for p in P2]
        T1, T2 = target_of(t1, al, be, nu, P1, shift), target_of(t2, al, be, nu, P2, shift)
        extra = set()
        # candidate w over the whole sub-interval (mean of Y is affine)
        m0 = 2 * (T1 + (T2 - T1) / (t2 - t1) * (x0 - t1))
        m1 = 2 * (T1 + (T2 - T1) / (t2 - t1) * (x1 - t1))
        ws = set(wcands(min(m0, m1) / 2)) | set(wcands(max(m0, m1) / 2))
        wmin, wmax = min(ws), max(ws)
        k = int(2 * wmin)
        while Fr(k, 2) <= wmax:
            w = Fr(k, 2)
            k += 1
            S = sets(P1, w)
            if S is None:
                continue
            for j in (0, 1):
                g1 = sum(p[0] * s[j] for p, s in zip(P1, S)) - T1
                g2 = sum(p[0] * s[j] for p, s in zip(P2, S)) - T2
                if g1 != g2:
                    xz = t1 - g1 * (t2 - t1) / (g2 - g1)
                    if x0 < xz < x1:
                        extra.add(xz)
        pts = sorted({x0, x1} | extra)
        evals = set(pts) | {(a + b) / 2 for a, b in zip(pts, pts[1:])}
        for x in sorted(evals):
            if x <= xlo:
                continue
            n += 1
            if not feasible_at(x, al, be, nu, shift):
                if bad is None or x < bad:
                    bad = x
                if stop:
                    return False, bad, n
    return bad is None, bad, n
