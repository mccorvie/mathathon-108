#!/usr/bin/env python3
"""rv_exact.py -- skeptic review of ../README.md (tasks 1-3).  Exact rationals throughout.

Ground truth: ../../scope_alpha_beta/pkg_ab.py (imported read-only: PkgAB.R, Tout, outer_parts, I_out, int_R_x3, A_M).
Own code: rv_core.py.  Does not import or read ../bounds.py or the W-step-bounds check scripts.
Usage: python3 -B rv_exact.py [n_random=300] [seed=20261115]   -> prints a log (tee it to rv_exact.out)
"""
import os
import random
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "scope_alpha_beta"))
import pkg_ab as PA  # noqa: E402  (read-only)
import rv_core as C  # noqa: E402

NRAND = int(sys.argv[1]) if len(sys.argv) > 1 else 300
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 20261115
rng = random.Random(SEED)
FAILS = []


def check(name, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILS.append(name)


def rq(lo, hi, den=10 ** 4):
    lo, hi = Fr(lo), Fr(hi)
    a, b = int(lo * den) + 1, int(hi * den) - 1
    return Fr(rng.randint(a, max(a, b)), den)


def pkg_step(s, nu, al, be):
    return 2 * Fr(be) / 3 + PA.PkgAB(s + 2, nu, al, be).I_out() - PA.PkgAB(s, nu, al, be).I_out()


t0 = time.time()
print(f"rv_exact.py  n_random={NRAND} seed={SEED}")

# ---------------------------------------------------------------- A. inner range: Prop. 1' in pkg_ab
print("\nA. Prop. 1' in pkg_ab: R_{s+2}(x) - R_s(x) = 2 beta x, and the M-free step of A_M")
cases = [(3, 0, Fr(0), Fr(9, 10)), (5, 6, Fr(3, 40), Fr(37, 40)), (5, 7, Fr(1, 10), Fr(3, 5)), (7, 21, Fr(1, 100), Fr(13, 10)),
         (9, 45, Fr(1, 60), Fr(2)), (11, 3, Fr(1, 7), Fr(5, 2)), (3, 9, Fr(1, 10), Fr(2, 5)), (7, 10, Fr(1, 6) - Fr(1, 10**6), Fr(1, 2))]
nbad = 0
ntot = 0
for s, nu, al, be in cases:
    P0, P2 = PA.PkgAB(s, nu, al, be), PA.PkgAB(s + 2, nu, al, be)
    for _ in range(40):
        x = rq(3, 400, 997)
        ntot += 1
        if P2.R(x) - P0.R(x) != 2 * be * x:
            nbad += 1
check("R_{s+2} - R_s == 2 beta x exactly", nbad == 0, f"{ntot} points, {len(cases)} parameter sets (incl. alpha=0, odd nu, nu=45)")
nbad = 0
for s, nu, al, be in cases[:4]:
    P0, P2 = PA.PkgAB(s, nu, al, be), PA.PkgAB(s + 2, nu, al, be)
    for M in (Fr(3), Fr(40), Fr(97, 2)):
        try:
            i0, i2 = P0.I_out(), P2.I_out()
        except ValueError:
            continue
        try:
            d = P2.A_M(M, i2, P2.int_R_x3(3, M)) - P0.A_M(M, i0, P0.int_R_x3(3, M))
        except ZeroDivisionError as e:
            print(f"    pkg_ab.int_R_x3 cannot run at alpha = {al} (s={s}, nu={nu}): ZeroDivisionError {e}")
            break
        if d != 2 * be / 3 + i2 - i0:
            nbad += 1
            print("    A_M step mismatch", s, nu, al, be, M, d)
check("A_M(s+2) - A_M(s) == 2 beta/3 + I_out(s+2) - I_out(s) at M = 3, 40, 97/2", nbad == 0)

# ---------------------------------------------------------------- B. outer range y > 1 and the normaliser terms are s-free
print("\nB. pkg_ab Tout on 1 < y <= 2 beta does not depend on s (also where (iii) fails)")
nbad = ntot = 0
for s, nu, al, be in [(3, 0, Fr(0), Fr(9, 10)), (5, 6, Fr(3, 40), Fr(37, 40)), (9, 45, Fr(1, 60), Fr(2)), (11, 3, Fr(1, 7), Fr(5, 2)),
                      (3, 10, Fr(3, 40), Fr(37, 40)), (5, 30, Fr(1, 10), Fr(9, 5))]:
    P0, P2 = PA.PkgAB(s, nu, al, be), PA.PkgAB(s + 2, nu, al, be)
    if 2 * be <= 1:
        continue
    for _ in range(40):
        y = rq(1, 2 * be, 9973)
        ntot += 1
        if P0.Tout(y) != P2.Tout(y):
            nbad += 1
check("Tout_{s+2}(y) == Tout_s(y) for y in (1, 2 beta]", nbad == 0, f"{ntot} points; incl. (3,10,3/40,37/40) and (5,30,1/10,9/5) where (iii) fails")

# ---------------------------------------------------------------- C. own outer function == pkg_ab.outer_parts
print("\nC. own outer function (rv_core.Out) == PkgAB.outer_parts (cost, z, rank) at random y in (1/3, 1]")
nbad = ntot = 0
for _ in range(60):
    s = rng.choice([3, 5, 7, 9, 11, 13])
    nu = rng.randint(0, 40)
    al = rng.choice([Fr(0), rq(0, Fr(1, 6))])
    be = rq(Fr(1, 10), Fr(5, 2))
    P, O = PA.PkgAB(s, nu, al, be), C.Out(s, nu, al, be)
    for _ in range(25):
        y = rq(Fr(1, 3), 1, 99991)
        k = C.kof(y)
        cost, zz, r = P.outer_parts(y)
        ntot += 1
        if (cost, zz, r) != (O.cost(y, k), O.z(y, k), O.rhat(y)):
            nbad += 1
    # also y = 1 and y = 1/2 exactly
    for y in (Fr(1), Fr(1, 2)):
        cost, zz, r = P.outer_parts(y)
        ntot += 1
        if (cost, zz, r) != (O.cost(y, C.kof(y)), O.z(y, C.kof(y)), O.rhat(y)):
            nbad += 1
check("outer pieces identical", nbad == 0, f"{ntot} evaluations")

# ---------------------------------------------------------------- D. per-index facts
print("\nD. per-index facts: delta(m) = (m+2)_+ - (m)_+, e(m) = 1[m in {-1,0}]")
tbl = {m: (max(0, m + 2) - max(0, m), 1 if m in (-1, 0) else 0) for m in range(-30, 31)}
check("e(m) <= delta(m) <= 2 for m in [-30, 30]", all(e <= d <= 2 for d, e in tbl.values()))
check("delta = 2,2,1,0 for m>=1, m=0, m=-1, m<=-2", all(tbl[m][0] == (2 if m >= 0 else 1 if m == -1 else 0) for m in tbl))
# Delta z = sum d sum_i e(m_i) and Delta c = sum_i delta(m_i), directly from the definitions of c_s and z1_s
nbad = 0
for s in range(3, 30, 2):
    for nu in range(0, 50):
        for l in range(2, 9):
            dc = C.c_s(s + 2, nu, l) - C.c_s(s, nu, l)
            dz = C.z1_s(s, nu, l) - C.z1_s(s + 2, nu, l)
            ms = [l + s - 1 - nu - 2 * i for i in range(l - 2)]
            if dc != sum(tbl.get(m, (2 if m > 0 else 0, 0))[0] for m in ms) or dz != sum(1 for m in ms if m in (-1, 0)):
                nbad += 1
            if not (0 <= dz <= dc <= 2 * (l - 2)):
                nbad += 1
check("0 <= Delta z1(l) <= Delta c(l) <= 2(l-2), and the index-sum forms, s=3..29, nu=0..49, l=2..8", nbad == 0)
# min inequality
nbad = 0
for _ in range(20000):
    a2, b2 = Fr(rng.randint(-50, 50), 7), Fr(rng.randint(-50, 50), 7)
    a, b = a2 + Fr(rng.randint(0, 40), 7), b2 + Fr(rng.randint(0, 40), 7)
    dd = min(a, b) - min(a2, b2)
    if not (0 <= dd <= (a - a2) + (b - b2)):
        nbad += 1
check("0 <= min(a,b) - min(a',b') <= (a-a') + (b-b') for a>=a', b>=b' (20000 random)", nbad == 0)
# monotonicity in s of rhat and z (pointwise, own code)
nbad = 0
for _ in range(3000):
    s = rng.choice([3, 5, 7, 9, 11]); nu = rng.randint(0, 40); al = rq(0, Fr(1, 6)); be = rq(Fr(1, 10), Fr(5, 2))
    y = rq(Fr(1, 3), 1, 99991); k = C.kof(y)
    o0, o2 = C.Out(s, nu, al, be), C.Out(s + 2, nu, al, be)
    if not (o2.rhat(y) <= o0.rhat(y) and o2.z(y, k) <= o0.z(y, k)):
        nbad += 1
check("rhat and z nonincreasing in s (3000 random points)", nbad == 0)

# ---------------------------------------------------------------- E. the closed form of int P
print("\nE. int_{1/3}^1 P dy = 2/9 - alpha + alpha^2/3 (own exact piecewise integral)")
rows = []
for al in [Fr(0), Fr(1, 240), Fr(3, 40), Fr(1, 10), Fr(39, 240), Fr(1, 6) - Fr(1, 10 ** 6), Fr(1, 6), Fr(1, 5), Fr(1, 4),
           Fr(3, 10), Fr(1, 3), Fr(17, 50), Fr(2, 5), Fr(1, 2)]:
    v = C.int_P(al)
    cf = Fr(2, 9) - al + al ** 2 / 3
    rows.append((al, v, cf, v == cf))
    print(f"    alpha={str(al):>14}  int P = {str(v):>22}  closed = {str(cf):>22}  {'equal' if v == cf else 'DIFFERENT'}")
check("closed form exact for every tested alpha <= 1/3", all(eq for al, v, cf, eq in rows if al <= Fr(1, 3)))
# the two partial integrals quoted in the README proof
nbad = 0
for al in [Fr(0), Fr(1, 240), Fr(3, 40), Fr(1, 7), Fr(1, 6), Fr(1, 4), Fr(1, 3)]:
    W = lambda y, k, al=al: sum(dn * (l - 2) for l, dn in C.dens(al, y, k).items())  # noqa: E731
    pts = C.base_kinks(al, [])
    hi = C.integrate(W, [p for p in pts if p >= C.HALF])
    lo_ = C.integrate(W, [p for p in pts if p <= C.HALF])
    if hi != al / 2 - al ** 2 / 4 or lo_ != al / 2 - al ** 2 / 12:
        nbad += 1
        print("    partial integral mismatch at alpha", al, hi, lo_)
check("int_{1/2}^1 sum d(l-2) = alpha/2 - alpha^2/4 and int_{1/3}^{1/2} = alpha/2 - alpha^2/12 (7 alphas in [0, 1/3])", nbad == 0)
print("    (for alpha > 1/3 it is expected to fail; the README states validity for 0 <= alpha <= 1/3)")
# densities nonnegative for alpha <= 1/3
nbad = 0
for _ in range(5000):
    al = rq(0, Fr(1, 3)); y = rq(Fr(1, 3), 1, 99991)
    d = C.dens(al, y, C.kof(y))
    if min(d.values()) < 0 or sum(d.values()) != al:
        nbad += 1
check("densities >= 0 and sum to alpha for 0 <= alpha <= 1/3 (5000 random)", nbad == 0)

# ---------------------------------------------------------------- F. uniform floor
print("\nF. uniform floor f(alpha) = 4/9 - 2 alpha + (2/3) alpha^2")
f = lambda a: Fr(4, 9) - 2 * a + Fr(2, 3) * a * a  # noqa: E731
check("f(1/6) == 7/54", f(Fr(1, 6)) == Fr(7, 54), str(f(Fr(1, 6))))
check("f'(alpha) = -2 + (4/3) alpha < 0 on [0, 1/6] (so f > 7/54 on [0, 1/6))", -2 + Fr(4, 3) * Fr(1, 6) < 0)
check("f(0) == 4/9 == int 2(1-y) over (1/3,1]", f(Fr(0)) == Fr(4, 9) == 2 * C.int_P(Fr(0)))

# ---------------------------------------------------------------- G. J closed form and J <= 2 beta/3
print("\nG. J_s: closed form vs own integrator; J_s <= 2 beta/3")
nbad = nbig = 0
for _ in range(600):
    s = rng.choice([3, 5, 7, 9, 11, 13]); nu = rng.randint(0, 40); al = rq(0, Fr(1, 6)); be = rq(Fr(1, 100), Fr(5, 2))
    a, b = C.J(s, nu, al, be), C.J_closed(s, nu, al, be)
    if a != b:
        nbad += 1
    if b > 2 * be / 3 or b < 0:
        nbig += 1
check("J integrator == J closed form (600 random)", nbad == 0)
check("0 <= J_s <= 2 beta/3 (600 random)", nbig == 0)

# ---------------------------------------------------------------- H. edge cases against pkg_ab's exact I_out
print("\nH. edge cases: step = 2beta/3 + I_out(s+2) - I_out(s) from PkgAB (exact) vs own integral; both bounds")


def sat_edge(s, nu, al):
    """beta* with min z_{s+2} = 0 exactly (z is beta + z(beta=0))."""
    return -C.zmin(C.Out(s + 2, nu, al, 0))


def run_point(tag, s, nu, al, be, verbose=True):
    al, be = Fr(al), Fr(be)
    ok_dom, why, z0, z2 = C.in_domain(s, nu, al, be)
    mine = 2 * be / 3 + C.step_outer(s, nu, al, be)
    lo, up = C.lower(s, nu, al, be), C.upper(be)
    try:
        ps = pkg_step(s, nu, al, be)
        perr = None
    except ValueError as e:
        ps, perr = None, str(e)[:60]
    same = (ps == mine) if ps is not None else None
    okb = lo <= mine <= up
    if verbose:
        print(f"  {tag:<34} s={s:<2} nu={nu:<2} a={str(al):<12} b={str(be):<16} dom={'yes' if ok_dom else 'NO ' + ','.join(why):<12}"
              f" zmin(s+2)={float(z2):+.4f}  step={float(mine):.6f}  lo={float(lo):.6f}  up={float(up):.6f}"
              f"  pkg==own:{same}  bounds:{'ok' if okb else 'VIOLATED'}" + (f"  pkg_ab: {perr}" if perr else ""))
    return dict(dom=ok_dom, why=why, same=same, okb=okb, step=mine, lo=lo, up=up, perr=perr)


edge = []
# alpha = 0
edge += [("alpha=0", 3, 0, 0, Fr(9, 10)), ("alpha=0, sat edge beta=2/3", 3, 5, 0, Fr(2, 3)), ("alpha=0", 5, 7, 0, 1),
         ("alpha=0", 7, 30, 0, Fr(3, 2)), ("alpha=0, beta=2", 9, 3, 0, 2), ("alpha=0, beta=2", 11, 0, 0, 2)]
# alpha near 1/6
a1 = Fr(1, 6) - Fr(1, 10 ** 6)
edge += [("alpha=1/6-1e-6", 5, 6, a1, Fr(9, 10)), ("alpha=1/6-1e-6", 7, 10, a1, Fr(1, 2)), ("alpha=39/240", 5, 6, Fr(39, 240), Fr(7, 10)),
         ("alpha=1/6-1e-6", 3, 0, a1, Fr(9, 10)), ("alpha=1/6-1e-6, odd nu", 9, 15, a1, Fr(3, 2))]
# saturation edges (z_{s+2} min = 0 exactly), and just inside
for s, nu, al in [(5, 6, Fr(3, 40)), (5, 8, Fr(11, 80)), (3, 9, Fr(1, 10)), (7, 2, Fr(1, 8)), (5, 0, Fr(1, 20)), (7, 21, Fr(1, 40)),
                  (9, 14, Fr(3, 40)), (11, 30, Fr(1, 50)), (3, 1, Fr(1, 7))]:
    bs = sat_edge(s, nu, al)
    edge += [(f"sat edge s+2 (beta*)", s, nu, al, bs), (f"sat edge + 1e-6", s, nu, al, bs + Fr(1, 10 ** 6))]
    bs0 = -C.zmin(C.Out(s, nu, al, 0))
    if bs0 < bs:
        mid = (bs0 + bs) / 2
        edge += [(f"between sat(s) and sat(s+2)", s, nu, al, mid)]
# large beta (outer integral to 2 beta)
edge += [("large beta", 9, 6, Fr(1, 12), 2), ("large beta", 11, 13, Fr(1, 7), 2), ("large beta", 11, 2, Fr(1, 10), Fr(199, 100)),
         ("beta=12/5 (>2)", 11, 1, Fr(1, 20), Fr(12, 5)), ("beta=5/2", 13, 4, Fr(1, 9), Fr(5, 2)), ("large beta, s=9", 9, 0, Fr(1, 6) - Fr(1, 10**6), Fr(199, 100))]
# A just below r_s
for s, nu, al in [(3, 7, Fr(1, 20)), (5, 4, Fr(1, 10)), (7, 10, Fr(3, 40)), (9, 21, Fr(1, 30)), (11, 1, Fr(1, 6) - Fr(1, 1000))]:
    r = Fr(s - 1, 2)
    be = (r - Fr(1, 1000) + 1 - nu * al) / 2
    edge += [(f"A = r_s - 1/1000", s, nu, al, be)]
    be2 = (r + 1 - nu * al) / 2
    edge += [(f"A = r_s exactly (iii fails)", s, nu, al, be2)]
# large / odd nu
edge += [("odd nu=21", 7, 21, Fr(1, 100), Fr(13, 10)), ("nu=45", 9, 45, Fr(1, 60), Fr(3, 2)), ("nu=31 odd", 11, 31, Fr(1, 31), Fr(2)),
         ("nu=61", 13, 61, Fr(1, 61), Fr(9, 5)), ("nu=1", 3, 1, Fr(1, 7), Fr(1, 2))]
# z-binding with Delta z > 0 (s=3 -> 5, nu = 9)
edge += [("z binds, Delta z > 0", 3, 9, Fr(1, 10), Fr(2, 5)), ("z binds, Delta z > 0", 3, 9, Fr(1, 10), Fr(3, 10)),
         ("z binds", 5, 11, Fr(1, 10), Fr(1, 2)), ("z binds", 7, 13, Fr(1, 12), Fr(3, 4))]
# template rows
edge += [("template", 5, nu, Fr(3, 40), Fr(37, 40)) for nu in (2, 6, 8, 10)]

res_edge = []
for e in edge:
    res_edge.append((e, run_point(*e)))
valid = [(e, r) for e, r in res_edge if r["dom"]]
check(f"edge points in the domain: pkg_ab step == own step ({len(valid)} points)", all(r["same"] for e, r in valid))
check(f"edge points in the domain: lower <= step <= upper ({len(valid)} points)", all(r["okb"] for e, r in valid))
inval = [(e, r) for e, r in res_edge if not r["dom"]]
print(f"  outside the domain ({len(inval)} points): pkg_ab raised at {sum(1 for e, r in inval if r['perr'])}; "
      f"bounds hold for the formula at {sum(1 for e, r in inval if r['okb'])} of {len(inval)}")

# ---------------------------------------------------------------- I. pointwise bounds on PkgAB.outer_parts
print("\nI. pointwise: 2P - (rhat_s - rhat_{s+2}) <= T_{s+2} - T_s <= 2(1-y) on PkgAB.outer_parts (z>=0 not required)")
nlo = nup = ntot = 0
for _ in range(400):
    s = rng.choice([3, 5, 7, 9, 11, 13]); nu = rng.randint(0, 45); al = rng.choice([Fr(0), rq(0, Fr(1, 6))]); be = rq(Fr(1, 100), Fr(5, 2))
    P0, P2, O = PA.PkgAB(s, nu, al, be), PA.PkgAB(s + 2, nu, al, be), C.Out(s, nu, al, be)
    O2 = C.Out(s + 2, nu, al, be)
    for _ in range(25):
        y = rq(Fr(1, 3), 1, 99991)
        c0, z0, r0 = P0.outer_parts(y)
        c2, z2, r2 = P2.outer_parts(y)
        dT = (c2 + min(r2, z2)) - (c0 + min(r0, z0))
        Pv = O.P(y, C.kof(y))
        ntot += 1
        if dT > 2 * (1 - y):
            nup += 1
        if dT < 2 * Pv - (r0 - r2):
            nlo += 1
check("pointwise upper", nup == 0, f"{ntot} points")
check("pointwise lower", nlo == 0, f"{ntot} points")

# ---------------------------------------------------------------- J. random domain points against PkgAB
print(f"\nJ. {NRAND} random points in the README domain (beta biased to the saturation and (iii) edges)")
n = nskip = 0
worst_lo = worst_up = None
ratios = []
nviol = nmis = 0
while n < NRAND:
    s = rng.choice([3, 5, 7, 9, 11])
    nu = rng.randint(0, 40)
    al = rng.choice([Fr(0), rq(0, Fr(1, 6)), Fr(1, 6) - Fr(1, rng.randint(10 ** 3, 10 ** 6))])
    r = Fr(s - 1, 2)
    bmax = (r + 1 - nu * al) / 2               # (iii): beta < bmax
    bsat = max(sat_edge(s, nu, al), Fr(1, 10 ** 4))
    if bsat >= bmax:
        nskip += 1
        continue
    mode = rng.random()
    if mode < 0.25:
        be = bsat
    elif mode < 0.4:
        be = bsat + (bmax - bsat) * Fr(1, 10 ** 5)
    elif mode < 0.55:
        be = bmax - (bmax - bsat) * Fr(1, 10 ** 5)
    else:
        be = bsat + (bmax - bsat) * Fr(rng.randint(1, 9999), 10 ** 4)
    ok_dom, why, z0, z2 = C.in_domain(s, nu, al, be)
    if not ok_dom:
        print("    generator produced an out-of-domain point", s, nu, al, be, why)
        nskip += 1
        continue
    n += 1
    mine = 2 * be / 3 + C.step_outer(s, nu, al, be)
    ps = pkg_step(s, nu, al, be)
    if ps != mine:
        nmis += 1
        print("    MISMATCH pkg vs own", s, nu, al, be, ps, mine)
    lo, up = C.lower(s, nu, al, be), C.upper(be)
    if not (lo <= ps <= up):
        nviol += 1
        print("    VIOLATION", s, nu, al, be, float(lo), float(ps), float(up))
    sl, su = ps - lo, up - ps
    if worst_lo is None or sl < worst_lo[0]:
        worst_lo = (sl, s, nu, al, be)
    if worst_up is None or su < worst_up[0]:
        worst_up = (su, s, nu, al, be)
    ratios.append(float(lo / ps))
check("PkgAB step == own exact step", nmis == 0, f"{n} points ({nskip} draws skipped: empty domain)")
check("lower <= step <= upper", nviol == 0)
print(f"    tightest lower: step - lower = {worst_lo[0]} ({float(worst_lo[0]):.3g}) at s={worst_lo[1]} nu={worst_lo[2]} alpha={worst_lo[3]} beta={worst_lo[4]}")
print(f"    tightest upper: upper - step = {worst_up[0]} ({float(worst_up[0]):.3g}) at s={worst_up[1]} nu={worst_up[2]} alpha={worst_up[3]} beta={worst_up[4]}")
ratios.sort()
print(f"    lower/step: min {ratios[0]:.4f}  median {ratios[len(ratios)//2]:.4f}  max {ratios[-1]:.4f}")

print(f"\nSUMMARY: {len(FAILS)} failed checks {FAILS}   ({time.time() - t0:.0f} s)")
