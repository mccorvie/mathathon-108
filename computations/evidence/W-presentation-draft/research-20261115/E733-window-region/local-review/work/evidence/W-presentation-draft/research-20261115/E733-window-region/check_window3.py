#!/usr/bin/env python3
"""[108/N E733] Check of extend.window3_fails against the exact window allocation (COMPUTED, exact rationals).

At a point (nu, alpha, beta) and x slightly above 3, decide whether SOME window allocation has L_a >= 0 at every class
(continuum, E732 window.py's class structure): find the window base Y*; forced classes sit at Y* + 1/2; matching classes at
Y* or Y* + 1, and the measure at Y* + 1 is fixed by the mean. An assignment with all L >= 0 exists iff every forced class has
L >= 0, every matching class has L >= 0 at Y* + 1, and the matching classes that are negative at Y* fit into the up-measure.
Claim tested: window3_fails(box) at the corner => no valid allocation at any sampled point of the box with alpha > 0 (soundness),
and the test's inequality agrees with this exact feasibility at x -> 3+ (sharpness, sampled).
"""
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "E732-odd-nu")))
import window as W  # noqa: E402
import extend as EX  # noqa: E402
from window import PA, frac, fl  # noqa: E402


def feasible(P, x):
    cl = W.classes(P, x)
    target = P.HL * x - sum(mu * Fr(l, 2) for mu, l, _, _ in cl)
    base = fl(4 * target) - 4
    for k in range(base, base + 9):
        ys = Fr(k, 2)
        match = [(mu, c) for mu, _, _, c in cl if frac(c - ys) == 0]
        other = [(mu, c) for mu, _, _, c in cl if frac(c - ys) != 0]
        M, O = sum((m for m, _ in match), Fr(0)), sum((m for m, _ in other), Fr(0))
        lo = M * ys + O * (ys + Fr(1, 2))
        hi = M * (ys + 1) + O * (ys + Fr(1, 2))
        if lo <= target <= hi and (M > 0 or lo == target):
            up = target - lo
            if any(ys + Fr(1, 2) - c < 0 for _, c in other):
                return False
            if any(ys + 1 - c < 0 for _, c in match):
                return False
            need = sum((m for m, c in match if ys - c < 0), Fr(0))
            return need <= up
    raise RuntimeError("no window")


def main():
    rng = random.Random(733)
    xs = [3 + Fr(1, 10 ** 6), 3 + Fr(1, 10 ** 4)]
    sound_bad = sharp_bad = n_flag = n_unflag = 0
    for _ in range(3000):
        nu = rng.randint(1, 30)
        a = Fr(rng.randint(1, 1599), 9600)                  # 0 < alpha < 1/6
        b = Fr(rng.randint(1, 3999), 2000)                  # 0 < beta < 2
        if 2 * b + nu * a - 1 >= 3:
            continue
        P = PA.PkgAB(7, nu, a, b)
        flagged = EX.window3_fails(a, a, b, b, nu)
        ok = [feasible(P, x) for x in xs]
        if flagged:
            n_flag += 1
            if ok[0]:
                sound_bad += 1                              # test says invalid but the window allocation is valid at 3+
        else:
            n_unflag += 1
            if not ok[0]:
                sharp_bad += 1                              # not flagged, yet infeasible at 3+ (allowed: test is only necessary)
    print(f"flagged points {n_flag}: valid at x = 3 + 1e-6 anyway (unsound): {sound_bad}  (must be 0)")
    print(f"unflagged points {n_unflag}: infeasible at x = 3 + 1e-6 (test not sharp there): {sharp_bad}")
    for nu, a, b in ((23, Fr(1, 240), Fr(9, 5)), (17, Fr(1, 240), Fr(53, 40)), (23, Fr(7, 240), Fr(3, 2)), (25, Fr(1, 240), Fr(19, 10)), (24, Fr(1, 240), Fr(9, 5))):
        P = PA.PkgAB(7, nu, a, b)
        print(f"  review point nu={nu} ({a}, {b}): window3_fails={EX.window3_fails(a, a, b, b, nu)}, feasible at 3+ = {feasible(P, xs[0])}")


if __name__ == "__main__":
    main()
