#!/usr/bin/env python3
"""Check 1 of the E733 review: hunt for a window-valid point inside a box declared invalid (COMPUTED, exact rationals).

reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)

(a) every `window(x=3), alpha > 0` box of extend.json: its upper corner (alpha1, beta1), 3 points within 1/10^4 of that corner
    and 6 random interior points (alpha > 0). Each must be window-INFEASIBLE at some x in (3, 3.5] (rv_window.valid_all, exact
    in x, shift 0 = the most generous row total).
(b) every `saturation` box of the final tiling (all nu = 1..24): 6 random points plus the upper corner; a point with
    pkg_ab z_7 >= 0 would be a candidate (then tested for (iii) and window validity).
(c) sharpness band: random (nu, alpha) and beta just below / above the line 6 beta = (1 - 6 alpha)(ceil(nu/2) - 1).
(d) FINITE p (no continuum): at a few flagged points near the line, an inner prime p with x = K/p just above 3 and the exact
    discrete window feasibility over the (p - 1)/2 classes with Fauzan's row total sum L_a = h - L_0 (h = floor(beta K),
    L_0 = 4M + 10, M = 40, K >= 200 M^2, K in 40Z).
<= 6 processes. Writes hunt_holes.json (small).
"""
import json
import math
import os
import random
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "scope_alpha_beta")))
import rv_window as RW  # noqa: E402
import coverage as CV  # noqa: E402

E733 = os.path.normpath(os.path.join(HERE, ".."))


def kk(nu):
    return -((-nu) // 2) - 1


def job_a(args):
    nu, a, b = args
    a, b = Fr(a), Fr(b)
    ok, bad, _ = RW.valid_all(a, b, nu, xhi=Fr(7, 2))
    return dict(nu=nu, alpha=str(a), beta=str(b), feasible_on_3_to_3p5=ok, first_bad=None if bad is None else float(bad))


def job_b(args):
    nu, a, b = args
    import pkg_ab as PA
    a, b = Fr(a), Fr(b)
    try:
        z = PA.PkgAB(7, nu, a, b).zmin()
    except Exception as e:  # noqa: BLE001
        return dict(nu=nu, alpha=str(a), beta=str(b), err=repr(e))
    r = dict(nu=nu, alpha=str(a), beta=str(b), zmin7=float(z))
    if z >= 0:
        r["iii"] = 2 * b + nu * a - 1 < 3
        r["window_valid"] = RW.valid_all(a, b, nu)[0] if r["iii"] else None
    return r


def discrete_feasible(nu, al, be, x_target, M=40):
    """Exact finite-p window feasibility (L_a >= 0 integers, all Y in one [w, w + 1]) at a prime p with K/p just above
    x_target. Returns (feasible, p, K, x)."""
    K = 40 * math.ceil(200 * M * M / 40)
    while True:   # find K in 40Z and prime p with 3 < K/p <= x_target, p <= K/3
        p = math.floor(K / x_target) + 1
        while p <= K // 3 and not all(p % q for q in range(2, int(p ** 0.5) + 1)):
            p += 1
        if p <= K // 3 and Fr(K, p) <= x_target and Fr(K, p) > 3:
            break
        K += 40
    N = math.floor(al * K)
    h = math.floor(be * K)
    L0 = 4 * M + 10
    m = (p - 1) // 2
    groups = {}
    for a in range(1, m + 1):
        lK = sum(1 for j0 in (a, p - a) for j in range(j0, K + 1, p))
        lN = sum(1 for j0 in (a, p - a) for j in range(j0, N + 1, p))
        groups[(lK, lN)] = groups.get((lK, lN), 0) + 1
    c = {g: Fr(nu, 2) * g[1] - Fr(g[0], 2) for g in groups}
    total_Y = (h - L0) + sum(n * c[g] for g, n in groups.items())     # sum_a Y_a = sum L_a + sum c_a
    mean = total_Y / m
    for k in range(math.floor(2 * (mean - 1)) - 2, math.ceil(2 * mean) + 3):
        w = Fr(k, 2)
        lo = hi = Fr(0)
        okw = True
        for g, n in groups.items():
            ymin = c[g] + math.ceil(max(w, c[g]) - c[g])
            ymax = c[g] + math.floor(w + 1 - c[g])
            if ymin > ymax:
                okw = False
                break
            lo += n * ymin
            hi += n * ymax
        if okw and lo <= total_Y <= hi:
            return True, p, K, float(Fr(K, p))
    return False, p, K, float(Fr(K, p))


def main():
    rng = random.Random(1108)
    ext = json.load(open(os.path.join(E733, "extend.json")))
    out = {"reviewer": "Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"}
    # (a)
    jobs = []
    for x in ext:
        if x["status"] == "invalid" and x["why"].startswith("window"):
            a0, a1, b0, b1 = CV.box(x)
            nu = x["nu"]
            pts = [(a1, b1)] + [(a1 - Fr(rng.randint(0, 9), 10 ** 5), b1 - Fr(rng.randint(0, 9), 10 ** 5)) for _ in range(3)]
            pts += [(a0 + (a1 - a0) * Fr(rng.randint(1, 999), 1000), b0 + (b1 - b0) * Fr(rng.randint(0, 1000), 1000))
                    for _ in range(6)]
            jobs += [(nu, str(a), str(b)) for a, b in pts if a > 0]
    with Pool(6) as pool:
        ra = pool.map(job_a, jobs, chunksize=16)
    holes_a = [r for r in ra if r["feasible_on_3_to_3p5"]]
    out["a"] = dict(points=len(ra), boxes=sum(1 for x in ext if x.get("why", "").startswith("window")),
                    feasible_anyway=holes_a[:20], n_feasible=len(holes_a),
                    max_first_bad_x=max(r["first_bad"] for r in ra if r["first_bad"] is not None))
    print(f"(a) window(x=3) boxes: {len(ra)} points, window-feasible on (3, 3.5] anyway: {len(holes_a)}; "
          f"largest first failing x: {out['a']['max_first_bad_x']:.6f}", flush=True)
    # (b) saturation boxes of the final tiling, all nu
    jobs = []
    for nu in range(1, 25):
        if nu <= 22:
            prev = json.load(open(os.path.join(CV.E732 if nu % 2 else CV.E730, f"cover-nu{nu}.json")))
        else:
            prev = []
        boxes = [x for x in prev if x.get("why") == "saturation"] + [x for x in ext if x["nu"] == nu and x.get("why") == "saturation"]
        for x in boxes:
            a0, a1, b0, b1 = CV.box(x)
            pts = [(a1, b1)] + [(a0 + (a1 - a0) * Fr(rng.randint(1, 999), 1000), b0 + (b1 - b0) * Fr(rng.randint(1, 999), 1000))
                                for _ in range(6)]
            jobs += [(nu, str(a), str(b)) for a, b in pts if a > 0]
    with Pool(6) as pool:
        rb = pool.map(job_b, jobs, chunksize=16)
    cand = [r for r in rb if r.get("zmin7", -1) >= 0]
    holes_b = [r for r in cand if r.get("window_valid")]
    out["b"] = dict(points=len(rb), errors=sum(1 for r in rb if "err" in r), zmin_nonneg=cand[:20], n_zmin_nonneg=len(cand),
                    holes=holes_b, max_zmin=max(r["zmin7"] for r in rb if "zmin7" in r))
    print(f"(b) saturation boxes: {len(rb)} points, z_7 >= 0 at {len(cand)}, of which window-valid with (iii): {len(holes_b)}; "
          f"max z_7 seen {out['b']['max_zmin']:.5f}", flush=True)
    # (c) sharpness band
    jobs, side = [], []
    for _ in range(600):
        nu = rng.randint(3, 30)
        a = Fr(rng.randint(1, 1599), 9600)
        line = (1 - 6 * a) * kk(nu) / 6
        d = Fr(rng.randint(1, 2000), 10 ** 6)
        for b, s in ((line - d, "below"), (line + d, "above")):
            if b > 0 and 2 * b + nu * a - 1 < 3:
                jobs.append((nu, str(a), str(b)))
                side.append(s)
    with Pool(6) as pool:
        rc = pool.map(job_a, jobs, chunksize=16)
    below_feas = [r for r, s in zip(rc, side) if s == "below" and r["feasible_on_3_to_3p5"]]
    above = [r for r, s in zip(rc, side) if s == "above"]
    above_infeas_at3 = [r for r in above if not r["feasible_on_3_to_3p5"] and r["first_bad"] < 3.001]
    out["c"] = dict(below=sum(1 for s in side if s == "below"), below_feasible=below_feas[:10], n_below_feasible=len(below_feas),
                    above=len(above), above_infeasible_just_above_3=len(above_infeas_at3),
                    above_infeasible_somewhere_in_3_3p5=sum(1 for r in above if not r["feasible_on_3_to_3p5"]))
    print(f"(c) band: below the line {out['c']['below']} points, feasible anyway {len(below_feas)}; above the line {len(above)}, "
          f"infeasible just above 3: {len(above_infeas_at3)}, infeasible somewhere in (3, 3.5]: {out['c']['above_infeasible_somewhere_in_3_3p5']}", flush=True)
    # (d) finite p near the line
    pts = []
    for nu in (9, 12, 17, 23, 24):
        a = Fr(1, 96)
        line = (1 - 6 * a) * kk(nu) / 6
        pts += [(nu, a, line - Fr(1, 200)), (nu, a, line + Fr(1, 200))]
    rd = []
    for nu, a, b in pts:
        f, p, K, x = discrete_feasible(nu, a, b, Fr(3) + Fr(1, 2000))
        rd.append(dict(nu=nu, alpha=str(a), beta=str(b), side="below" if 6 * b < (1 - 6 * a) * kk(nu) else "above",
                       finite_p_feasible=f, p=p, K=K, x=x))
        print(f"(d) nu={nu} alpha={a} beta={b} ({rd[-1]['side']}): finite-p feasible={f} at p={p}, K={K}, x={x:.6f}", flush=True)
    out["d"] = rd
    json.dump(out, open(os.path.join(HERE, "hunt_holes.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
