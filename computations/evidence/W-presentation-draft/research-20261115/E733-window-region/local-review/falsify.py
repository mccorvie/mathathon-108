#!/usr/bin/env python3
"""Check 4 of the E733 review: falsification by sampling window-valid points (COMPUTED, exact rationals + scan.cell floats).

reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)

Stage 1 (membership, cheap, many points): random (nu, alpha, beta), nu = 1..24, 0 < alpha < 1/6, 0 < beta < 2, kept if
(iii) holds, pkg_ab z_7 >= 0 (saturation) and rv_window.valid_all (window L_a >= 0 at EVERY x >= 3, exact in x, shift 0).
Half the draws are inside the boxes that E733 newly certified (outside the derived region by construction), half uniform,
kept only when OUTSIDE the derived region (La_check < 0 at even nu, < 2 at odd nu). Every kept point must lie only in
CERTIFIED boxes of the final tiling (earlier covers + extend.json); a kept point in an invalid box is a hole.
Stage 2 (values, expensive): for a subset, scan.cell's floor7 (relaxed formulas), minus 1/144 at odd nu, must be >= the
floor_lo of every containing box. Reports the smallest slack.
Usage: falsify.py [n_stage1_per_nu] [n_stage2_per_nu]   (<= 6 processes). Writes falsify.json.
"""
import json
import os
import random
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "scope_alpha_beta")))
import rv_window as RW  # noqa: E402
import coverage as CV  # noqa: E402

LA = "La(x=3), alpha > 0"


def tiling(nu, ext):
    prev = json.load(open(os.path.join(CV.E732 if nu % 2 else CV.E730, f"cover-nu{nu}.json"))) if nu <= 22 else []
    return [x for x in prev if x.get("why") != LA] + [x for x in ext if x["nu"] == nu]


def job1(args):
    nu, a, b, src = args
    import pkg_ab as PA
    a, b = Fr(a), Fr(b)
    if 2 * b + nu * a - 1 >= 3:
        return None
    lc = PA.La_check(nu, a, b)[0]
    if src == "uniform" and lc >= (2 if nu % 2 else 0):
        return None                       # inside the derived region: not what this check targets
    try:
        z = PA.PkgAB(7, nu, a, b).zmin()
    except Exception:  # noqa: BLE001
        return None
    if z < 0:
        return None
    ok, bad, _ = RW.valid_all(a, b, nu)
    if not ok:
        return None
    return dict(nu=nu, alpha=str(a), beta=str(b), src=src, La_check=str(lc), zmin7=float(z))


def job2(r):
    sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "scope_alpha_beta")))
    import scan
    t = time.time()
    c = scan.cell((r["alpha"], r["beta"], r["nu"]))
    r = dict(r)
    r["floor7_relaxed"] = c.get("floor7")
    r["seconds"] = round(time.time() - t, 1)
    return r


def main():
    n1 = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    n2 = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rng = random.Random(733108)
    ext = json.load(open(os.path.join(CV.E733, "extend.json")))
    tiles = {nu: tiling(nu, ext) for nu in range(1, 25)}
    jobs = []
    for nu in range(1, 25):
        newc = [x for x in ext if x["nu"] == nu and x["status"] == "certified"]
        for i in range(n1):
            if newc and i % 2 == 0:
                bx = rng.choice(newc)
                a0, a1, b0, b1 = CV.box(bx)
                a = a0 + (a1 - a0) * Fr(rng.randint(1, 9999), 10000)
                b = b0 + (b1 - b0) * Fr(rng.randint(0, 10000), 10000)
                jobs.append((nu, str(a), str(b), "new-cert-box"))
            else:
                jobs.append((nu, str(Fr(rng.randint(1, 15999), 96000)), str(Fr(rng.randint(1, 3999), 2000)), "uniform"))
    t0 = time.time()
    with Pool(6) as pool:
        kept = [r for r in pool.map(job1, jobs, chunksize=8) if r]
    holes, rows = [], []
    for r in kept:
        a, b = Fr(r["alpha"]), Fr(r["beta"])
        cont = [x for x in tiles[r["nu"]] if CV.inside((a, a, b, b), CV.box(x))]
        r["boxes"] = [(x["status"] + ("/" + x["why"] if x["status"] == "invalid" else ""),
                       x.get("floor_lo")) for x in cont]
        if not cont or any(x["status"] != "certified" for x in cont):
            holes.append(r)
        rows.append(r)
    by = {}
    for r in rows:
        by.setdefault(r["nu"], []).append(r)
    print(f"stage 1: {len(jobs)} draws, {len(rows)} window-valid points outside the derived region "
          f"({time.time() - t0:.0f}s); in a non-certified box (HOLE): {len(holes)}", flush=True)
    print("  per nu:", {nu: len(v) for nu, v in sorted(by.items())}, flush=True)
    for h in holes[:10]:
        print("  HOLE", h, flush=True)
    # stage 2: per nu, the points in the lowest-bound boxes first, then random
    pick = []
    for nu, v in sorted(by.items()):
        v = sorted(v, key=lambda r: min(lo for _, lo in r["boxes"] if lo is not None) if any(lo is not None for _, lo in r["boxes"]) else 9)
        sel = v[:max(1, n2 // 2)] + rng.sample(v[max(1, n2 // 2):], min(len(v) - max(1, n2 // 2), n2 - max(1, n2 // 2))) if len(v) > 1 else v
        pick += sel[:n2]
    t1 = time.time()
    with Pool(6) as pool:
        vals = pool.map(job2, pick, chunksize=1)
    bad, slacks = [], []
    for r in vals:
        if r["floor7_relaxed"] is None:
            r["note"] = "scan.cell returned no floor7"
            continue
        fl_lo = r["floor7_relaxed"] - (1 / 144 if r["nu"] % 2 else 0)
        r["floor_window_lower"] = fl_lo
        for st, lo in r["boxes"]:
            if lo is not None:
                slacks.append((fl_lo - lo, r["nu"], r["alpha"], r["beta"]))
                if lo > fl_lo:
                    bad.append(r)
    slacks.sort()
    print(f"stage 2: {len(vals)} floors ({time.time() - t1:.0f}s); box bound above the floor: {len(bad)}; "
          f"smallest slack {slacks[0] if slacks else None}", flush=True)
    print("  min floor seen:", min((r["floor_window_lower"], r["nu"], r["alpha"], r["beta"]) for r in vals if "floor_window_lower" in r), flush=True)
    json.dump(dict(reviewer="Claude Opus 5.5 (local fresh-context subagent; same model family as the author)",
                   draws=len(jobs), kept=len(rows), per_nu={nu: len(v) for nu, v in sorted(by.items())}, holes=holes,
                   stage2=vals, bound_above_floor=bad, smallest_slacks=slacks[:10]),
              open(os.path.join(HERE, "falsify.json"), "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
