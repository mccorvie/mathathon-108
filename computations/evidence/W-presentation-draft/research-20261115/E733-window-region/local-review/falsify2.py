#!/usr/bin/env python3
"""Check 4, stage 2 (values) on a coarse rational grid alpha = k/240, beta = m/120 (small period P, so scan.cell is fast;
falsify.py's stage 2 was stopped because its fine random rationals give periods ~10^5). Stage 1 as in falsify.py (window-valid
at every x, (iii), z_7 >= 0, outside the derived region, membership in certified boxes only); stage 2: per nu the two points
whose containing certified box has the LOWEST floor_lo, plus one point of a newly certified (extend.json) box; scan.cell's
floor7 minus 1/144 at odd nu must be >= every containing box's floor_lo. Writes falsify2.json.
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import json, os, random, sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify as FS, coverage as CV

if __name__ == "__main__":
    rng = random.Random(2401)
    ext = json.load(open(os.path.join(CV.E733, "extend.json")))
    tiles = {nu: FS.tiling(nu, ext) for nu in range(1, 25)}
    newbox = {nu: [CV.box(x) for x in ext if x["nu"] == nu and x["status"] == "certified"] for nu in range(1, 25)}
    jobs = sorted({(nu, str(Fr(rng.randint(1, 39), 240)), str(Fr(rng.randint(1, 239), 120)), "uniform")
                   for nu in range(1, 25) for _ in range(700)})
    t0 = time.time()
    with Pool(6) as pool:
        kept = [r for r in pool.map(FS.job1, jobs, chunksize=16) if r]
    holes, by = [], {}
    for r in kept:
        a, b = Fr(r["alpha"]), Fr(r["beta"])
        cont = [x for x in tiles[r["nu"]] if CV.inside((a, a, b, b), CV.box(x))]
        r["boxes"] = [(x["status"] + ("/" + x["why"] if x["status"] == "invalid" else ""), x.get("floor_lo")) for x in cont]
        r["in_new_box"] = any(CV.inside((a, a, b, b), B) for B in newbox[r["nu"]])
        if not cont or any(x["status"] != "certified" for x in cont):
            holes.append(r)
        else:
            r["min_lo"] = min(lo for _, lo in r["boxes"])
            by.setdefault(r["nu"], []).append(r)
    print(f"stage 1: {len(jobs)} grid draws, {len(kept)} window-valid outside the derived region ({time.time()-t0:.0f}s); HOLES: {len(holes)}", flush=True)
    pick = []
    for nu, v in sorted(by.items()):
        v.sort(key=lambda r: r["min_lo"])
        sel = v[:2]
        nb = [r for r in v[2:] if r["in_new_box"]]
        if nb:
            sel.append(nb[0])
        pick += sel
    t1 = time.time()
    with Pool(6) as pool:
        vals = pool.map(FS.job2, pick, chunksize=1)
    bad, sl = [], []
    for r in vals:
        if r["floor7_relaxed"] is None:
            r["note"] = "no floor7"; continue
        f = r["floor7_relaxed"] - (1 / 144 if r["nu"] % 2 else 0)
        r["floor_window_lower"] = f
        for _, lo in r["boxes"]:
            sl.append((round(f - lo, 5), r["nu"], r["alpha"], r["beta"], round(lo, 5), round(f, 5)))
            if lo > f: bad.append(r)
    sl.sort()
    print(f"stage 2: {len(vals)} floors ({time.time()-t1:.0f}s); bound above floor: {len(bad)}", flush=True)
    print("  smallest slacks (slack, nu, alpha, beta, box floor_lo, floor):", sl[:5], flush=True)
    print("  smallest floor:", min((r["floor_window_lower"], r["nu"], r["alpha"], r["beta"]) for r in vals if "floor_window_lower" in r), flush=True)
    print("  points per nu:", {nu: sum(1 for r in vals if r["nu"] == nu) for nu in sorted(by)}, flush=True)
    json.dump(dict(reviewer="Claude Opus 5.5 (local fresh-context subagent; same model family as the author)",
                   draws=len(jobs), kept=len(kept), holes=holes, stage2=vals, bound_above_floor=bad, smallest_slacks=sl[:10]),
              open(os.path.join(HERE, "falsify2.json"), "w"), indent=1, default=str)
