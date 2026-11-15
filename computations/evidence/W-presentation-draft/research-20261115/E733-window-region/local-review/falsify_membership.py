#!/usr/bin/env python3
"""Check 4, stage 1 only, at larger scale: window-valid points (exact in x, shift 0) with (iii) and z_7 >= 0, outside the
derived region, for nu = 1..24 -- each must lie only in certified boxes of the final tiling (COMPUTED, exact rationals).
Uses falsify.job1 / falsify.tiling. Usage: falsify_membership.py [draws_per_nu] [seed]. Writes falsify_membership.json.
reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"""
import json, os, random, sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify as FS, coverage as CV

if __name__ == "__main__":
    n1 = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 99)
    ext = json.load(open(os.path.join(CV.E733, "extend.json")))
    tiles = {nu: FS.tiling(nu, ext) for nu in range(1, 25)}
    jobs = []
    for nu in range(1, 25):
        newc = [x for x in ext if x["nu"] == nu and x["status"] == "certified"]
        # also aim at the window-invalid boxes' neighbourhood: draws near the line 6 beta = (1 - 6 alpha) k, both sides
        k = -((-nu) // 2) - 1
        for i in range(n1):
            r = i % 3
            if newc and r == 0:
                a0, a1, b0, b1 = CV.box(rng.choice(newc))
                a = a0 + (a1 - a0) * Fr(rng.randint(1, 9999), 10000); b = b0 + (b1 - b0) * Fr(rng.randint(0, 10000), 10000)
                jobs.append((nu, str(a), str(b), "new-cert-box"))
            elif r == 1 and k > 0:
                a = Fr(rng.randint(1, 15999), 96000); b = (1 - 6 * a) * k / 6 + Fr(rng.randint(-500, 3000), 10 ** 4)
                if b > 0:
                    jobs.append((nu, str(a), str(b), "uniform"))
            else:
                jobs.append((nu, str(Fr(rng.randint(1, 15999), 96000)), str(Fr(rng.randint(1, 3999), 2000)), "uniform"))
    t0 = time.time()
    with Pool(6) as pool:
        kept = [r for r in pool.map(FS.job1, jobs, chunksize=16) if r]
    holes, by, below_line = [], {}, 0
    for r in kept:
        a, b = Fr(r["alpha"]), Fr(r["beta"])
        cont = [x for x in tiles[r["nu"]] if CV.inside((a, a, b, b), CV.box(x))]
        r["boxes"] = [(x["status"] + ("/" + x["why"] if x["status"] == "invalid" else ""), x.get("floor_lo")) for x in cont]
        k = -((-r["nu"]) // 2) - 1
        below_line += 6 * b < (1 - 6 * a) * k
        if not cont or any(x["status"] != "certified" for x in cont):
            holes.append(r)
        by[r["nu"]] = by.get(r["nu"], 0) + 1
    lows = sorted(min(lo for _, lo in r["boxes"]) for r in kept if r["boxes"] and all(lo is not None for _, lo in r["boxes"]))
    print(f"{len(jobs)} draws, {len(kept)} window-valid points outside the derived region ({time.time() - t0:.0f}s); "
          f"in a non-certified box (HOLE): {len(holes)}; window-valid points strictly below the x = 3 line: {below_line}")
    print("per nu:", dict(sorted(by.items())))
    print("lowest containing-box bound among them:", lows[:3])
    for h in holes[:10]:
        print("  HOLE", h)
    json.dump(dict(reviewer="Claude Opus 5.5 (local fresh-context subagent; same model family as the author)",
                   draws=len(jobs), kept=len(kept), per_nu=by, holes=holes, below_line=below_line, lowest_bounds=lows[:10]),
              open(os.path.join(HERE, "falsify_membership.json"), "w"), indent=1, default=str)
