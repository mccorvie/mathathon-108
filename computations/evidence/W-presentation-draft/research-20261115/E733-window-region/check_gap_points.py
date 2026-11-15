#!/usr/bin/env python3
"""[108/N E733] The window-valid points that E732's review found outside the derived region (its gap.json 'examples' and
'floors') must now lie in certified boxes of extend.json, with box bound <= the point's floor (COMPUTED).

Floor at a point: scan.cell's floor7 (relaxed formulas) minus 1/144 at odd nu (the window correction |D| <= 1/144 for the
floor, from |R_true - R_rel| <= 1/8 integrated against x^-3 on [3, oo)); exact at even nu (window = Fauzan there).
"""
import json
import os
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "scope_alpha_beta")))
import scan  # noqa: E402

if __name__ == "__main__":
    g = json.load(open(os.path.join(HERE, "..", "E732-odd-nu", "local-review", "gap.json")))
    pts = {(int(p["nu"]), p["alpha"], p["beta"]) for p in g["examples"]}
    for p in (g["floors"] if isinstance(g["floors"], list) else []):
        if isinstance(p, dict) and "nu" in p:
            pts.add((int(p["nu"]), p["alpha"], p["beta"]))
    pts = sorted(pts)[:60]
    ext = json.load(open(os.path.join(HERE, "extend.json")))
    with Pool(6) as pool:
        res = pool.map(scan.cell, [(a, b, nu) for nu, a, b in pts])
    rows, bad, orphan = [], [], []
    for (nu, a, b), r in zip(pts, res):
        a_, b_ = Fr(a), Fr(b)
        boxes = [x for x in ext if x["nu"] == nu and Fr(x["alpha"][0]) <= a_ <= Fr(x["alpha"][1]) and Fr(x["beta"][0]) <= b_ <= Fr(x["beta"][1])]
        cert = [x["floor_lo"] for x in boxes if x["status"] == "certified"]
        fl7 = r.get("floor7")
        floor = None if fl7 is None else fl7 - (1 / 144 if nu % 2 else 0)
        row = dict(nu=nu, alpha=a, beta=b, floor_window_lower=floor, box_bounds=cert, statuses=[x["status"] + "/" + x.get("why", "") for x in boxes])
        if not cert:
            orphan.append(row)
        elif floor is not None and any(lo > floor for lo in cert):
            bad.append(row)
        rows.append(row)
    slack = [r["floor_window_lower"] - lo for r in rows if r["floor_window_lower"] is not None for lo in r["box_bounds"]]
    out = dict(points=len(rows), in_no_certified_box=orphan, bound_above_floor=bad, min_slack=min(slack) if slack else None, rows=rows)
    json.dump(out, open(os.path.join(HERE, "check-gap-points.json"), "w"), indent=1)
    print(f"points {len(rows)}; in no certified extension box: {len(orphan)}; bound above floor: {len(bad)}; min slack {out['min_slack']}")
    for o in orphan[:5]:
        print("  orphan", o)
