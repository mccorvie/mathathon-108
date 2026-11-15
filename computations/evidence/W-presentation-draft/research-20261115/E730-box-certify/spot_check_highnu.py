#!/usr/bin/env python3
"""[108/N E730] Spot check of the nu = 12..22 cover (cover.py --la) against exact package values (scope_alpha_beta/scan.cell).

Random rational points (alpha = k/240, beta = m/120, seed 1224) that satisfy (i) La >= 0, (ii) zmin >= 0 and (iii); at each,
every certified box containing it must have floor_lo <= floor7 (a necessary condition), and no such point may lie only in
invalid boxes. Writes spot-check-highnu.json. Run from any folder.
"""
import json
import os
import random
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "..", "scope_alpha_beta")))
import scan  # noqa: E402
import pkg_ab as PA  # noqa: E402

NUS = (12, 14, 16, 18, 20, 22)


def candidates(per_nu=8, seed=1224):
    rng = random.Random(seed)
    out = []
    for nu in NUS:
        got, tries = 0, 0
        while got < per_nu and tries < 4000:
            tries += 1
            a, b = Fr(rng.randint(1, 39), 240), Fr(rng.randint(12, 239), 120)
            if 2 * b + nu * a - 1 >= 3 or PA.La_check(nu, a, b)[0] < 0:
                continue
            try:
                if min(PA.PkgAB(5, nu, a, b).zmin(), PA.PkgAB(7, nu, a, b).zmin()) < 0:
                    continue
            except Exception:
                continue
            out.append((str(a), str(b), nu)); got += 1
    return out


if __name__ == "__main__":
    pts = candidates()
    with Pool(6) as p:
        res = p.map(scan.cell, pts)
    rows, bad, orphan = [], [], []
    for (a, b, nu), r in zip(pts, res):
        a_, b_ = Fr(a), Fr(b)
        boxes = [x for x in json.load(open(os.path.join(HERE, f"cover-nu{nu}.json")))
                 if Fr(x["alpha"][0]) <= a_ <= Fr(x["alpha"][1]) and Fr(x["beta"][0]) <= b_ <= Fr(x["beta"][1])]
        cert = [x["floor_lo"] for x in boxes if x["status"] == "certified"]
        row = dict(nu=nu, alpha=a, beta=b, admissible=r["admissible"], floor7=r.get("floor7"), box_bounds=cert,
                   statuses=[x["status"] + ("/" + x["why"] if x.get("why") else "") for x in boxes])
        if not cert:
            orphan.append(row)
        if r.get("floor7") is not None and any(lo > r["floor7"] for lo in cert):
            bad.append(row)
        rows.append(row)
        print(row, flush=True)
    slack = [r["floor7"] - lo for r in rows if r["floor7"] is not None for lo in r["box_bounds"]]
    out = dict(points=len(rows), violations=bad, in_no_certified_box=orphan, min_slack=min(slack) if slack else None,
               min_floor7={nu: min((r["floor7"] for r in rows if r["nu"] == nu and r["floor7"] is not None), default=None) for nu in NUS},
               rows=rows)
    json.dump(out, open(os.path.join(HERE, "spot-check-highnu.json"), "w"), indent=1)
    print("points", len(rows), "violations", len(bad), "orphans", len(orphan), "min slack", out["min_slack"], "min floor7", out["min_floor7"])
