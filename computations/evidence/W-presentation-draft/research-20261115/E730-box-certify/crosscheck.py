#!/usr/bin/env python3
"""[108/N E730] Cross-check of the cover against the team's scan (scope_alpha_beta/out/*.json, read-only).

Every admissible scan point with alpha < 1/6 must lie in a certified box, and every certified box containing it must have
a lower bound <= the point's floor7 (the scan's sigma is the optimum of lb_opt there; ours is rescaled from the box centre,
so this is a necessary condition, not a proof). Writes crosscheck.json.
"""
import glob
import json
import os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
SCAN = os.path.normpath(os.path.join(HERE, "..", "..", "..", "scope_alpha_beta", "out"))
cover = {nu: json.load(open(os.path.join(HERE, f"cover-nu{nu}.json"))) for nu in (2, 4, 6, 8, 10)}
pts = {}
for f in sorted(glob.glob(os.path.join(SCAN, "*.json"))):
    try:
        d = json.load(open(f))
    except Exception:
        continue
    if isinstance(d, dict):
        d = [x for v in d.values() if isinstance(v, list) for x in v]
    for r in d:
        if isinstance(r, dict) and r.get("admissible") and "floor7" in r:
            pts[(r["nu"], r["alpha"], r["beta"])] = r
bad, orphan, slack, scan_min = [], [], [], {}
for (nu, a, b), r in pts.items():
    a, b = Fr(a), Fr(b)
    if a >= Fr(1, 6):
        continue
    scan_min[nu] = min(scan_min.get(nu, 9.0), r["floor7"])
    boxes = [x for x in cover[nu] if Fr(x["alpha"][0]) <= a <= Fr(x["alpha"][1]) and Fr(x["beta"][0]) <= b <= Fr(x["beta"][1])]
    cert = [x for x in boxes if x["status"] == "certified"]
    if not cert:
        orphan.append([nu, str(a), str(b), r["floor7"], [x.get("why") for x in boxes]])
    for x in cert:
        slack.append(r["floor7"] - x["floor_lo"])
        if x["floor_lo"] > r["floor7"]:
            bad.append([nu, str(a), str(b), r["floor7"], x["floor_lo"]])
out = dict(admissible_points=sum(1 for k in pts if Fr(k[1]) < Fr(1, 6)), pairs_checked=len(slack),
           bound_above_point_value=bad, points_in_no_certified_box=orphan,
           slack=dict(min=min(slack), median=sorted(slack)[len(slack) // 2], max=max(slack)),
           scan_min_floor7=scan_min,
           cover_min_bound={nu: min(x["floor_lo"] for x in cover[nu] if x["status"] == "certified") for nu in cover})
json.dump(out, open(os.path.join(HERE, "crosscheck.json"), "w"), indent=1)
print(json.dumps(out, indent=1))
