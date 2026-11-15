#!/usr/bin/env python3
"""Check 2 of the E733 review: coverage of [0, 1/6] x [0, 2] for every nu = 1..24 (COMPUTED, exact rationals).

reviewer: Claude Opus 5.5 (local fresh-context subagent; same model family as the author)

Reads (never writes) E730 cover-nu{2..22 even}.json, E732 cover-nu{1..21 odd}.json and E733 extend.json. For each nu:
  final tiling = earlier cover with every `La(x=3), alpha > 0` box replaced by the extend.json boxes inside it
                 (nu = 23, 24: extend.json alone).
Checks: (a) every La box of every earlier cover has an extend.json replacement tiling it exactly; extend.json has no box
outside a La box (nu <= 22); (b) the final boxes tile the rectangle (pairwise interior-disjoint, total area 1/3);
(c) every final status is certified (floor_lo > 0) or invalid for iii / saturation / window(x=3); no La, open, error,
unresolved remains; (d) each invalid verdict re-derived independently where cheap: iii at the lower corner, window(x=3)
by MY OWN reading of the inequality at the upper corner; (e) the even nu <= 10 covers contain no La verdict at all;
(f) min floor_lo per nu and overall.
Writes coverage.json (small) next to this file.
"""
import json
import math
import os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.normpath(os.path.join(HERE, "..", ".."))
E730, E732, E733 = (os.path.join(R, d) for d in ("E730-box-certify", "E732-odd-nu", "E733-window-region"))
LA = "La(x=3), alpha > 0"
A_MAX, B_MAX = Fr(1, 6), Fr(2)


def box(x):
    return (Fr(x["alpha"][0]), Fr(x["alpha"][1]), Fr(x["beta"][0]), Fr(x["beta"][1]))


def inside(b, B):
    return B[0] <= b[0] and b[1] <= B[1] and B[2] <= b[2] and b[3] <= B[3]


def area(b):
    return (b[1] - b[0]) * (b[3] - b[2])


def overlap(b, c):
    return min(b[1], c[1]) > max(b[0], c[0]) and min(b[3], c[3]) > max(b[2], c[2])


def my_window3(b, nu):
    """Necessary condition at x -> 3+ (my derivation, see REVIEW.md check 1): window-valid with alpha > 0 requires
    2*beta*x >= (1 - 2*alpha*x) * (ceil(nu/2) - 1) for x -> 3+, i.e. 6 beta >= (1 - 6 alpha) k. Fails on the whole box iff it
    fails at the corner (alpha1, beta1)."""
    k = -((-nu) // 2) - 1
    return 6 * b[3] < (1 - 6 * b[1]) * k


def main():
    ext = json.load(open(os.path.join(E733, "extend.json")))
    out = {"per_nu": {}, "problems": []}
    allmin = None
    for nu in range(1, 25):
        if nu <= 22:
            src = os.path.join(E732 if nu % 2 else E730, f"cover-nu{nu}.json")
            prev = json.load(open(src))
        else:
            prev = []
        exn = [x for x in ext if x["nu"] == nu]
        la = [x for x in prev if x.get("why") == LA]
        if nu % 2 == 0 and nu <= 10 and la:
            out["problems"].append(f"nu={nu}: even nu <= 10 cover has {len(la)} La boxes")
        whys = sorted({x.get("why", x["status"]) for x in prev})
        final = [x for x in prev if x.get("why") != LA]
        used = set()
        for L in la:
            B = box(L)
            rep = [i for i, x in enumerate(exn) if inside(box(x), B)]
            if sum(area(box(exn[i])) for i in rep) != area(B):
                out["problems"].append(f"nu={nu}: La box {B} not exactly re-tiled by extend.json")
            used |= set(rep)
        if nu <= 22:
            stray = [i for i in range(len(exn)) if i not in used]
            if stray:
                out["problems"].append(f"nu={nu}: {len(stray)} extend.json boxes outside every La box")
            final += [exn[i] for i in sorted(used)]
        else:
            final += exn
        # tiling
        bs = [box(x) for x in final]
        tot = sum((area(b) for b in bs), Fr(0))
        if tot != A_MAX * B_MAX:
            out["problems"].append(f"nu={nu}: total area {tot} != 1/3")
        if any(b[0] < 0 or b[1] > A_MAX or b[2] < 0 or b[3] > B_MAX for b in bs):
            out["problems"].append(f"nu={nu}: box outside the rectangle")
        # pairwise disjointness (bucket by beta grid row of 1/20)
        buckets = {}
        for i, b in enumerate(bs):
            for j in range(math.floor(b[2] * 20), math.ceil(b[3] * 20)):
                buckets.setdefault(j, []).append(i)
        ov = 0
        for idx in buckets.values():
            for p in range(len(idx)):
                for q in range(p + 1, len(idx)):
                    if overlap(bs[idx[p]], bs[idx[q]]):
                        ov += 1
        if ov:
            out["problems"].append(f"nu={nu}: {ov} overlapping box pairs")
        # statuses
        cnt, mn, mnbox = {}, None, None
        for x, b in zip(final, bs):
            st = x["status"] if x["status"] != "invalid" else "invalid:" + x["why"]
            cnt[st] = cnt.get(st, 0) + 1
            if x.get("final") == "unresolved" or x["status"] not in ("certified", "invalid"):
                out["problems"].append(f"nu={nu}: box {b} status {x['status']} {x.get('final')}")
            if x["status"] == "certified":
                if not x["floor_lo"] > 0:
                    out["problems"].append(f"nu={nu}: certified box {b} has floor_lo {x['floor_lo']}")
                if mn is None or x["floor_lo"] < mn:
                    mn, mnbox = x["floor_lo"], [str(v) for v in b]
            elif x["status"] == "invalid":
                w = x["why"]
                if w == "iii":
                    if not 2 * b[2] + nu * b[0] - 1 >= 3:
                        out["problems"].append(f"nu={nu}: iii box {b} does not fail (iii) at its lower corner")
                elif w.startswith("window"):
                    if not my_window3(b, nu):
                        out["problems"].append(f"nu={nu}: window box {b} fails my own window(x=3) check")
                elif w == "saturation":
                    pass  # spot-checked in hunt_holes.py
                else:
                    out["problems"].append(f"nu={nu}: unexpected invalid reason {w} at {b}")
        out["per_nu"][nu] = dict(prev_reasons=whys, la_boxes=len(la), extend_boxes=len(exn), final_boxes=len(final),
                                 area=str(tot), counts=cnt, min_floor_lo=mn, min_box=mnbox)
        if mn is not None and (allmin is None or mn < allmin[0]):
            allmin = (mn, nu, mnbox)
        print(f"nu={nu:2d} La={len(la):3d} ext={len(exn):3d} final={len(final):3d} area={tot} min={mn} {cnt}", flush=True)
    out["overall_min"] = allmin
    print("overall min floor_lo:", allmin)
    print("problems:", len(out["problems"]))
    for p in out["problems"][:40]:
        print("  ", p)
    out["reviewer"] = "Claude Opus 5.5 (local fresh-context subagent; same model family as the author)"
    json.dump(out, open(os.path.join(HERE, "coverage.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
