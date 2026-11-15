#!/usr/bin/env python3
"""[108/N E733] Extend the E730/E732 cover from the derived region (La_check) to the window region (COMPUTED + PROOF-DRAFT).

The derived region of E730/E732 uses the sufficient test La_check for condition (i). The package is valid wherever Fauzan's
proof of Prop. 4.1 applies with the window allocation (E732): L_a >= 0 at every class and every inner prime. That is a larger
set (E732 local review, check 5). This driver takes every box that the earlier covers marked invalid by the La_check shortcut
`La(x=3), alpha > 0` (and, for nu = 23 and 24, the whole grid), and either certifies it with E730's box2.floor_box, or proves
it lies outside the window region, or splits it.

Necessary condition at x = 3 (PROOF-DRAFT): at x -> 3+, every class has l_K = 6 and l_N in {0, 1} (l_N = 1 on measure 3 alpha
when 0 < alpha < 1/6). L_a >= 0 means Z >= b, so Z_1 >= nu/2 on the l_N = 1 classes. The window (Y_1 - Y_0 <= 1 with the same
l_K) forces Z_0 >= Z_1 - 1, and Z_0 is an integer, so Z_0 >= ceil(nu/2) - 1. The mean of Z is 6 beta + 3 nu alpha, hence
  6 beta + 3 nu alpha >= 6 alpha (nu/2) + (1 - 6 alpha)(ceil(nu/2) - 1),  i.e.  6 beta >= (1 - 6 alpha)(ceil(nu/2) - 1).
A box (alpha > 0 part) is outside the window region if 6 beta_1 < (1 - 6 alpha_1)(ceil(nu/2) - 1). With (iii) this also makes
the window region empty for every nu >= 25. The line alpha = 0 is the nu-free package (E730), covered separately.
Usage: extend.py [--workers 7] [--maxdepth 4]
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
E730 = os.path.normpath(os.path.join(HERE, "..", "E730-box-certify"))
E732 = os.path.normpath(os.path.join(HERE, "..", "E732-odd-nu"))
sys.path.insert(0, E730)

LA_WHY = "La(x=3), alpha > 0"


def window3_fails(a0, a1, b0, b1, nu):
    k = math.ceil(Fr(nu, 2)) - 1
    return 6 * Fr(b1) < (1 - 6 * Fr(a1)) * k


def work(job):
    a0, a1, b0, b1, nu, depth = job
    import box2 as B2
    t0 = time.time()
    a0, a1, b0, b1 = Fr(a0), Fr(a1), Fr(b0), Fr(b1)
    if 2 * b0 + nu * a0 - 1 >= 3:
        r = {"status": "invalid", "why": "iii"}
    elif window3_fails(a0, a1, b0, b1, nu):
        r = {"status": "invalid", "why": "window(x=3), alpha > 0"}
    else:
        try:
            r = B2.floor_box(a0, a1, b0, b1, nu)
        except Exception as e:  # recorded, never hidden
            r = {"status": "error", "error": f"{type(e).__name__}: {e}"}
    r.update(alpha=[str(a0), str(a1)], beta=[str(b0), str(b1)], nu=nu, depth=depth, seconds=round(time.time() - t0, 2))
    return r


def initial_jobs():
    jobs = []
    for nu in list(range(1, 22, 2)) + list(range(12, 23, 2)):
        src = os.path.join(E732 if nu % 2 else E730, f"cover-nu{nu}.json")
        for x in json.load(open(src)):
            if x.get("why") == LA_WHY:
                jobs.append((x["alpha"][0], x["alpha"][1], x["beta"][0], x["beta"][1], nu, 0))
    for nu in (23, 24):
        jobs += [(str(Fr(i, 48)), str(Fr(i + 1, 48)), str(Fr(j, 20)), str(Fr(j + 1, 20)), nu, 0) for i in range(8) for j in range(40)]
    return jobs


def main():
    args = sys.argv[1:]
    workers, maxdepth = 7, 4
    if "--workers" in args:
        i = args.index("--workers"); workers = int(args[i + 1])
    if "--maxdepth" in args:
        i = args.index("--maxdepth"); maxdepth = int(args[i + 1])
    jobs = initial_jobs()
    done = []
    logf = open(os.path.join(HERE, "extend.log"), "a")

    def log(s):
        print(s, flush=True); logf.write(s + "\n"); logf.flush()
    t0 = time.time()
    log(f"start {time.strftime('%H:%M:%S')} boxes={len(jobs)} workers={workers} maxdepth={maxdepth}")
    with Pool(workers) as pool:
        while jobs:
            nxt = []
            for r in pool.imap_unordered(work, jobs):
                if r["status"] in ("open", "error") and r["depth"] < maxdepth:
                    a0, a1 = Fr(r["alpha"][0]), Fr(r["alpha"][1])
                    b0, b1 = Fr(r["beta"][0]), Fr(r["beta"][1])
                    am, bm = (a0 + a1) / 2, (b0 + b1) / 2
                    nxt += [(str(x0), str(x1), str(y0), str(y1), r["nu"], r["depth"] + 1)
                            for x0, x1 in ((a0, am), (am, a1)) for y0, y1 in ((b0, bm), (bm, b1))]
                else:
                    if r["status"] in ("open", "error"):
                        r["final"] = "unresolved"
                    done.append(r)
            json.dump(done, open(os.path.join(HERE, "extend.json"), "w"), indent=0)
            log(f"  {time.time() - t0:7.0f}s level done; {len(done)} final, next level {len(nxt)} boxes")
            jobs = nxt
    by = {}
    for r in done:
        d = by.setdefault(r["nu"], {"certified": 0, "invalid": {}, "unresolved": 0, "min": None})
        if r["status"] == "certified":
            d["certified"] += 1
            d["min"] = r["floor_lo"] if d["min"] is None else min(d["min"], r["floor_lo"])
        elif r["status"] == "invalid":
            d["invalid"][r["why"]] = d["invalid"].get(r["why"], 0) + 1
        if r.get("final") == "unresolved":
            d["unresolved"] += 1
    for nu in sorted(by):
        d = by[nu]
        log(f"nu={nu}: {d['certified']} certified (min {d['min'] if d['min'] is None else round(d['min'], 4)}), invalid {d['invalid']}, unresolved {d['unresolved']}")
    log(f"end {time.strftime('%H:%M:%S')} total {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
