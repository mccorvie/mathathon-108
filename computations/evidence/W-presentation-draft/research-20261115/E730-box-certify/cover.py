#!/usr/bin/env python3
"""[108/N E730] Branch and bound: cover alpha in [0, 1/6] x beta in [0, 2] for each even nu <= 10 (COMPUTED).

Each box ends as 'certified' (box2.floor_box lower bound > 0), 'invalid' (condition (iii) fails on the whole box, or the
outer saturation z_beta >= 0 fails at every point of it), or is split into four (also when it raised an error, which is
recorded), up to MAXDEPTH levels; boxes still open or failing at the last level are reported as 'unresolved'. Results: cover-nu<nu>.json and cover.log.
Usage: cover.py [nu ...] [--workers 11] [--maxdepth 6] [--la]
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

NA, NB = 8, 40                     # initial grid: alpha step 1/48, beta step 1/20
A_MAX, B_MAX = Fr(1, 6), Fr(2)


def la3_fails(a0, a1, b0, b1, nu):
    """True if condition (i) L_a >= 0 fails at x = 3 at every point of the box with alpha > 0 (PROOF-DRAFT; Lean
    E730.la3_neg_of_le and E730.ell_half). L_a(3) = floor(6 beta + 3 nu alpha - 21/20) + 1 - (nu/2) lmax(3 alpha), and
    lmax(3 alpha) = 1 for 0 < alpha < 1/6, so L_a(3) <= floor(6 b1 + 3 nu a1 - 21/20) + 1 - nu/2 on the box (floor is
    monotone). The line alpha = 0 is not covered by this test (there lmax(0) = 0); the package there does not depend on nu."""
    a1, b1 = Fr(a1), Fr(b1)
    return a1 <= Fr(1, 6) and math.floor(6 * b1 + 3 * nu * a1 - Fr(21, 20)) + 1 - Fr(nu, 2) < 0


def work(job):
    a0, a1, b0, b1, nu, depth = job
    import box2 as B2
    t0 = time.time()
    if os.environ.get("E730_LA_TEST") == "1" and la3_fails(a0, a1, b0, b1, nu):
        r = {"status": "invalid", "why": "La(x=3), alpha > 0"}
        r.update(alpha=[str(a0), str(a1)], beta=[str(b0), str(b1)], nu=nu, depth=depth, seconds=0.0)
        return r
    try:
        r = B2.floor_box(a0, a1, b0, b1, nu)
    except Exception as e:  # recorded, never hidden
        r = {"status": "error", "error": f"{type(e).__name__}: {e}"}
    r.update(alpha=[str(a0), str(a1)], beta=[str(b0), str(b1)], nu=nu, depth=depth, seconds=round(time.time() - t0, 2))
    return r


def main():
    args = sys.argv[1:]
    workers, maxdepth = 11, 6
    if "--workers" in args:
        i = args.index("--workers"); workers = int(args[i + 1]); del args[i:i + 2]
    if "--maxdepth" in args:
        i = args.index("--maxdepth"); maxdepth = int(args[i + 1]); del args[i:i + 2]
    if "--la" in args:   # also mark boxes invalid where condition (i) fails at x = 3 (used for nu >= 12)
        args.remove("--la"); os.environ["E730_LA_TEST"] = "1"
    nus = [int(x) for x in args] or [2, 4, 6, 8, 10]
    logf = open(os.path.join(HERE, "cover.log"), "a")

    def log(s):
        print(s, flush=True); logf.write(s + "\n"); logf.flush()
    jobs = [(A_MAX * i / NA, A_MAX * (i + 1) / NA, B_MAX * j / NB, B_MAX * (j + 1) / NB, nu, 0)
            for nu in nus for i in range(NA) for j in range(NB)]
    done = {nu: [] for nu in nus}
    t0 = time.time()
    log(f"start {time.strftime('%H:%M:%S')} nus={nus} boxes={len(jobs)} workers={workers} maxdepth={maxdepth}")
    with Pool(workers) as pool:
        while jobs:
            nxt = []
            for r in pool.imap_unordered(work, jobs):
                st, nu, d = r["status"], r["nu"], r["depth"]
                if st in ("open", "error") and d < maxdepth:
                    a0, a1 = Fr(r["alpha"][0]), Fr(r["alpha"][1])
                    b0, b1 = Fr(r["beta"][0]), Fr(r["beta"][1])
                    am, bm = (a0 + a1) / 2, (b0 + b1) / 2
                    nxt += [(x0, x1, y0, y1, nu, d + 1) for x0, x1 in ((a0, am), (am, a1)) for y0, y1 in ((b0, bm), (bm, b1))]
                else:
                    if st in ("open", "error"):
                        r["final"] = "unresolved"
                    done[nu].append(r)
            for nu in nus:
                json.dump(done[nu], open(os.path.join(HERE, f"cover-nu{nu}.json"), "w"), indent=0)
            log(f"  {time.time() - t0:7.0f}s level done; next level {len(nxt)} boxes; "
                + "; ".join(f"nu={nu}: {sum(1 for r in done[nu] if r['status'] == 'certified')} cert, "
                            f"{sum(1 for r in done[nu] if r['status'] == 'invalid')} inval, "
                            f"{sum(1 for r in done[nu] if r.get('final') == 'unresolved')} unres" for nu in nus))
            jobs = nxt
    for nu in nus:
        cert = [r for r in done[nu] if r["status"] == "certified"]
        unres = [r for r in done[nu] if r.get("final") == "unresolved"]
        area = sum((Fr(r["alpha"][1]) - Fr(r["alpha"][0])) * (Fr(r["beta"][1]) - Fr(r["beta"][0])) for r in done[nu])
        log(f"nu={nu}: {len(cert)} certified (min floor lower bound {min(r['floor_lo'] for r in cert):.4f}), "
            f"{sum(1 for r in done[nu] if r['status'] == 'invalid')} invalid, {len(unres)} unresolved; covered area {float(area):.6f} "
            f"of {float(A_MAX * B_MAX):.6f}")
    log(f"end {time.strftime('%H:%M:%S')} total {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
