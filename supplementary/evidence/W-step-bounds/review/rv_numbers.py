#!/usr/bin/env python3
"""rv_numbers.py -- skeptic review of ../README.md, task 4 (the numbers).  Own code (rv_core.py) + pkg_ab (read-only)
+ the team scan files ../../scope_alpha_beta/out/scan_*.json (read-only).
Usage: python3 -B rv_numbers.py   -> prints a log (tee it to rv_numbers.out)
"""
import glob
import json
import os
import statistics
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
SAB = os.path.join(HERE, "..", "..", "scope_alpha_beta")
sys.path.insert(1, SAB)
import pkg_ab as PA  # noqa: E402
import rv_core as C  # noqa: E402

t0 = time.time()
AL, BE = Fr(3, 40), Fr(37, 40)

# ------------------------------------------------------------------ 1. the Values table
print("1. Values table at (3/40, 37/40, nu), step 5 -> 7")
claimed = {6: ("1991/2400", "751/768", "191/180"), 8: ("3817/4800", "12817/14400", "191/180"),
           10: ("43609/57600", "92111/115200", "191/180"), 2: ("2129/2400", "9929/9600", "191/180")}
for nu in (6, 8, 10, 2):
    lo, up = C.lower(5, nu, AL, BE), C.upper(BE)
    true = 2 * BE / 3 + PA.PkgAB(7, nu, AL, BE).I_out() - PA.PkgAB(5, nu, AL, BE).I_out()
    own = 2 * BE / 3 + C.step_outer(5, nu, AL, BE)
    cl = claimed[nu]
    ok = (str(lo), str(true), str(up)) == cl and own == true
    dom = C.in_domain(5, nu, AL, BE)[0]
    print(f"   nu={nu:2d}: lower {lo} ({float(lo):.4f})  true {true} ({float(true):.4f})  upper {up} ({float(up):.4f})"
          f"  own==pkg {own == true}  in domain {dom}  README {cl}  -> {'MATCH' if ok else 'MISMATCH'}"
          f"   [2beta/3 - J_5 = {float(2 * BE / 3 - C.J_closed(5, nu, AL, BE)):.3f}, cf. README's W-generic-step column]")

# ------------------------------------------------------------------ 2. lower end >= 691/800 for s >= 7 at the template
print("\n2. min of the lower bound over odd s = 7..99, nu = 0..10 at (3/40, 37/40)")
best = None
for s in range(7, 100, 2):
    for nu in range(0, 11):
        assert C.in_domain(s, nu, AL, BE)[0]
        lo = C.lower(s, nu, AL, BE)
        if best is None or lo < best[0]:
            best = (lo, s, nu)
print(f"   min = {best[0]} = {float(best[0]):.6f} at s={best[1]}, nu={best[2]};  == 691/800: {best[0] == Fr(691, 800)}"
      f";  > 167/300: {best[0] > Fr(167, 300)}")
best39 = min((C.lower(s, nu, AL, BE), s, nu) for s in range(7, 40, 2) for nu in range(11))
print(f"   restricted to s = 7..39: min = {best39[0]} at s={best39[1]}, nu={best39[2]}")
js = [(s, max(C.J_closed(s, nu, AL, BE) for nu in range(11))) for s in (7, 9, 11, 13)]
print("   max_nu J_s for s = 7, 9, 11, 13:", [(s, str(j)) for s, j in js], "(J_s = 0 from s = 11: the range s <= 39 is enough)")
# the true steps there, for comparison
tmin = min((2 * BE / 3 + PA.PkgAB(s + 2, nu, AL, BE).I_out() - PA.PkgAB(s, nu, AL, BE).I_out(), s, nu)
           for s in (7, 9, 11) for nu in range(11))
print(f"   true step min over s = 7, 9, 11 and nu = 0..10: {tmin[0]} ({float(tmin[0]):.6f}) at s={tmin[1]}, nu={tmin[2]}")

# ------------------------------------------------------------------ 3. the scan's exact data
print("\n3. bounds at the team scan's exact steps (2 beta/3 + I_out7 - I_out5)")
rows = {}
nfile = {}
for f in sorted(glob.glob(os.path.join(SAB, "out", "scan_*.json"))):
    d = json.load(open(f))
    nfile[os.path.basename(f)] = len(d)
    for r in d:
        key = (r["alpha"], r["beta"], r["nu"])
        if "I_out5" in r:
            r["_file"] = os.path.basename(f) if key not in rows else rows[key]["_file"] if rows[key]["_file"] in ("scan_coarse.json", "scan_fine.json") else os.path.basename(f)
            if key in rows and (rows[key]["I_out5"], rows[key]["I_out7"]) != (r["I_out5"], r["I_out7"]):
                print("   duplicate with different values:", key)
            rows[key] = r
print("   files:", nfile, " distinct rows with I_out:", len(rows))
cells = []
for (a, b, nu), r in rows.items():
    al, be = Fr(a), Fr(b)
    A = 2 * be - 1 + nu * al
    if al < Fr(1, 6) and A < 2:
        cells.append((al, be, nu, r))
print(f"   cells with alpha < 1/6 and A < 2: {len(cells)} (README/report: 651)")
nadm = sum(1 for c in cells if c[3]["admissible"])
neven = sum(1 for c in cells if c[2] % 2 == 0 and c[2] <= 10)
nla = sum(1 for c in cells if Fr(c[3]["La_min"]) >= 0)
print(f"   of these: scan 'admissible' (La >= 0 and z >= 0) {nadm}; La_min >= 0: {nla}; even nu <= 10: {neven}; "
      f"La < 0 (not in the derived region): {len(cells) - nla}")
nlo = nup = 0
ratios = []
sdiff = 0.0
fdiff = 0.0
own_mis = 0
dom_bad = 0
for i, (al, be, nu, r) in enumerate(cells):
    step = 2 * be / 3 + Fr(r["I_out7"]) - Fr(r["I_out5"])
    lo, up = C.lower(5, nu, al, be), C.upper(be)
    if not lo <= step:
        nlo += 1
    if not step <= up:
        nup += 1
    ratios.append(float(lo / step))
    sdiff = max(sdiff, abs(float(step) - r["sstep"]))
    fdiff = max(fdiff, abs((r["floor7"] - r["floor5"]) - float(step)))
    if not C.in_domain(5, nu, al, be)[0]:
        dom_bad += 1
    if i % 5 == 0 and 2 * be / 3 + C.step_outer(5, nu, al, be) != step:   # own recomputation on every 5th cell
        own_mis += 1
ratios.sort()
print(f"   lower violations {nlo}, upper violations {nup};  cells outside the README domain (own zmin, (iii)): {dom_bad}")
print(f"   own step != scan step on every 5th cell: {own_mis} of {len(range(0, len(cells), 5))}")
print(f"   lower/true: min {ratios[0]:.4f}  median {statistics.median(ratios):.4f}  max {ratios[-1]:.4f}"
      f"   (README: 0.612-0.996, median 0.842)")
print(f"   max |exact step - row sstep| = {sdiff:.2e};  max |(floor7 - floor5) - step| = {fdiff:.2e}"
      "  (the scan's floor7 is BUILT as floor5 + step: A7 = A5 + dI_out + 2 beta/3)")

# ------------------------------------------------------------------ 4. the zeta(5) side
print("\n4. zeta(5) side on the same cells (floor5 = A*(5) + LB, float, from the scan rows)")


def stats(cs, label):
    f5 = min(cs, key=lambda c: c[3]["floor5"])
    print(f"   [{label}] {len(cs)} cells; min floor5 = {f5[3]['floor5']:+.5f} at ({f5[0]}, {f5[1]}, {f5[2]})")
    close = [c for c in cs if c[3]["floor5"] < 0]
    nus = sorted({c[2] for c in close})
    print(f"      floor5 < 0 at {len(close)} cells, nu in {nus};  top5 < 0 (heuristic achievable U) at "
          f"{sum(1 for c in cs if c[3]['top5'] < 0)} cells")
    if close:
        lo = min(float(C.lower(5, c[2], c[0], c[1])) for c in close)
        st = min(float(2 * c[1] / 3 + Fr(c[3]["I_out7"]) - Fr(c[3]["I_out5"])) for c in close)
        fl = min(c[3]["floor5"] + float(C.lower(5, c[2], c[0], c[1])) for c in close)
        f7 = min(c[3]["floor7"] for c in close)
        print(f"      at those: min lower = {lo:.5f}, min true step = {st:.5f}, min floor5 + lower = {fl:+.5f},"
              f" min floor7 = {f7:+.5f}")
    allfl = min((c[3]["floor5"] + float(C.lower(5, c[2], c[0], c[1])), c) for c in cs)
    print(f"      over ALL these cells: min floor5 + lower = {allfl[0]:+.5f} at ({allfl[1][0]}, {allfl[1][1]}, {allfl[1][2]});"
          f" min floor5 + 7/54 = {f5[3]['floor5'] + 7 / 54:+.5f}; min floor7 = {min(c[3]['floor7'] for c in cs):+.5f}")
    return close


team = [c for c in cells if c[3]["admissible"] and c[3].get("_file") in ("scan_coarse.json", "scan_fine.json")]
stats(team, "team's set: admissible cells of scan_coarse + scan_fine only")
close = stats(cells, "all four scan files: alpha<1/6, A<2, z>=0 (README domain)")
stats([c for c in cells if Fr(c[3]["La_min"]) >= 0], "same, La >= 0 only")
stats([c for c in cells if Fr(c[3]["La_min"]) >= 0 and c[2] % 2 == 0 and c[2] <= 10], "same, La >= 0, even nu <= 10")
nla_close = sum(1 for c in close if Fr(c[3]["La_min"]) < 0)
print(f"   of the floor5 < 0 cells, {nla_close} have La < 0 (outside the derived region)")

# ------------------------------------------------------------------ 5. min_lower claim (README checks table, row 4)
print("\n5. min of the lower bound 5 -> 7 over alpha = k/240 < 1/6, beta = m/80 <= 2, nu = 0..24 (saturation at 5, 7; A < 2)")
glob_min = None
by_nu = {}
npts = 0
for k in range(0, 40):
    al = Fr(k, 240)
    for nu in range(0, 25):
        bstar = -C.zmin(C.Out(7, nu, al, 0))
        for m in range(1, 161):
            be = Fr(m, 80)
            if be < bstar or not (2 * be - 1 + nu * al < 2):
                continue
            npts += 1
            lo = C.lower(5, nu, al, be)
            if nu not in by_nu or lo < by_nu[nu][0]:
                by_nu[nu] = (lo, al, be)
            if glob_min is None or lo < glob_min[0]:
                glob_min = (lo, al, be, nu)
print(f"   {npts} points; global min {float(glob_min[0]):.4f} at ({glob_min[1]}, {glob_min[2]}, {glob_min[3]})")
print(f"   min for nu <= 5: {min(float(by_nu[n][0]) for n in range(6) if n in by_nu):.4f};"
      f"  nu <= 10: {min(float(by_nu[n][0]) for n in range(11) if n in by_nu):.4f}   (README: 0.530, 0.279, 0.2319 at (13/80, 21/80, 15))")
print(f"\n({time.time() - t0:.0f} s)")
