#!/usr/bin/env python3
"""check_step_bound.py -- the explicit step bound for generic (alpha, beta, nu) against the scan (lane W, #108).

Claude Opus 5.5 (Claude Code, [team machine]), for [team member], Sun 15 Nov 2026. EVENT WORK. No human check.
Bound (README): Theta*(s+2) - Theta*(s) >= 2 beta/3 - ((a - (s-1)/6)_+)^2/(s-1),  a = 2 beta - 1 + nu alpha.
Part 1 (fast): the step 5 -> 7 at every admissible scan point with alpha < 1/6 and a < 2, using the stored A* values
           of ../scope_alpha_beta/out/scan_*.json (read-only; floats).
Part 2 (slow, about 3 min): the step 7 -> 9 at 41 points spread over a, computing A*(9) with ../scope_alpha_beta/pkg_ab.py
           (imported unchanged; float tail, 1500 periods). Points outside the s = 9 validity region are counted, not used.
COMPUTED (floating point; not interval arithmetic). Usage: python3 -B check_step_bound.py [fast] -> out/check.log
"""
import json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
SA = os.path.join(HERE, "..", "scope_alpha_beta")
sys.path.insert(0, SA)

def bound(s, be, a):
    return 2 * be / 3 - max(0.0, a - (s - 1) / 6) ** 2 / (s - 1)

def main():
    rows = {}
    for f in ["scan_coarse.json", "scan_lowbeta.json", "scan_fine.json", "scan_fine2.json"]:
        for r in json.load(open(os.path.join(SA, "out", f))):
            rows[(r["alpha"], r["beta"], r["nu"])] = r
    cells = [r for r in rows.values() if r.get("admissible") and "A7" in r and F(r["alpha"]) < F(1, 6)]
    out = []
    n = viol = skip = 0; worst = None; ratios = []
    for r in cells:
        al, be, nu = float(F(r["alpha"])), float(F(r["beta"])), r["nu"]
        a = 2 * be - 1 + nu * al
        if a >= 2: skip += 1; continue
        st = r["A7"] - r["A5"]; b = bound(5, be, a); n += 1; ratios.append(b / st)
        if b <= 0: out.append(f"  NONPOSITIVE bound at {r['alpha']},{r['beta']},{nu}")
        if st < b - 1e-12: viol += 1
        if worst is None or st - b < worst[0]: worst = (st - b, (r["alpha"], r["beta"], nu), st, b)
    out.append(f"5->7: {n} admissible points (alpha < 1/6, a < 2), {skip} with a >= 2 skipped; violations {viol}")
    out.append(f"  tightest {worst[1]}: step {worst[2]:.6f}, bound {worst[3]:.6f}; bound/step in [{min(ratios):.3f}, {max(ratios):.3f}]")
    tpl = rows[("3/40", "37/40", 6)]
    out.append(f"  template (3/40, 37/40, 6): step {tpl['A7'] - tpl['A5']:.6f} (751/768 = {751/768:.6f}), bound {bound(5, 37/40, 1.3):.6f}; "
               f"s >= 7 bound at nu = 10: {bound(7, 37/40, 1.6):.6f} (167/300 = {167/300:.6f})")
    if len(sys.argv) < 2 or sys.argv[1] != "fast":
        import pkg_ab as K
        cells.sort(key=lambda r: 2 * float(F(r["beta"])) - 1 + r["nu"] * float(F(r["alpha"])))
        pick = cells[::max(1, len(cells) // 40)][:40] + [cells[-1]]
        ok = inv = v9 = 0; w9 = None
        for r in pick:
            al, be, nu = F(r["alpha"]), F(r["beta"]), r["nu"]
            try:
                a9 = K.PkgAB(9, nu, al, be).A_star_float(periods=1500)[0]
            except ValueError:
                inv += 1; continue
            ok += 1; st = a9 - r["A7"]; a = float(2 * be - 1 + nu * al); b = bound(7, float(be), a)
            if st < b - 1e-9: v9 += 1
            if w9 is None or st - b < w9[0]: w9 = (st - b, (str(al), str(be), nu), st, b)
        out.append(f"7->9: {ok} sampled points, {inv} outside the s = 9 validity region; violations {v9}")
        out.append(f"  tightest {w9[1]}: step {w9[2]:.6f}, bound {w9[3]:.6f}")
    text = "\n".join(out); print(text)
    open(os.path.join(HERE, "out", "check.log"), "w").write(text + "\n")

if __name__ == "__main__":
    main()
