#!/usr/bin/env python3
"""compare_e29.py -- the free-beta package against E29's exact finite-K exponents (EVENT WORK,
advocate:scope-alpha-beta, Claude Opus 5.5).

Exact side (COMPUTED by advocate:construction-changes, E29, read only): e_H(s) = log Q^prim_H(zeta(s))/K^2 for the
Hankel matrix [mu_X(D_N^6 t^(i+j)/D_K)]_(i,j<H), alpha = 3/40, K = 40, 80, 120, from
../construction/out/beta_table.txt.  By Gauss's lemma every integer normalisation, in particular the package's,
is >= Q^prim, so in the limit K -> oo the package value must lie above lim e_H (finite K carries O(log K / K)).
Package side: A*(s, 6; 3/40, beta) + [LB, U] at beta = H/K (pkg_ab.py, scan.cell).
Prints: per (K, H): beta, e_H(7), package floor/top at s = 7, package - exact; the s-step 5 -> 7 exact vs package
(U-free, exact rational); and slopes d/d beta (finite differences) of e_H(7) and of the package floor.
Output: out/compare_e29.log, out/compare_e29.json
"""
import json
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import scan  # noqa: E402

LOG = []


def log(s=""):
    print(s, flush=True)
    LOG.append(s)


def read_table():
    rows = {}
    K = None
    for line in open(os.path.join(HERE, "..", "construction", "out", "beta_table.txt")):
        m = re.match(r"n = (\d+) \(K = (\d+)", line)
        if m:
            K = int(m.group(2))
            continue
        p = line.split()
        if len(p) >= 9 and p[0].isdigit():
            H = int(p[0])
            rows[(K, H)] = dict(K=K, H=H, beta=Fr(H, K), e5=float(p[3]), e7=float(p[4]), step=float(p[5]))
    return rows


def main():
    rows = read_table()
    betas = sorted({r["beta"] for r in rows.values()})
    pk = {}
    for b in betas:
        c = scan.cell(("3/40", str(b), 6))
        pk[b] = c
    log("Package (M -> oo, alpha = 3/40, nu = 6) vs exact e_H (E29), zeta(7):")
    log("   K    H    beta   e_H(7) exact   pkg floor7   pkg top7   floor-exact | step exact  step pkg (2b/3+dI_out)")
    out = []
    for (K, H), r in sorted(rows.items()):
        c = pk[r["beta"]]
        if "floor7" not in c:
            log(f"  {K:3d} {H:4d}  {float(r['beta']):.4f}  inadmissible in the package: {c.get('err', c)}")
            continue
        d = c["floor7"] - r["e7"]
        out.append(dict(K=K, H=H, beta=float(r["beta"]), e7=r["e7"], e5=r["e5"], floor7=c["floor7"], top7=c["top7"],
                        floor5=c["floor5"], top5=c["top5"], step_exact=r["step"], step_pkg=c["sstep"]))
        log(f"  {K:3d} {H:4d}  {float(r['beta']):.4f}  {r['e7']:+.6f}     {c['floor7']:+.6f}   {c['top7']:+.6f}   "
            f"{d:+.4f}     | {r['step']:+.4f}     {c['sstep']:+.4f}")
    log("")
    log("Slopes d/d beta between consecutive tabulated H (finite differences):")
    for K in (40, 80, 120):
        rs = [o for o in out if o["K"] == K]
        for a, b in zip(rs, rs[1:]):
            db = b["beta"] - a["beta"]
            log(f"  K={K:3d} beta {a['beta']:.4f}->{b['beta']:.4f}: exact e7 {(b['e7'] - a['e7']) / db:+.3f}  "
                f"pkg floor7 {(b['floor7'] - a['floor7']) / db:+.3f}  | step: exact {(b['step_exact'] - a['step_exact']) / db:+.3f}"
                f"  pkg {(b['step_pkg'] - a['step_pkg']) / db:+.3f}  | zeta5: exact {(b['e5'] - a['e5']) / db:+.3f} "
                f"pkg floor5 {(b['floor5'] - a['floor5']) / db:+.3f}")
    json.dump(out, open(os.path.join(HERE, "out", "compare_e29.json"), "w"), indent=1)
    open(os.path.join(HERE, "out", "compare_e29.log"), "w").write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
