#!/usr/bin/env python3
"""analyze.py -- floors over (alpha, beta) from scan_*.json, and the figure out/floor_alpha_beta.svg
(EVENT WORK, advocate:scope-alpha-beta, Claude Opus 5.5).

floor7(alpha, beta) = min over admissible even nu <= 10 of A*(7) + LB  (float scan values; the decisive cells are
certified separately by certify_min.py).  'valid' = alpha < 1/6 (the derivation's outer range needs 2N < p);
'admissible' = La >= 0 and z_beta >= 0 (pkg_ab).  zeta(5): best bracket over the same cells, with the extra
condition 2 beta + nu alpha - 1 < 2 (no polynomial correction for p > K at s = 5).
Usage: python3 analyze.py scan_coarse.json [scan_fine.json ...] -> out/analysis.log, out/floor_alpha_beta.svg,
       out/decisive_cells.json
"""
import json
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
LOG = []


def log(s=""):
    print(s, flush=True)
    LOG.append(s)


def load(names):
    rows = {}
    for n in names:
        for r in json.load(open(os.path.join(OUT, n))):
            rows[(r["alpha"], r["beta"], r["nu"])] = r
    return list(rows.values())


def table(rows, key="floor7", s5=False):
    T = {}
    for r in rows:
        if not r.get("admissible") or key not in r:
            continue
        al, be, nu = Fr(r["alpha"]), Fr(r["beta"]), r["nu"]
        if s5 and not (2 * be + nu * al - 1 < 2):
            continue
        k = (al, be)
        if k not in T or r[key] < T[k][0]:
            T[k] = (r[key], nu, r)
    return T


def svg(T, rows, path, mincell, romik=0.84):
    als = sorted({Fr(r["alpha"]) for r in rows})
    bes = sorted({Fr(r["beta"]) for r in rows})
    W, Hh = 1180, 560
    computed = {(Fr(r["alpha"]), Fr(r["beta"])) for r in rows}
    ml, mt, pw, ph = 80, 60, 520, 400
    cw, ch = pw / len(bes), ph / len(als)
    vals = [v[0] for v in T.values()]
    lo, hi = min(vals), max(vals)

    def col(v):
        u = (v - lo) / (hi - lo) if hi > lo else 0
        r = int(255 * (0.15 + 0.85 * u))
        g = int(255 * (0.35 + 0.45 * (1 - abs(2 * u - 1))))
        b = int(255 * (0.95 - 0.8 * u))
        return f"rgb({r},{g},{b})"
    el = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{Hh}" font-family="Helvetica,Arial" font-size="12">',
          '<rect width="100%" height="100%" fill="white"/>',
          f'<text x="{ml}" y="24" font-size="15" font-weight="bold">zeta(7) dual floor min over even nu &lt;= 10 of '
          f'A*(7,nu;alpha,beta) + LB(nu;alpha,beta), M -&gt; oo</text>',
          f'<text x="{ml}" y="42" font-size="11">beta = H/K free (derivation_beta.md, PROOF-DRAFT). grey: inadmissible (La &lt; 0 or '
          f'z_beta &lt; 0 for every even nu); white: not computed; hatched: alpha &gt;= 1/6 (not derived); circles: template beta = 1 - alpha; '
          f'box: minimum</text>']
    el.append('<defs><pattern id="h" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">'
              '<line x1="0" y1="0" x2="0" y2="6" stroke="black" stroke-width="1"/></pattern></defs>')
    for i, al in enumerate(als):
        y = mt + (len(als) - 1 - i) * ch
        for j, be in enumerate(bes):
            x = ml + j * cw
            v = T.get((al, be))
            fill = col(v[0]) if v else ("#cccccc" if (al, be) in computed else "#ffffff")
            el.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{cw:.1f}" height="{ch:.1f}" fill="{fill}" stroke="white" '
                      f'stroke-width="0.5"/>')
            if v and len(bes) <= 24:
                el.append(f'<text x="{x + cw / 2:.1f}" y="{y + ch / 2 + 3:.1f}" text-anchor="middle" font-size="7.5">'
                          f'{v[0]:.3f}</text>')
            if al >= Fr(1, 6):
                el.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{cw:.1f}" height="{ch:.1f}" fill="url(#h)" opacity="0.35"/>')
            if mincell and (al, be) == mincell:
                el.append(f'<rect x="{x + 1:.1f}" y="{y + 1:.1f}" width="{cw - 2:.1f}" height="{ch - 2:.1f}" fill="none" '
                          f'stroke="black" stroke-width="2.5"/>')
        el.append(f'<text x="{ml - 6}" y="{y + ch / 2 + 4:.1f}" text-anchor="end">{al}</text>')
    for j, be in enumerate(bes):
        if j % 4 == 0:
            el.append(f'<text x="{ml + j * cw + cw / 2:.1f}" y="{mt + ph + 16}" text-anchor="middle" font-size="10">'
                      f'{float(be):.3f}</text>')
    el.append(f'<text x="{ml + pw / 2}" y="{mt + ph + 36}" text-anchor="middle">beta = H/K (Hankel size); '
              f'the published template is beta = 1 - alpha</text>')
    el.append(f'<text x="20" y="{mt + ph / 2}" transform="rotate(-90 20 {mt + ph / 2})" text-anchor="middle">'
              f'alpha = N/K</text>')
    for i, al in enumerate(als):            # the template line beta = 1 - alpha
        be = 1 - al
        if be in bes:
            j = bes.index(be)
            x = ml + j * cw + cw / 2
            y = mt + (len(als) - 1 - i) * ch + ch / 2
            el.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3" fill="none" stroke="black"/>')
    # colour bar
    for k in range(50):
        v = lo + (hi - lo) * k / 49
        el.append(f'<rect x="{ml + pw + 20}" y="{mt + ph - (k + 1) * ph / 50:.1f}" width="14" height="{ph / 50 + 0.5:.1f}" '
                  f'fill="{col(v)}"/>')
    el.append(f'<text x="{ml + pw + 38}" y="{mt + ph}" font-size="10">{lo:+.3f}</text>')
    el.append(f'<text x="{ml + pw + 38}" y="{mt + 8}" font-size="10">{hi:+.3f}</text>')
    # right panel: floor vs beta per alpha
    px, py, pw2, ph2 = ml + pw + 110, mt + 20, 250, 360
    vmin, vmax = min(min(vals), 0.8), min(max(vals), 1.3)

    def X(b):
        return px + (float(b) - float(bes[0])) / (float(bes[-1]) - float(bes[0])) * pw2

    def Y(v):
        return py + (vmax - v) / (vmax - vmin) * ph2
    el.append(f'<rect x="{px}" y="{py}" width="{pw2}" height="{ph2}" fill="none" stroke="#999"/>')
    for v in (0.8, 0.84, 0.9, 1.0, 1.1, 1.2):
        if vmin <= v <= vmax:
            el.append(f'<line x1="{px}" x2="{px + pw2}" y1="{Y(v):.1f}" y2="{Y(v):.1f}" stroke="{"#d00" if v in (0.8, 0.84) else "#eee"}"'
                      f' stroke-dasharray="{"4,3" if v in (0.8, 0.84) else ""}"/>'
                      f'<text x="{px - 4}" y="{Y(v) + 4:.1f}" text-anchor="end" font-size="10">{v:.2f}</text>')
    el.append(f'<text x="{px + pw2 - 2}" y="{Y(0.84) - 3:.1f}" text-anchor="end" font-size="9" fill="#d00">'
              f'Romik audit p. 20: +0.84</text>')
    palette = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b", "#e377c2", "#7f7f7f", "#17becf"]
    for i, al in enumerate(als):
        pts = sorted((be, T[(al, be)][0]) for be in bes if (al, be) in T)
        if len(pts) < 2:
            continue
        dash = ' stroke-dasharray="5,3"' if al >= Fr(1, 6) else ""
        el.append(f'<polyline fill="none" stroke="{palette[i % 9]}" stroke-width="1.6"{dash} points="'
                  + " ".join(f"{X(b):.1f},{Y(min(max(v, vmin), vmax)):.1f}" for b, v in pts) + '"/>')
        el.append(f'<text x="{px + pw2 + 4}" y="{py + 14 + 14 * i}" font-size="10" fill="{palette[i % 9]}">alpha={al}</text>')
    el.append(f'<text x="{px + pw2 / 2}" y="{py + ph2 + 18}" text-anchor="middle" font-size="10">beta</text>')
    el.append(f'<text x="{px}" y="{py - 6}" font-size="11">floor vs beta (dashed: alpha &gt;= 1/6, not derived)</text>')
    el.append("</svg>")
    open(path, "w").write("\n".join(el))


def main():
    names = sys.argv[1:] or ["scan_coarse.json"]
    rows = load(names)
    log(f"cells: {len(rows)}; admissible: {sum(1 for r in rows if r.get('admissible'))}")
    T = table(rows)
    valid = {k: v for k, v in T.items() if k[0] < Fr(1, 6)}
    (al0, be0), (v0, nu0, r0) = min(valid.items(), key=lambda kv: kv[1][0])
    log(f"zeta(7) dual floor, valid region (alpha < 1/6, admissible): min = {v0:+.6f} at alpha = {al0}, beta = {be0}, "
        f"nu = {nu0}  (top {r0['top7']:+.6f}; A*(7) = {r0['A7']:.6f}, LB = {r0['LB']:+.6f})")
    inv = {k: v for k, v in T.items() if k[0] >= Fr(1, 6)}
    if inv:
        (al1, be1), (v1, nu1, r1) = min(inv.items(), key=lambda kv: kv[1][0])
        log(f"  outside the derivation (alpha >= 1/6, formula continuation only): min = {v1:+.6f} at alpha = {al1}, "
            f"beta = {be1}, nu = {nu1}")
    below = sorted((v[0], k) for k, v in valid.items() if v[0] < 0.84)
    log(f"  valid cells with floor < +0.84: {len(below)}; with floor < +0.80: {sum(1 for v, _ in below if v < 0.8)}")
    for al in sorted({k[0] for k in T}):
        line = sorted((k[1], v) for k, v in T.items() if k[0] == al)
        if not line:
            continue
        bm, vm = min(line, key=lambda z: z[1][0])
        tl = T.get((al, 1 - al))
        log(f"  alpha={str(al):5s}: beta range [{float(line[0][0]):.4f}, {float(line[-1][0]):.4f}] admissible; "
            f"min floor {vm[0]:+.5f} at beta={bm} (nu={vm[1]}); at template beta=1-alpha: "
            f"{(f'{tl[0]:+.5f} (nu={tl[1]})' if tl else 'n/a')}; gain {((tl[0] - vm[0]) if tl else float('nan')):+.5f}")
    # zeta(5)
    T5 = table(rows, "floor5", s5=True)
    T5top = table(rows, "top5", s5=True)
    v5 = {k: v for k, v in T5top.items() if k[0] < Fr(1, 6)}
    (a5, b5), (u5, n5, r5) = min(v5.items(), key=lambda kv: kv[1][0])
    log(f"zeta(5) calibration (valid region): best upper end A*(5) + U = {u5:+.6f} at alpha = {a5}, beta = {b5}, "
        f"nu = {n5} (lower end there {r5['floor5']:+.6f}; U is a float-grid HEURISTIC value)")
    f5 = {k: v for k, v in T5.items() if k[0] < Fr(1, 6)}
    (a6, b6), (l6, n6, r6) = min(f5.items(), key=lambda kv: kv[1][0])
    log(f"  most negative lower end A*(5) + LB = {l6:+.6f} at alpha = {a6}, beta = {b6}, nu = {n6}; at Fauzan's "
        f"(3/40, 37/40, 6): [{T5.get((Fr(3, 40), Fr(37, 40)), (float('nan'),))[0]:+.6f}, ...]")
    svg(T, rows, os.path.join(OUT, "floor_alpha_beta.svg"), (al0, be0))
    # decisive cells: the valid minimum, its neighbours, and each alpha's minimum
    dec = [[str(al0), str(be0), nu0]]
    for al in sorted({k[0] for k in valid}):
        line = [(k[1], v) for k, v in valid.items() if k[0] == al]
        bm, vm = min(line, key=lambda z: z[1][0])
        c = [str(al), str(bm), vm[1]]
        if c not in dec:
            dec.append(c)
    json.dump(dec, open(os.path.join(OUT, "decisive_cells.json"), "w"))
    log(f"decisive cells -> out/decisive_cells.json: {dec}")
    open(os.path.join(OUT, "analysis.log"), "w").write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
