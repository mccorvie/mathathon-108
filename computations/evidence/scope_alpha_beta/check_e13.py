#!/usr/bin/env python3
"""check_e13.py -- exact identity checks for pkg_ab.py (EVENT WORK, advocate:scope-alpha-beta, Claude Opus 5.5).

C1  at beta = lam = 1 - alpha, pkg_ab equals theta.py reading 'S' (E13) EXACTLY: R(x) at 240 rational points in
    [3, 240], T_out(y) at 240 points in (1/3, 2 lam], I_out, int_3^20 R/x^3; alpha = k/40, k = 1..6;
    (s, nu) in {5, 7} x {2, 4, 6, 8, 10}.  theta is evaluated at alpha by setting theta.AL, theta.LAM at run
    time (param_scan/run.py's alpha_ctx method), restored afterwards; theta.py is not edited.
C2  anchors through pkg_ab at (alpha, beta) = (3/40, 37/40): Fauzan I_out(5,6) = 127751/96000 (Fauzan (5.10));
    Lai (103) int_3^20 R/x^3; audit I_out(7,8) = 453803/288000; s-step 751/768 (E14).
C3  Prop. 1' (derivation_beta.md section 2): R = x F_beta + Q exactly, F_beta = (s-1) beta + 2 beta {x} - 2 nu beta {alpha x},
    Q s-free, at 300 points for beta != lam; hence R_(s+2) - R_s = 2 beta x and the mean slope is (s - nu) beta.
C4  the U-free s-step at free beta: Theta(7) - Theta(5) = 2 beta/3 + I_out(7) - I_out(5) (exact) for a beta row.
Output: out/check_e13.log (ALL PASS line).
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pkg_ab as PA  # noqa: E402
TH = PA.TH
LOG = []


def log(s=""):
    print(s, flush=True)
    LOG.append(s)


class alpha_ctx:
    def __init__(self, al):
        self.al = Fr(al)

    def __enter__(self):
        self.old = (TH.AL, TH.LAM)
        TH.AL, TH.LAM = self.al, 1 - self.al

    def __exit__(self, *a):
        TH.AL, TH.LAM = self.old


def pts_x():
    return [Fr(3) + Fr(237 * k, 240) + Fr(1, 7919) for k in range(240)]


def pts_y(top):
    return [Fr(1, 3) + (top - Fr(1, 3)) * Fr(k, 240) + Fr(1, 104729) for k in range(240)]


def main():
    ok_all = True
    log("C1  beta = lam: pkg_ab == theta reading S (exact)")
    for k in range(1, 7):
        al = Fr(k, 40)
        lam = 1 - al
        with alpha_ctx(al):
            for s in (5, 7):
                for nu in (2, 4, 6, 8, 10):
                    A = PA.PkgAB(s, nu, al, lam)
                    B = TH.Pkg(s, nu, "S")
                    okR = all(A.R(x) == B.R(x) for x in pts_x())
                    okT = all(A.Tout(y) == B.Tout(y) for y in pts_y(2 * lam) if y <= 2 * lam)
                    io_a, io_b = A.I_out(), TH.I_out(B)
                    i_a, i_b = A.int_R_x3(3, 20), TH.int_R_x3(B, 3, 20)
                    ok = okR and okT and io_a == io_b and i_a == i_b
                    ok_all &= ok
                    log(f"  alpha={str(al):5s} s={s} nu={nu:2d}: R {okR} Tout {okT} I_out {io_a == io_b} "
                        f"({float(io_a):.10f}) int_3^20 {i_a == i_b}  -> {'PASS' if ok else 'FAIL'}")
    log("C2  anchors at (3/40, 37/40) through pkg_ab")
    al, be = Fr(3, 40), Fr(37, 40)
    P56, P76, P78 = PA.PkgAB(5, 6, al, be), PA.PkgAB(7, 6, al, be), PA.PkgAB(7, 8, al, be)
    c = [P56.I_out() == Fr(127751, 96000),
         P56.int_R_x3(3, 20) == Fr(322437603634266857629, 7535670527041937280000),
         P78.I_out() == Fr(453803, 288000)]
    st = (P76.I_out() + P76.int_R_x3(3, 40) + P76.c_cr * be / 40) - (P56.I_out() + P56.int_R_x3(3, 40) +
                                                                       P56.c_cr * be / 40)
    c.append(st == Fr(751, 768))
    log(f"  I_out(5,6) = 127751/96000: {c[0]};  Lai (103): {c[1]};  I_out(7,8) = 453803/288000: {c[2]};  "
        f"A_40(7,6) - A_40(5,6) = {st} == 751/768: {c[3]}")
    ok_all &= all(c)
    log("C3  Prop. 1': R = x F_beta + Q (exact), beta != lam")
    n = 0
    okp = True
    for al in (Fr(2, 40), Fr(3, 40), Fr(5, 40)):
        for be in (Fr(56, 80), Fr(68, 80), Fr(77, 80), Fr(88, 80)):
            for nu in (2, 6, 10):
                for s in (5, 7):
                    A = PA.PkgAB(s, nu, al, be)
                    for x in [Fr(3) + Fr(97 * j, 25) + Fr(1, 6007) for j in range(25)]:
                        n += 1
                        okp &= A.R(x) == x * A.F(x) + A.Q(x)
                    B = PA.PkgAB(s + 2, nu, al, be)
                    okp &= all(B.R(x) - A.R(x) == 2 * be * x for x in [Fr(3) + Fr(j, 3) + Fr(1, 101) for j in range(30)])
    log(f"  {n} points, and R_(s+2) - R_s = 2 beta x at 30 points per row: {'PASS' if okp else 'FAIL'}")
    ok_all &= okp
    log("C4  U-free s-step at free beta (alpha = 3/40, nu = 6): 2 beta/3 + Delta I_out, exact")
    for be in (Fr(68, 80), Fr(74, 80), Fr(80, 80)):
        A5, A7 = PA.PkgAB(5, 6, Fr(3, 40), be), PA.PkgAB(7, 6, Fr(3, 40), be)
        d40 = (A7.I_out() + A7.int_R_x3(3, 40) + A7.c_cr * be / 40) - (A5.I_out() + A5.int_R_x3(3, 40) + A5.c_cr * be / 40)
        form = 2 * be / 3 + A7.I_out() - A5.I_out()
        okc = d40 == form
        ok_all &= okc
        log(f"  beta={be}: Theta_40(7) - Theta_40(5) = {d40} = {float(d40):.6f}  == 2beta/3 + dI_out: {okc}")
    log(f"ALL PASS: {ok_all}")
    open(os.path.join(HERE, "out", "check_e13.log"), "w").write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
