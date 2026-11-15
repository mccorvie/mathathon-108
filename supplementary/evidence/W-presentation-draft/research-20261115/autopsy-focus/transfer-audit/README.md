# Follow-up scoped to the zeta(5) proof and its zeta(7) breakpoint

15 November 2026 UTC. [team member]'s goal governs these two bounded LOCAL Codex
audits: explain the successful proof, identify its failed extension, and
require each experiment to address a named proof obligation. The existing
[proof-chain map](../zeta5-chain.md) and [breakpoint map](../zeta7-breakpoint.md)
remain the detailed explanations of the original method. This folder adds
two checks of how the recent experiments relate to that explanation.

Written deductions are **PROOF-DRAFT**, reportable as CONJECTURE. Fresh
finite calculations are **COMPUTED**. Current report statements below are
**CITED** as repository records; this session ran no Lean gate and upgraded
no claim. The two reviewers share the parent's model family. No novelty or
irrationality result is claimed.

## 1. The main proof chain and the exact lost margin

**CITED — canonical report at `413402a199f410014035f9f7af6f0e97f3cdf667`,
Sections 1.2--1.4 and Claims 1, 2, 3, 5, 8.** The original slice is
`nu=6, K=40n, N=3n, h=37n`. The functional constructs a rational polynomial;
Gram positivity makes its target value nonzero; local valuations construct
an integer polynomial `Q_n=m_n F_n`; degree is at most `37n`.
The real bound and the selected multiplier's limit give the sufficient
closing estimate

\[
\log Q_n(\zeta(s))\le [A_M(s,6)+u+o(1)](40n)^2.
\]

A negative coefficient beats the denominator factor `b^(37n)` under a
hypothetical rational target `a/b`. Construction, positivity, integrality,
and the compact real bound survive at `s=7`; the selected negative closing
margin does not.

**COMPUTED — dependency replay of the selected scalar package.** With the
same compact constant `u=-2678491/2000000` and fixed `M=400`, fresh exact
rational integration using the inherited scalar implementation gives:

| Quantity | At zeta(5) | At zeta(7) |
|---|---:|---:|
| Selected certificate margin `A_400(s,6)+u` | -0.0096825830 | +0.9681820003 |

The decimal entries are rounded displays of saved exact fractions. Their
exact difference is

\[
\frac{751}{768}
=\underbrace{\frac{37}{60}}_{\text{inner and crude-prime cost}}
+\underbrace{\frac{1387}{3840}}_{\text{outer-prime cost}}.
\]

The analytic constant is held fixed. This identifies the arithmetic
budget lost in the selected transfer. These numbers are scalar
certificates, not evaluations or lower bounds for `Q_n(zeta(s))`.
`check_original_step.py` also checks cutoffs 40 and 200 and verifies the
same exact gap there. It reuses `numerical-source-theta.py`, whose local
Git blob `40b3e761c2b4ce777049867c622c49cb0e0455e4` matches the pinned remote
source. It is a replay, not an independent implementation.

**CITED — failure scope.** The canonical report's stronger certificate
floor is `A_M(7,6)>2.29` and `U_opt(rho)>-1.39`, for their stated fixed
slice, allocation, cutoff range and explicit energy class. Thus the
composed certificate exceeds `0.9` within that scope. It remains distinct
from actual primitive-value growth. The original primitive-content/H0/Jensen
programme is owned by the producing lanes and remains conditional.

## 2. The thin lattice experiment changes the test space

**PROOF-DRAFT — source and exact finite evidence in [thin/README.md](thin/README.md).**
For `s` in `{5,7,9}` and `D_N^5/T`, with `T=product_(N<j<=K)(t+j^2)`, the coefficient of `X` in
the k-th moment first appears at

\[
\ell=22n-1-\frac{s-1}{2}.
\]

At the thin size used for the zeta(7) experiment, `h=11n-1`, this gives:

| Zeta index | Rank of the target-coefficient block at this thin size | Consequence |
|---|---:|---|
| 5 | 0 | The moment matrix contains no target variable |
| 7 | 1 | The monic-polynomial test has target coefficient -1 |
| 9 | 2 | The target coefficient depends on the chosen polynomial |

The smallest target-bearing block at `s=5` instead has size `11n` and rank
2. Its determinant has degree 2, using positivity at the target. The full
original block of size `37n` has full target rank at all three indices.
Consequently this thin-space parity effect is separate from the original
proof's arithmetic-margin failure. The integer-p search changes the test
object; its smaller denominators cannot be credited as a scalar saving
for the original full determinant.

## 3. Every repair must pay for its actual degree

**PROOF-DRAFT — full argument and proof-obligation table in [budget/README.md](budget/README.md).**
A sufficient general target is

\[
\frac{\log|Q_n(\xi)|}{\max(1,\deg Q_n)}\longrightarrow-\infty,
\qquad Q_n\in\mathbb Z[X],\quad Q_n(\xi)\ne0.
\]

This exposes exactly what the supporting experiments still owe:

| Experiment | Required closing comparison |
|---|---|
| Thin linear forms | Reduced denominator times positive approximation error tends to zero |
| Extra rational-moment rows | Primitive arithmetic cost is beaten by the proved Schur decay, retaining the joint analytic constant and actual degree `K-N` |
| Quadratic-degree cube family | Primitive content cancellation plus an analytic upper bound gives decay faster than degree `n(n+1)+1` |

For the quadratic family, `exp(-c n^2)` alone would be insufficient: even
the primitive polynomials `X^(n(n+1)+1)` have that smallness at suitable
rational targets. The existing cubic-scale raw **lower** bound proves
failure of the specified quartic-scale coarse multiplier and supplies a
necessary content-cancellation budget. It supplies no cubic analytic upper
bound and no sufficient primitive decay estimate.

These obligations keep the experiments attached to the final step of the
known zeta(5) proof. No additional construction campaign is opened here.

## 4. Source snapshot and reproduction

The current report/ledger snapshot is `413402a199f410014035f9f7af6f0e97f3cdf667`.
Its report records D24, the compact finite real bound for all fixed natural
`s>=2`, in the submitted project, alongside D22 (the zeta5 endpoint), D23
(the criterion), and D12--D14 (normalizer limit and scoped sign results).
The older companion maps explicitly describe their earlier snapshot;
their historical gate caveats should not override the current report's
item-specific labels. This is a source-status distinction, not a fresh
certification by this session.

From this folder:

```sh
python3 check_original_step.py
python3 thin/check.py
```

The scalar replay depends on the inherited exact piecewise integrator.
The thin checker uses fresh standard-library residue/remainder arithmetic,
with its precise finite range and methods recorded in `thin/results.json`.
Neither script evaluates a full determinant at a zeta value or proves an
asymptotic arithmetic estimate. The budget audit is a written logical
check; its cited earlier experiments were not rerun.
