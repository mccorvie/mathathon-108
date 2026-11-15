# Deeper follow-up: actual constructions and matched cost questions

15 November 2026 UTC. [team member] requested a deeper investigation of superlinear-degree polynomials with stronger analytic bounds. Three local Codex agents resumed their distinct tasks; the parent supplied additional constructions, reviewed the written proofs, and reran the checks. **No Open Math OS worker ran.** These are research inputs, not another paper or a change to the frozen submission spine. No deck, speaker notes, report, Lean source, mathematical label or novelty verdict was changed.

New deductions are **PROOF-DRAFT** (report label CONJECTURE). Finite exact calculations are **COMPUTED**. Classical ingredients are cited in the individual notes. Same-family review and finite checks are not human approval, a cross-family receipt, or a Lean gate.

[team member]'s subsequent [scope clarification](../../autopsy-focus/README.md) keeps the project centered on explaining the zeta(5) proof and locating its zeta(7) failure. These experiments are diagnostic support for named proof steps. They are not a replacement main story or an ongoing search for alternative constructions without that connection.

## What is now concrete

| Direction | Written result | Remaining question |
|---|---|---|
| Extra rational-moment rows | Explicit all-size raw bound \(\det S_q(\zeta(s))\le Cq^{-4r(N+1)}\), \(r=K-N\), with joint constant control | Primitive coefficient cost after the rational Schur correction |
| Thin degree-one family | Raw error is between two linear exponential scales; its exact reduced denominator is a determinant/gcd quotient | Uniform lower or upper bounds for that reduced denominator |
| Arithmetic-controlled auxiliary polynomials | Every monic integer test polynomial preserves the linear residual and has an explicit small-prime normalizer; optimization becomes a lattice problem | A polynomial with a favorable denominator-weighted residual |
| Genuine two-variable moment families | Explicit rational-affine moments, positivity, fixed-exponent rank obstructions, and an actual varying-exponent family of degree \(n(n+1)+1\) | Primitive cancellation sufficient to match a possible cubic analytic scale |

All four rows are PROOF-DRAFT, with finite computations separated below. None proves irrationality of \(\zeta(7)\), failure of every construction, or novelty.

## 1. Oversizing now has a quantitative analytic estimate

**PROOF-DRAFT.** Put \(h=r+q\). Eliminating the rational-moment block gives the same degree-\(r\) Schur pencil as in the first investigation. A classical Meixner–Pollaczek polynomial kernel, evaluated at the negative pole nodes, now gives

\[
0<\det S_q(\zeta(s))\le C_{K,N,s,\nu}q^{-4r(N+1)},
\]
\[
\log C_{K,N,s,\nu}=O_{s,\nu}(K^2\log(K+1)).
\]

The proof constructs actual interpolation residuals, dominates their measures by an explicitly normalized gamma weight, and applies Hadamard's inequality. This replaces qualitative convergence by a rate. It is an upper bound, not a sharp asymptotic.

The exact integer certificate still contains the inverse rational-moment matrix through its adjugate. Its crude arithmetic bound does not balance the guaranteed analytic gain. This does not prove that the primitive polynomial fails. The precise remaining object is the primitive scalar after all coefficient cancellations.

Details: [projection.md](projection.md). **COMPUTED:** 5,000 coefficient identities, 5,000 summand bounds and 5,000 kernel bounds pass in projection_deep_checks.py. These check finite algebra, not continuous orthogonality or the whole proof.

## 2. The thin family: excellent approximation can be expensive

**PROOF-DRAFT.** For \((s,\nu,K,N,h)=(7,6,40n,3n,11n-1)\), write the rational root of the degree-one determinant as \(r_n=p_n/q_n>\zeta(7)\). The raw error is the last monic orthogonal-polynomial norm:

\[
e_n=r_n-\zeta(7)=\min_{p\text{ monic},\ \deg p=11n-2}
\int_0^\infty p(y^2)^2\frac{D_N(y^2)^5}{T(y^2)}w_7(y)\,dy.
\]

The full determinant is a product of such norms; taking its primitive degree-one representative removes the other factors. Restricting the scaled integral to a fixed interval and using the monic Legendre norm gives
\[
e_n\ge \frac{256C_7}{22n-3}e^{-Cn},
\quad C=37\log3+80\pi\sqrt2+11\log16.
\]
A monomial trial also gives \(e_n\le A2^{-11n}\), with finite \(A\) independent of \(n\). Thus this raw error has linear exponential scale and cannot have a negative quadratic logarithmic exponent.

The primitive value is \(q_ne_n\). If \(\log q_n/n\to\infty\), it diverges by the lower bound; that denominator assertion remains unproved. The exact determinant/gcd formula in [thin.md](thin.md) §4 identifies the missing arithmetic.

**COMPUTED, three cases only.** After stripping all prime factors at most \(2K\) from the orthogonal-root denominators, the remaining cofactors have 582, 2,544 and 5,883 digits. They are not claimed to be prime or fully factored. This shows that familiar small-pole denominators do not describe the main cost in these examples.

## 3. A systematic search in an integer lattice

**PROOF-DRAFT.** The auxiliary polynomial need not be the rational norm minimizer. For every monic integer \(p\) of the same degree,
\[
\mu_{7,X}\left(\frac{D_N^5p^2}{T}\right)=r(p)-X,
\]
and its positive target value is the corresponding squared norm. The denominator of \(r(p)\) divides
\[
12\operatorname{lcm}(1,\ldots,K)^7(K-N-1)!(2K)!.
\]
In particular it has no prime divisor above \(2K\), avoiding the large-prime Gram-minor cofactors seen in the rational optimizer.

Writing \(p=t^m-\sum v_it^i\), the raw error is
\[
e_{\mathrm{opt}}+(v-A^{-1}b)^TA(v-A^{-1}b).
\]
Minimization over integer coefficient vectors is exactly a closest-vector problem for the rational positive Gram metric \(A\). The final objective also includes the reduced denominator, so raw-error minimization alone is not the whole search. Coordinate rounding is a cheap control, not a solution of that lattice problem.

**COMPUTED.** Exact Euler–Maclaurin enclosures compare three choices at the overlapping scales. An entry \([a,a+1]\) means that the positive quantity lies strictly between \(10^a\) and \(10^{a+1}\).

| \(n\) | Choice | Denominator digits | Raw-error power bracket | Primitive-value power bracket |
|---|---|---:|---:|---:|
| 1 | Rational orthogonal optimizer | 674 | \([-57,-56]\) | \([616,617]\) |
| 1 | Integer monomial | 160 | \([-52,-51]\) | \([108,109]\) |
| 1 | Rounded integer coefficients | 165 | \([-57,-56]\) | \([108,109]\) |
| 2 | Rational orthogonal optimizer | 2,731 | \([-117,-116]\) | \([2614,2615]\) |
| 2 | Integer monomial | 390 | \([-105,-104]\) | \([285,286]\) |
| 2 | Rounded integer coefficients | 396 | \([-112,-111]\) | \([283,284]\) |
| 3 | Rational orthogonal optimizer | 6,158 | \([-176,-175]\) | \([5981,5982]\) |
| 3 | Integer monomial | 612 | \([-158,-157]\) | \([454,455]\) |
| 3 | Rounded integer coefficients | 619 | \([-165,-164]\) | \([454,455]\) |

The integer choices greatly reduce arithmetic cost but still give primitive values above one in every tested case. Monomial cases \(n=4,5,6\) were also checked, with the same finite conclusion. No asymptotic success or failure follows from the table. See thin.md §5–5A, thin_integer_rounding.py/json and trial_enclosure.py/json. The orthogonal rows come from the preceding thin_enclosure.py/json.

## 4. A genuine quadratic-degree single-target family

**PROOF-DRAFT.** On the seven-cube, let
\[
\mathcal L(f)=\int_{(0,1)^7}\frac{f(x)}{1-x_1\cdots x_7}\,dx,
\quad U=\prod_{\ell=1}^7x_\ell^\ell,
\quad V=\prod_{\ell=1}^7x_\ell^{8-\ell}.
\]
At scale \(n\), use \(u_n=U^{n+1}\), \(v_n=V^n\) and the \((n+1)^2\) independent functions \(u_n^iv_n^j\), \(0\le i,j\le n\).

Its moments have an explicit convergent partial-fraction formula. They are rational unless the seven denominator shifts coincide; in that case they are \(X-H_c^{(7)}\). There are no unwanted lower zeta values. The coefficient of \(X\) in the Gram matrix is an isolated entry plus a permutation on \(n(n+1)\) basis elements. Positivity therefore gives
\[
\deg\det G_n(X)=n(n+1)+1,
\qquad \det G_n(\zeta(7))>0.
\]
This realizes superlinear degree without reindexing the old sequence or taking powers. Holding the monomial exponents fixed instead imposes an \(O(n)\) target-rank bound for this class; varying the exponents evades that scoped obstruction.

**PROOF-DRAFT, explicit limitation.** A coarse entrywise normalizer has logarithm \(112n^4+o(n^4)\). A separate scaled-box comparison with tensor Legendre moment matrices proves
\[
\log\det G_n(\zeta(7))\ge -O(n^3+n^2\log n).
\]
Consequently this particular coarse integer normalization diverges. It cannot be repaired by seeking an \(e^{-cn^4}\) raw bound for this family, since the lower bound excludes that rate. Primitive coefficient cancellation remains open: for a primitive value below one, its content must cancel the displayed normalizer down to an effective scalar whose logarithm is bounded above by \(O(n^3+n^2\log n)\). This is a necessary condition, not an established cancellation theorem or an analytic upper bound at cubic scale.

**COMPUTED.** Exact matrices have sizes 4 and 9 and degrees 3 and 7 at \(n=1,2\). Their primitive values lie between \(10^{87}\) and \(10^{88}\), and between \(10^{937}\) and \(10^{938}\). Parent rank checks also cover \(n=1,\ldots,8\). These are finite checks only.

Full moment/rank/arithmetic arguments: [multiparameter.md](multiparameter.md) §7. Explicit raw lower bound and specified-normalizer consequence: [scaled_analytic.md](scaled_analytic.md).

## Reproduction and the remaining decisions

Run these scripts in order from this directory or by their repository paths:

1. projection_deep_checks.py
2. thin_deep_checks.py
3. thin_integer_rounding.py
4. multiparameter_checks.py
5. parent_checks.py
6. trial_enclosure.py
7. multivalue_enclosure.py

They use the standard library. Thin roots/rounding reuse the event witness moment engine; the interval scripts reuse witness/zeta_rig.py. Those dependencies are credited rather than called independent implementations. parent_checks.py recomputes finite Hilbert norm identities, denominator stripping and target ranks; it reads saved exact roots for the stripping step. The larger mathematical arguments remain written proof drafts.

**HEURISTIC research priorities.** The most immediately executable search is the integer-lattice auxiliary-polynomial problem, measuring the reduced denominator with every candidate. For the actual quadratic-degree family, the next step is coefficient content or a better integral normalization; another raw \(n^4\)-scale estimate cannot rescue the specified coarse normalizer. Oversized Schur projection now has a rigorous rate to compare against a future arithmetic improvement. These are concrete research questions, not claims added to the submission.
