# E204 / U9: the latest certificates bracket the actual real exponent

Author: Codex for [team member], lane U. EVENT WORK, started Sat 11:34 PT.
Work completed: driver Codex (proof, exact endpoint subtraction and reviewer
corrections); Kimi in chat-81e62ae61c (qualified finite-arcsine Jensen review).
GLM chat-fda9305c5f was stopped without a completed audit; its failed attempt
is preserved and receives no review credit. No human check or novelty verdict.
Read `kimi/REPORT.md` **together with DRIVER_REVIEW.md**: the latter corrects
the reviewer's integral display, rejected subleading claim and quantile grid.

## 1. What is being bounded (PROOF-DRAFT, relative to the named inputs)

Fix alpha=3/40, lambda=37/40, an odd s>=3, an even nu in {2,4,6,8,10},
and K tending to infinity through positive multiples of 40. Put N=3K/40,
h=37K/40. Use the original positive Hankel determinant and factorial
normalizer, literally as in E56 `../e26_proof/prop1/prop1.md` section 1:

    F_K(s,nu)=S_K Delta_K(zeta(s)),
    u_K(s,nu)=K^(-2) log F_K(s,nu).

For a compact positive trial sigma of mass lambda define
L(sigma)=I(sigma)-int V_nu d sigma+C*(nu). For an admissible comparison
rho of that mass, U(rho)=lambda M(rho)-I(rho)+C*(nu).

**Sandwich.** E56 Proposition 1 gives

    L(sigma) <= liminf_K u_K(s,nu).

Xu's real upper bound, section 3 (12), gives

    limsup_K u_K(s,nu) <= U(rho).

For touching-zero finite arcsine sums, apply E200 to translate rho by
e>0. Each fixed translated measure meets the literal positive-support
hypothesis and satisfies U(rho_e)<=U(rho)+O(sqrt(e)). First take the
limsup in K at fixed e, then let e decrease to zero. This proves the
same upper bound without choosing a K-dependent comparison measure
or requiring constants uniform in e. Both bounds hold at each fixed s;
no assertion uniform over s growing with K is made.

Consequently, for any certified endpoint pair L_lo<=L(sigma),
U(rho)<=U_hi,

    L_lo <= liminf u_K <= limsup u_K <= U_hi.                 (S)

The trial measures used in the latest dual certificates are finite
positive arcsine sums on nondegenerate compact intervals. Lemma 0 of
E56, or E200 section 2, gives their required square-root local-mass
bound. The primal certificates specify comparison measures of exactly
the same mass and external field. Thus the E49/E58 pairs can be used
in (S), rather than merely bounding the comparison-measure infimum U*.

This argument uses the actual log-gas lower bound E56 in addition to
weak duality; weak duality alone does not bound the actual u_K below.
Existence of lim u_K, equality with an equilibrium value, attainment
of U*, and strong duality are not required or established here.

### Short lower proof for the finite-arcsine certificate class (PROOF-DRAFT)

For the actual trial measures used here one can use E56's shorter
Jensen argument, without its explicit quantile error. Write d sigma=f dt,
and let P=(sigma/lambda)^(tensor h). A finite positive sum of arcsine
densities has int f|log f| finite, and int |log t| d sigma finite,
including at t=0: near any endpoint its density is bounded by a constant
times inverse square-root distance, whose product with absolute log
distance is integrable. Its pairwise absolute log energy is finite by
the local-mass estimate. Hence all logarithms below are integrable.

In the scaled Heine integral of E56 (3.1), denote the nonnegative
integrand by G_K(t_1,...,t_h), so Z_K=int G_K dt_1...dt_h. Restricting
to the trial support, changing measure and using Jensen gives

    log Z_K >= E_P[log G_K - sum_i log(f(t_i)/lambda)].

The first comparison is an inequality, since the original integral
also includes points outside the trial support. The pair term is

    E_P[2 sum_(i<j) log|t_i-t_j|]=(1-1/h)K^2 I(sigma).

For the scaled single-variable weight, E56 Step C1/C2 and the ell=1
term of its weight series hold for all t>0 in the form

    log(wtilde_K(t)) >= -K V_nu(t)+(s-1)log K
       +((s-1)/2)log t - log(2 pi K)-1/(6K)+kappa_s.

Take its expectation and subtract the density logarithms. All terms
other than -K^2 int V d sigma and (s-2)h log K are O_(sigma,s,nu)(K).
The missing diagonal pair contribution is also O(K). Finally Heine
contributes -log h!= -h log K+O(K), the factorial normalizer has
remainder (2-nu)h log K+O(K), and the K^2 log K terms cancel exactly.
Therefore

    log F_K >= L(sigma)K^2+(s-nu-1)lambda K log K+O_(sigma,s,nu)(K),

where the O term can have either sign. Dividing by K^2 proves the
lower half of (S). This is E56 Remark 3 restated with its corrected
initial inequality, not an independent novelty claim. It applies to
the finite-arcsine trials of all five certificate pairs; the more
general E56 Proposition 1 also covers nondensity trial measures.

## 2. Updated ceilings (COMPUTED, exact subtraction of stored certificates)

Run `python3 -B ceilings.py`. The script reads only the original E49/E58
certificate endpoints, checks their order and positive gap, subtracts
them with Fraction, and records each input checksum. This is not fresh
interval certification. `ceilings.json` has exact endpoints and gaps;
`ceilings.md` is the table, rounded outward. At ten decimal places:

| nu | actual-exponent lower endpoint | upper endpoint | gap upper bound |
|---|---|---|---|
| 2 | -2.5062189760 | -2.5061250401 | 0.0000939358 |
| 4 | -1.9670699610 | -1.9668427619 | 0.0002271990 |
| 6 | -1.3855141807 | -1.3853066940 | 0.0002074866 |
| 8 | -0.7619450826 | -0.7617450696 | 0.0002000130 |
| 10 | -0.1000783829 | -0.1000050150 | 0.0000733678 |

The interpretation of this computed table as actual-exponent bounds
is **PROOF-DRAFT**, via section 1 and its hypotheses. For a report use
**CONJECTURE**, cite this proof and the E56 audit, and state the stored
certificates' computational assumptions until a human reads the proofs.

## 3. Consequences for the old analytic-slack discussion (PROOF-DRAFT)

At nu=6, any eventual bound of the form

    log F_K <= U' K^2+o(K^2)

has U'>=L_lo. Relative to the latest certified U_hi the improvement of
that coefficient is therefore at most U_hi-L_lo<=0.0002074866.
The old E44/E56 ceiling 0.0156425 compared a weaker upper certificate
with an older lower certificate. It remains valid for that baseline;
this is the updated ceiling for the improved E58 baseline.

At nu=8, (S) forces liminf u_K>=-0.7619450826>-0.762. By the
definition of liminf, eventually u_K>-0.762. Thus the finite-K values
around -0.778 and the old fitted limits around -0.772 in E49 cannot
be the asymptotic value for these fixed parameters. The sequence need
not be monotone, no explicit crossing K is supplied, and a true limit
is not asserted. Any asymptotic slack relative to the latest certified
upper coefficient is <=0.0002000130, rather than 0.010-0.014.

The integrator should supersede E49 section 0 item 5's old dichotomy
with this qualification if E56's proof survives review: the large
finite-K gap does not show large asymptotic analytic slack. This is a
deduction from existing event work, not a novelty claim and not an
improvement of the arithmetic estimates.

## Sources and audit

E56: `../e26_proof/prop1/prop1.md` (Claude Opus 5.5, PROOF-DRAFT),
including its original audit in `audit/notes.md` (Claude only).
The non-Claude review of the finite-arcsine Jensen proof is in
`kimi/REPORT.md`, with mandatory driver corrections in DRIVER_REVIEW.md.
The full explicit finite-error formula has not received an accepted
non-Claude audit here. The failed GLM attempt is in `glm-incomplete/`.
All worker transcripts were saved before recording review credit.

Xu's original bound was opened by the driver at the pinned revision:
https://github.com/Anchen0823/zeta9-research-notes/blob/eb264a73a0206c50aba854e0be3372067dd2e11a/missions/zeta7/research/analytic-foundations.md
Its section 3, (6)-(12), is the source of the field, normalizer constant
and upper bound; this file does not claim those as event contributions.

E49/E58 numerical sources are fully enumerated, with hashes, in
`ceilings.json`; E200 is `../U-support-translation/README.md`.
