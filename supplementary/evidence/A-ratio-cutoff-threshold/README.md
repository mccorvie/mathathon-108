# Exact cutoff thresholds for the fixed original-ratio certificates

Codex, 2026-11-15 UTC; scoped lane A continuation of
`A-ratio-1-12-upper` at commit34defd5dd05f881d42e5572b4998fd56bc220b59.

**COMPUTED:** for s=5, alpha=1/12, beta=11/12 and the previously certified
translated measures, the first integer cutoff M>=40 at which the FIXED
certificate expression becomes negative is138 for nu4 and165 for nu6.

| nu | Fixed potential bound tau | Previous cutoff and positive margin | First negative cutoff and margin |
|---|---|---|---|
| 4 | -801/125 | 137: approximately +0.0002236646954 | 138: approximately -0.0000026001482 |
| 6 | -667/100 | 164: approximately +0.0000211494945 | 165: approximately -0.0003004483082 |

These decimals are summaries, not directed endpoints. Exact rational
enclosures and every bisection evaluation are in results.json. The earlier
M1000 certificate remains valid. No potential search or global-supremum
certification is repeated: those are inputs, pinned by hash. Finite
arithmetic integrals are evaluated exactly as rationals with the inherited
piecewise-affine package; no limiting-tail estimate is needed here.

## Monotonicity lemma — PROOF-DRAFT

Retain the source definitions and identity R=xF+Q from
`A-ratio-1-12-review/replay/scope_alpha_beta/derivation_beta.md`,
Proposition1', with

    A(M)=I_out+6 beta/M+integral_3^M R(x)/x^3 dx,
    F(x)=4 beta+2 beta{x}-2 nu beta{x/12},
    Q(x)<=(nu+1)^2/8=:Qmax.

For x>=0 write floor(x)=12j+r, 0<=r<=11. Then

    {x/12}=(r+{x})/12 >= {x}/12.

This alignment of the two fractional-part grids is the key step. For
nu4/6 the coefficient2-nu/6 is positive, and hence

    F(x)<=4 beta+(2-nu/6)beta{x}<=(6-nu/6)beta.

On every compact interval in (0,infinity), R is bounded and piecewise
polynomial, with locally finitely many breakpoints. Thus A is locally
absolutely continuous and, almost everywhere,

    A'(M)=[R(M)-6 beta M]/M^3
          <=[Qmax-(nu beta/6)M]/M^3.

The right side is strictly negative for M>6Qmax/(nu beta), namely
225/44 fornu4 and147/22 fornu6. Both thresholds lie below40. Integrating
this derivative bound proves strict decrease on [40,infinity), including
across the breakpoints; no assumption of smoothness at a floor jump is made.

Let B_tau(M)=A(M)+beta*tau-I(rho)+Cstar. The last three terms are constant
in M, so B_tau is also continuous and strictly decreasing. Its certified
positive sign at m-1 and negative sign at m imply that it has exactly one
zero in (m-1,m), that m is its first negative integer argument>=40, and
that it is negative at EVERY real M>=m. This supplies the all-real-cutoff
conclusion from two endpoint certificates, not from an exhaustive grid.

## What follows, and what does not

**CONJECTURE (integrated package consequence):** conditional on the
inherited arithmetic and analytic package and the previous global
potential certificates, the s5 margin closes for every real M>=138 at
nu4 and every real M>=165 atnu6. The rational endpoint calculations are
COMPUTED; the universal implication above remains PROOF-DRAFT.

The first-integer assertion concerns B_tau with these exact chosen tau
values. A positive B_tau is an unsuccessful upper certificate, NOT a
positive lower bound on the true or optimal margin. A smaller true
supremum, a tighter tau, or a different measure might close earlier.
This neither proves failure below138/165 nor supplies a new irrationality
theorem, zeta7 result, novelty verdict, human read or Lean verification.

## Reproduction and review

Run `python3 check.py` in this folder (Python, mpmath, numpy and scipy,
versions inherited from the previous packet's INPUTS.json). The script
imports the previous certificate wrapper, which checks its dependency
hashes before loading the package. It saves the SHA256 of the prior
certificate and wrapper as well. The 750 exact rational diagnostics
across two nu values test fractional alignment, the F inequality and
the derivative numerator bound; the universal proof is above, not those
samples. Two full executions gave identical results.json bytes.

REVIEW.md is a separate same-family Codex proof review. It checked the
lemma, absolute-continuity step and fixed-certificate scope; it did not
independently replay the numerical integration. The parent read it and
reran the computation. Interval and arithmetic engines remain inherited.

## Sources and AI use

**CITED:** the exact finite arithmetic expression is from Claude's
`scope_alpha_beta/{pkg_ab.py,derivation_beta.md}` (Proposition1', sections
2-5), frozen in E710 at2b84a76b3d6a33e8d94aceea179f8ddd250e0538;
Qmax and cutoff definitions are also in E710/SCOPE_REVIEW.md. The global
potential/energy certificate is our preceding34defd5 packet, including
its113bit results and160bit verifier. Its SOURCES.md records Xu's
`analytic-foundations.md` section3 eqs6-12 at
eb264a73a0206c50aba854e0be3372067dd2e11a (nu=2q), and the inherited
Fauzan/Lai references and source-access limitations. No external paper
was freshly verified in this run and no priority claim is made.

Parent Codex derived the fractional-grid inequality, implemented the
exact bisection and scope checks. Native Codex cutoff_monotone_review
reviewed the proof independently. Both are the same model family.
WORK_RECORD.md records the session in condensed form; a full native
transcript export was not available. No other lane's evidence, report,
selection or active worker was edited.
