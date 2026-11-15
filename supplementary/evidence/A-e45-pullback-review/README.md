# A5: corrected pullback ambiguity and its Hankel footprint

14 November 2026. Codex scoped arithmetic audit for [team member].
Status for reporting: **CONJECTURE**, complete agent proofs below; no
human/Lean verification or novelty claim. This corrects a known false clause
in E45 and an additional reversed degree description in its review/dossier.

## Replacement for Theorem D, item 4

**PROOF-DRAFT.** Let s=2r+1>=3 be odd, J=2r, and fix
D=partial^J/J!. Use the functional tau_{D,X} of Lemma A and the domain
V=Q[t] plus finite Q-linear combinations of 1/(t+k^2), k>=1.
Equality below means equality of formal Q+QX-valued functionals, not equality
after a numerical specialization of X. Define mu^P(R)=tau(P(x)R(-x^2))
and mu_X=mu^{x^s}. Write P=P_odd+P_even and P_even=sum_i p_{2i}x^{2i}.

If the X-coefficient of mu^P(1/(t+k^2)) equals k^{s-1} for infinitely
many positive k, then P_odd=x^s and

    mu^P(R)-mu_X(R)
      = -1/2 sum_{i=0}^r p_{2i} (-1)^(r-i) R^(r-i)(0)/(r-i)! .     (1)

Consequently

    mu^P=mu_X  iff  P_even belongs to x^(s+1) Q[x^2].              (2)

Proof. The residues of P(x)/(k^2-x^2) at k and -k are -P(k)/(2k)
and P(-k)/(2k). Since tau of a simple pole has X-coefficient minus its
residue, that coefficient is P_odd(k)/k. Infinitely many values force
P_odd=x^s by polynomial identity. Lemma P(i) gives

    tau(g)=-[x^J]g/2

for even g regular at zero. Here R(-x^2) is regular at zero for every
R in V, so coefficient extraction proves (1). Test R=t^(r-i) to isolate
p_{2i}; all i=0,...,r must vanish for equality. Conversely those
coefficients vanishing makes (1) zero for every R. This proves (2).

**PROOF-DRAFT — kernel versus quotient.** The invisible even kernel is
x^(s+1)Q[x^2], which is infinite-dimensional. The space of effective local
corrections has dimension r+1=(s+1)/2, represented uniquely by even
polynomials of degree at most s-1. These are different statements:
low-degree even terms CHANGE the functional; high-degree even terms do not.

**COMPUTED — exact witness.** At s=5, P=x^5+x^6 leaves every value unchanged,
whereas P=x^5+x^4 changes mu(1) by -1/2. With P=x^5+1,
the change on R=t^2 is -1/2. The checker recomputes such statements from
Bernoulli moments and partial-fraction residues, not stored results.

## What to correct in the shared synthesis

The original Theorem D item 4 says equality holds iff P is odd. The prior
verifier already refuted this and correctly gave (2) in words. However,
its issue 1 then calls the ambiguity finite-dimensional and recommends
"up to even polynomials of degree <=s-1"; the dossier E45 repeats that
degree direction. Replace that prose by:

    Once its odd part is fixed, the pullback depends only on the even
    Taylor jet through degree s-1. Its invisible freedom is exactly the
    even polynomials divisible by x^(s+1).

This is a correction to explanatory wording, not a refutation of Lemmas
A-C or of the verifier's displayed coefficient criterion. The original
producer/referee files and dossier are left unchanged for the integrator.

## Exact finite-rank consequence

**PROOF-DRAFT.** Let delta denote the local functional in (1). Allow a
factor W(t) analytic at zero, with W(0)!=0, and define delta_W(R) by the
same finite Taylor formula applied to WR. This definition makes sense
even when WR is outside V. If W is rational and regular at zero and WR
is in the original domain, it agrees with the actual pullback difference.

If some low even coefficient is nonzero, put
m=min{i<=r:p_{2i}!=0}, d=r-m, and a_e=delta_W(t^e). Then

    a_e=0 for e>d,
    a_d=-1/2 (-1)^d p_{2m} W(0) !=0.                            (3)

Thus for h>=d+1, the h-by-h Hankel matrix (a_{i+j})_{0<=i,j<h}
has rank exactly d+1. Indeed all rows with i>d vanish, and the leading
(d+1)-square block has zeros beyond its antidiagonal and determinant

    (-1)^(d(d+1)/2) a_d^(d+1),

which is nonzero. This explicitly locates the correction in the first
d+1 rows and columns. No claim about the determinant growth of the full
Hankel matrix follows from rank alone: a fixed-rank perturbation can still
change its determinant substantially.

**PROOF-DRAFT — positivity of the correction alone.** Assume all relevant
Taylor coefficients are real. If d>=1, then

    delta_W((1+u t^d)^2)=a_0+2u a_d,

since a_{2d}=0. Choosing u=-(a_0+1)/(2a_d) makes this -1. If d=0,
the functional is a_0 times evaluation at zero, which is positive on
polynomial squares exactly when a_0>=0. Together with the zero case,
these are all positive local corrections. This does NOT decide positivity
of the full mu_X+delta_W; the base functional may contribute too.

## Evidence and scope

**COMPUTED.** Run `python3 problems/108-zeta-odd-autopsy/evidence/A-e45-pullback-review/check.py`.
The script builds Bernoulli numbers by their rational recurrence with
B_1=-1/2, evaluates polynomial tau moments and simple-pole residues, and
checks the correction against coefficient extraction. It also checks
weighted Hankel ranks, antidiagonal determinants and negative-square
witnesses by exact rational arithmetic. Exact counts are in results.json.
The s range is 3,5,7,9,11,13,15; poles k=1,...,6. No saved outputs are read.

**PROOF-DRAFT — separate same-family audit.** Agent `pullback_audit`
accepted the formula, kernel/quotient distinction and rank/positivity
statements, requiring the formal-X and real-coefficient scope clauses
included above. See REVIEW.md. This is a Codex review of a Claude-produced
draft, followed by a same-family review of this repair; neither is a human
check or an upgrade of any upstream claim.

## Provenance and coordination

**CITED — exact internal sources.**
- `evidence/zeta7_levers/loss-lower-bound/lemmas/lemmas_ABC.md`, section 5,
  Lemma P and Theorem D item 4: the functional and false clause.
- The adjacent `verify/VERDICT.md`, issue 1: the prior counterexample,
  correct coefficient condition and reversed degree/dimension prose.
- `dossier.md`, E45, and `lanes/A-arithmetic.md`, task A5: requested repair.

This audit cites those internal statements, proves the repair directly,
and makes no external-literature or novelty claim. Their exact Git blobs
are recorded in REVIEW.md. No numerical forcing of D from zeta values is
asserted: upstream Theorem D's formal/conditional alternatives remain.

Current AGENTS, README rubric and phase rules, DECISIONS, authoritative
shortlist, recent commits, dossier, all three lane reports and BOARD were
read. The repository now selects #108 and retains #24/#35; the saved
eight-problem instruction is stale relative to the recorded human decision.
This review makes no selection or restoration. Dedicated #24/#87 campaigns
and incumbent #108 tasks remain untouched. A5 was unclaimed on the board;
the scoped claim was published and re-read before work. Only this new
A-prefixed folder and append-only coordination/provenance records are owned.
The Mac path is unavailable; publication uses fresh-parent GitHub objects
and a non-forced expected-head update. No unfinished local capture resumed.

**HEURISTIC — remaining obstacle.** The integrator should replace the
false/reversed wording before presentation. Any use of the finite-rank
correction to improve arithmetic bounds still needs actual determinant,
valuation and full-functional positivity estimates; none are provided here.
