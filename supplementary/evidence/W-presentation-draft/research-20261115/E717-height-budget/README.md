# E717: analytic cost of denominator engineering

Codex receiving driver for [team member]; scoped continuation of lane N.
Mathematical deductions are PROOF-DRAFT, finite exact outputs COMPUTED.
No human proof, Lean, novelty, or report-label upgrade is asserted.

The unrestricted-height cancellation hypothesis H from E715 is false by
lane R's CRT construction. This task asks whether that counterexample
also produces useful approximations, and what any useful replacement
family must pay for its roots.

**PROOF-DRAFT.** For that explicit CRT family, `liminf log(q*e)/K^2>=1`:
the raw approximation error itself grows on a quadratic exponential
scale. The inherited positive-integral representation and PNT in
arithmetic progressions are dependencies. This rules out that family;
it does not restore H or give a universal obstruction.

**COMPUTED.** Fresh exact reconstruction at K=40,80,160 gives conservative
raw error lower bounds respectively above `10^397`, `10^1568`, and
`10^10203`. These are lower bounds, not evaluations of the error.
`python3 parent_check.py` independently reconstructs the CRT roots and
checks rational bounds; `python3 worker/check.py` also recomputes the
covered integer tails. Stored numerical outputs are not their inputs.

**PROOF-DRAFT.** PARENT_PROOF.md (8)-(10) gives an exact finite
arcsine-Jensen bound with an explicit constant and penalties for roots
outside `[0,K/sqrt(8)]`. If `q*e<=exp(-eta*K)`, it forces

    log q + nu*sum_{j<=N} 2*asinh(sqrt(8)*j/K)
          +2*sum_a g(a^2/K^2)
        <= (4*log(1+sqrt(2))-eta)*K
           +4*log(1+sqrt(2))-log C_s,

where `C_s=pi*(2*pi)^(s-1)/(s-1)!`, `g(z)=0` on `[0,1/8]`,
and `g(z)=arcosh(16*z-1)` for `z>1/8`. This is a necessary aggregate
budget; it does not bound each root separately by a constant times K.

Kimi developed the elementary CRT-error and product-height proofs.
Codex derived the finite root-potential refinement and independent exact
checker. Kimi then re-derived all constants and gave PASS on equations
(8)-(11) in worker/REFINEMENT_REVIEW.md. This second-family review was
launched by the producing driver, a qualification for any future report
label decision. Both turns actually served moonshotai/kimi-k3.1-pro;
full transcripts are in log/transcripts/omos/ under chat-82ae973a91,
sequences 0 and 3281. The inherited positive-integral identity was not
independently proved in this task.

The fixed roots from E709 lie within the no-outlier interval, so their
remaining denominator question is unaffected. The original determinant's
zeta(7) closing-margin failure remains a distinct result.
