# An explicit step bound for generic (alpha, beta, nu) (lane W)

Claude Opus 5.5 (Claude Code, [team machine]), for [team member], Sun 15 Nov 03:16 PT. EVENT WORK. No human check. This folder has no evidence id: lane W's E700-E711 are used, and E712 onward belong to lane N. Cite it by folder name.

**Question ([team member]).** The statements at (alpha, beta, nu) = (3/40, 37/40, 6) look rigid. Is there a similar statement about the cost for a generic choice of alpha, beta and nu?

## Statement

**Notation.** a = 2 beta - 1 + nu alpha, and r_s = (s-1)/2. The setting is the free-(alpha, beta) package of ../scope_alpha_beta/derivation_beta.md (E42), on its domain:
- alpha < 1/6, even nu <= 10;
- the inner allocation check passes and the outer saturation condition holds;
- a < r_s.

**(1) The s-dependence of the cost.** CONJECTURE: a written proof by an AI agent. E42's Prop. 1' and Cor. 4 passed lane N's second-family review E716. For every real M >= 3,

    Theta_pkg(s) = U + (s-1) beta/3 + 2 beta/M + C_M(nu, alpha, beta) + I_out(s; nu, alpha, beta),

where C_M does not depend on s. The inner and small primes charge exactly beta/3 per unit of s, for every proportion. Hence Theta_pkg(s+2) - Theta_pkg(s) = 2 beta/3 + I_out(s+2) - I_out(s), free of U and M. For beta = 1 - alpha and every real alpha this identity is in Lean (Claim 2, D5).

**(2) An explicit lower bound for the step.** CONJECTURE: a corollary of the written proofs below, by an AI agent, not reviewed.

    Theta*(s+2) - Theta*(s) >= 2 beta/3 - ((a - (s-1)/6)_+)^2 / (s-1)    (for s >= 7: 2 beta/3 - ((a-1)_+)^2/6).

*Derivation.*
- E63's free-(alpha, beta) step bound has a strengthened form by lane A's review (../A-e63-unsaturated-review/README.md, Lemma B; ledger C108-A-E63-COST; audited below saturation by lane U's Kimi audit E203, C108-U3, "pass with qualification"):
      step >= 2 beta/3 - J_s + J_{s+2},   J_s = int_{1/3}^{1} min{beta, (a - r_s y)_+} dy.
- Drop J_{s+2} >= 0.
- Bound J_s <= int_{1/3}^{oo} (a - r_s y)_+ dy = (a - r_s/3)_+^2/(2 r_s).

In words, the only thing a step can lose is the old rank correction, and that is bounded by a triangle.

*Checks of the formula.*
- At the template, a = 1 + (nu-2) alpha <= 8/5 for nu <= 10, and the s >= 7 form gives 37/60 - 3/50 = 167/300, Claim 2's bound.
- The bound is positive at every point of the domain. For 5 -> 7 this uses a < 2. For s >= 7 it uses either a - 1 < 2 beta - 1/3 (since nu alpha < 5/3) or a - r_s/3 < 2 r_s/3. The domain itself shrinks as s grows, because saturation depends on s.

**(3) The coupling between 5 and 7.** CONJECTURE, from (1). At every (alpha, beta, nu) where both s = 5 and s = 7 lie in the domain, and for every M and U:

    Theta_pkg(7) = Theta_pkg(5) + step_{5->7}(alpha, beta, nu).

So zeta(7) can close at a proportion only if zeta(5)'s margin there is below minus the whole step.

## Checks (COMPUTED, floating point; out/check.log)

- 5 -> 7, using the stored scan values A*(7) - A*(5): **all 679 admissible scan points with alpha < 1/6 and a < 2, no violation.**
  - The bound gives between 0.248 and 0.588 of the true step.
  - The tightest point is (1/10, 21/40, 10): step 0.5874, bound 0.3133.
  - The 56 points with a >= 2 lie outside the s = 5 domain.
- 7 -> 9, with A*(9) computed by pkg_ab.py: **40 points spread over a in [0.40, 2.75], no violation.** One sampled point lies outside the s = 9 domain. The tightest point is (1/10, 33/40, 10): step 0.8489, bound 0.4796.
- At the template, the 5 -> 7 step is 0.977865 (= 751/768) and the bound is 0.516.

## Not shown

- Nothing here is in Lean for beta != 1 - alpha.
- Nothing outside the derivation's domain: alpha >= 1/6, odd nu, nu > 10.
- Nothing about constructions other than this package.
- The bound is a sufficient lower bound, not the step. The dropped outer pole and class costs make up most of the true step.
- The certified statement over continuous boxes of (alpha, beta), that zeta(7)'s lower end stays positive, is lane N's E730 (research-20261115/), not this folder.

| claim | command (from this folder) | expected | time |
|---|---|---|---|
| both checks | `python3 -B check_step_bound.py` | out/check.log: "5->7: 679 ... violations 0"; "7->9: 40 sampled points ... violations 0" | 1 min |
| 5 -> 7 only | `python3 -B check_step_bound.py fast` | the first three lines | 1 s |
