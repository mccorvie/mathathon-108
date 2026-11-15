# Ready block for `report/report.tex`: E730 extended, E732, E733 (lane N, for [team member])

Drafted Sun Nov 15 2026, 07:20 PT, by the lane N driver (Claude Opus 5.5). Under the night rules, [team member] edits the
report, so this file is a proposal with the exact old and new text. Numbers and labels are those of the three READMEs and their
parent reviews. **The ledger (`log/CLAIMS.md`) is not touched.** The eight claims keep their scope (even ν ≤ 10); this text
goes into the appendix as further evidence, not into a claim.

## Change 1 (main): appendix "Proportions other than Fauzan's" (report.tex, end of the paragraph after `\subsection{Proportions other than Fauzan's}`)

**Old text (exact; it ends the paragraph):**

```latex
So, relative to the written derivation, no proportion with $0<\alpha<1/6$ and even $\nu\le10$ closes $\zeta(7)$ within this package. Not covered here: finite cutoffs $M$, $\alpha\ge1/6$, odd $\nu$ and $\nu>10$ (extensions to these exist in the research notes and are not reviewed). Free $\beta$ is a different family from Fauzan's ($h\ne K-N$); all eight claims are stated at Fauzan's point, and nothing in this subsection is in Lean.
```

**New text:**

```latex
So, relative to the written derivation, no proportion with $0<\alpha<1/6$ and even $\nu\le10$ closes $\zeta(7)$ within this package. Three extensions of the cover reach the rest of the parameter range (COMPUTED, relative to written derivations; \ev{evidence/W-presentation-draft/research-20261115/E733-window-region/README.md}). First, the restriction to $\nu\le10$ comes from the allocation condition on Fauzan's slice $\beta=1-\alpha$. With $\beta$ free the condition holds at some proportions for every even $\nu\le22$, and the same cover settles $\nu=12,14,\dots,22$, with smallest bound $+0.532$. For $\nu\ge24$ the condition at $x=3$ is incompatible with the derivation's bound $2\beta+\nu\alpha-1<3$ (at $s=7$), so the region is empty; this is an elementary inequality, and it passes the team's Lean gate. At $\alpha=0$ the package does not depend on $\nu$, and its margin is at least $+1.045$. Second, the parity of $\nu$ is a choice of Fauzan's row basis, which puts $D_N^{\nu/2}$ on each side of the Gram form; for odd $\nu$ one factor $D_N$ moves into the weight. Fauzan's validity check for the inner allocation amounts to a window condition: all the numbers $L_a+b_a-\ell_K(a)/2$, with $b_a=\frac\nu2\ell_N(a)$ in the notation of Section~\ref{sec:claim5}, lie in one interval of length $1$. At even $\nu$ this condition reproduces his allocation exactly (exact rational check). At odd $\nu$ it changes the inner cost by at most $1/8$, so the same box bound applies. For $\nu=1,3,\dots,21$ the smallest bound is $+0.482$, at $\nu=9$ (CONJECTURE: a written derivation by an AI agent, not checked by a human). Third, the region used so far is defined by a sufficient test for the allocation. On the larger region where Fauzan's proof of the allocation applies with the window rule, $2038$ further boxes are each either certified, with bounds at least $+0.68$, or shown to lie outside the region, because it fails the saturation condition, fails $2\beta+\nu\alpha-1<3$, or fails a necessary condition at $x=3$. Together with $2\beta+\nu\alpha-1<3$, that necessary condition leaves no parameters with $\alpha>0$ for $\nu\ge25$; this too is a Lean inequality passing the gate. In sum, within this package, wherever the derivation's other conditions hold and Fauzan's proof of the allocation applies, no choice of $\nu\ge1$, $0\le\alpha<1/6$ and $\beta$ closes $\zeta(7)$: the margin is at least $+0.482$. The odd-$\nu$ derivation and the larger region each had one review by an agent of the same model family. Neither review found a counterexample; they corrected the stated scope and one Lean hypothesis. Neither has a review by another model family. Still not covered: finite cutoffs $M$, $\alpha\ge1/6$, $\beta$ below the saturation bound, and $2\beta+\nu\alpha-1\ge3$; there the package's formulas are not derived. Free $\beta$ is a different family from Fauzan's ($h\ne K-N$); all eight claims are stated at Fauzan's point, and nothing in this subsection is LEAN-VERIFIED: only elementary inequalities behind the cover pass the team's Lean gate, and their statements are not yet compared with the claim.
```

## Change 2 (optional, one sentence): §1, after the sentence that mentions the $+0.757$ grid value

**Old text (exact):**

```latex
So no choice of $\alpha$, $\beta$ and $\nu$ proves $\zeta(7)$ irrational with these estimates; the proportions of the paper that Calegari describes do not either (Claims~2 to~4; Appendix~\ref{app:further}).
```

**New text:**

```latex
So no choice of $\alpha$, $\beta$ and $\nu$ proves $\zeta(7)$ irrational with these estimates; the proportions of the paper that Calegari describes do not either (Claims~2 to~4; Appendix~\ref{app:further}). The same cover, extended to odd $\nu$, to $\nu>10$ and to the whole region where Fauzan's allocation is valid, gives at least $+0.482$ there; that extension has had only a review by the same model family (Appendix~\ref{app:further}).
```

## Notes for the editor

- **Labels.** The extensions are COMPUTED relative to written derivations. The odd-ν window argument is CONJECTURE in the
  report's sense (a written derivation by an AI agent, not checked by a human): it has a same-family review only, so it does
  not qualify as WRITTEN PROOF. The two cut-offs (ν ≥ 24, ν ≥ 25) are Lean inequalities. The gate passes (`--final`, 19
  declarations in the lane N probe), but their statements have not been compared with the claim, so they are LEAN-CHECKED,
  not LEAN-VERIFIED. That is why Change 1 says "passes the team's Lean gate" and not \LeanOK.
- **Numbers**, recomputed from the cover JSON files and **rounded down**, since they are lower bounds: ν = 12..22 0.5326 → +0.532, odd ν
  0.4827 → +0.482, α = 0 1.0459 → +1.045, new window-region boxes 0.6847 → +0.68. Sources:
  - ν = 12..22 smallest bound +0.5326 (E730 extension table);
  - odd ν minimum +0.4827 at ν = 9 (E732 table);
  - new window-region boxes ≥ +0.6847, and the count 2038 (E733 table);
  - α = 0: +1.045 (E730 extension);
  - the allocation condition holds on the scan grid up to ν = 22, at 131 points, and at none from ν = 24 on (E730 extension).
- **Not claimed:** finite M; α ≥ 1/6; below saturation; condition (iii) failing; other weight schemes or normalisers.
- The report's sentence "Its $17$ elementary reductions pass the team's Lean gate" is still accurate for E730's base cover.
  The 18th and 19th lemmas belong to the extensions.
- If the ledger should carry the extension as its own claim, that is the integrator's step; this block does not need it.
