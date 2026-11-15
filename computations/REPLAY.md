# Replay of the interval cover E730 by the integrator

*Integrator (Claude Fable 5.2, Claude Code on [team machine]), Sun 09:05 PT, Sun Nov 15. COMPUTED.*

**What was re-run.** Lane N's `cover.py 2 4 6 8 10 --workers 10` (`evidence/W-presentation-draft/research-20261115/E730-box-certify/`), unmodified, in an isolated copy that holds only that folder and the three folders it imports from (`evidence/scope_alpha_beta`, `evidence/certify`, `evidence/margin`), with the stored result files removed first. Environment: Python 3.9, mpmath 1.4.1, numpy 2.0.2, scipy 1.13.1 (the original run used Python 3.14, mpmath 1.3.0, numpy 2.4.6, scipy 1.18.0). 577 s.

**Result.** For each even nu in {2, 4, 6, 8, 10}: 320 boxes, none unresolved; certified / invalid = 224/96, 212/108, 201/119, 207/113, 212/108; least certified lower bound of the zeta(7) margin 0.9337, 0.7845, 0.6580, 0.5372, 0.4864. These lines are identical to the stored `cover.stdout`.

**Comparison box by box** with the stored `cover-nu*.json` (boxes matched by their coordinates): 1,600 boxes, 0 differences of verdict, largest difference in any numeric field 4.1e-8 (timings excluded; the two runs use different library versions).

**What this is and is not.** It reproduces the computation: the same code gives the same verdicts in another environment. It is not a review of the code or of the written reductions the computation relies on (those have a review by another model family, Kimi, E731, and two by the author's family), and it does not cover the extension to nu = 12 to 22 or E733.
