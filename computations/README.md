# Computations that are not Lean

This folder holds the interval-arithmetic computation behind the statement of the report that, over the whole region of
proportions of the construction (0 < alpha < 1/6, even nu <= 10), the margin of the estimates at zeta(7) stays positive:
at least +0.486. It is the computation shown in the report's Figure 1 and cited in Claims 3 and 4.

**Status.** COMPUTED, relative to a written derivation of the bound package with free proportions
(`evidence/scope_alpha_beta/derivation_beta.md`: written by an AI agent, reviewed by an AI model of another family, not read
by a human). It is not Lean, and nothing here is checked by the Lean kernel. The report's label for it is COMPUTED.

**What it does.** For each even nu in {2, 4, 6, 8, 10} the rectangle alpha in [0, 1/6], beta in [0, 2] is cut into 320 boxes.
Each box is either shown to lie outside the region where the derivation applies, or receives a rigorous lower bound of the
zeta(7) margin that holds at every point of the box (interval arithmetic at 113 bits with exact rational inputs).
Result: 1,600 boxes, none unresolved; least lower bound 0.9337, 0.7845, 0.6580, 0.5372, 0.4864 for nu = 2, 4, 6, 8, 10.

**Where things are** (the paths are those of the team's working repository, kept so that the code runs unchanged):

- `evidence/W-presentation-draft/research-20261115/E730-box-certify/`: the cover (`cover.py`, `box.py`, `box2.py`), its result
  files `cover-nu*.json`, its log, a cross-check, and a README with the reductions it relies on.
- `evidence/W-presentation-draft/research-20261115/E733-window-region/`: the extension to every nu >= 1 on the region where
  the window allocation applies.
- `evidence/scope_alpha_beta/`: the bound package with free proportions (`pkg_ab.py`), its derivation, the grid scan and the
  interval certificates at single cells.
- `evidence/certify/`, `evidence/margin/`: the interval library and the margin formula that the cover imports.
- `REPLAY.md`: a second run of the cover in another environment, compared box by box with the stored results.

**To reproduce** (Python 3.9 or later with mpmath, numpy and scipy):

```bash
cd evidence/W-presentation-draft/research-20261115/E730-box-certify
python3 cover.py 2 4 6 8 10 --workers 10      # about 10 minutes on 10 cores
```

**Who wrote it.** The code and the derivation were written by AI agents during the event, under the team's direction. In these
copies the names of team members, their handles and their machines are replaced by bracketed text.
