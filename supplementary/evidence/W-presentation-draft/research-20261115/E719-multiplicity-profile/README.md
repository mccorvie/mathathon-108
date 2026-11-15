# E719: flexible pole multiplicities improve a finite approximation

Codex receiving driver for [team member], with one Open Math OS worker,
moonshotai/kimi-k3.1-pro, no swarm. All numerical claims below are
**COMPUTED**, bounded as specified. Analytic deductions remain
**PROOF-DRAFT**. This is a changed thin single-pole space, separate from
the original zeta(5) Hankel determinant and its zeta(7) closing margin.

## Question and finite result

The previous search fixed the negative-root factor to `D_N(t)^nu`.
This run instead permits

    A(t)=product_{j<=K}(t+j^2)^v_j * product_{a in J}(t-a^2)^2,
    sum_j v_j+2*|J|=K-4,

with nonnegative integer multiplicities. Kimi searched 12,000 distinct
candidates at K=40, J empty, v_j<=10, supported on j<=20, seed71920261115.
It searched by deterministic structured starts, local moves and seeded
random exploration. This is not an exhaustive optimum.

The best has nonuniform multiplicities on one contiguous block:

    (v_1,...,v_15)=(4,4,3,3,3,3,4,2,2,2,2,1,1,1,1),
    v_j=0 for j>15.

Its largest uncancelled pole is still40. It does not improve by deleting
a terminal string of poles. Disconnected blocks were tested, but did
not supply the best candidate in this bounded run.

| K40 candidate | Reduced denominator digits | Raw error interval, powers of10 | Primitive q*error interval, powers of10 |
|---|---:|---|---|
| E709 positive-root control |147| (10^-56,10^-55) | (10^91,10^92) |
| Uniform prefix v1..v12=3 |113| (10^-42,10^-41) | (10^71,10^72) |
| Best flexible multiplicities found |103| (10^-43,10^-42) | (10^60,10^61) |

Exact interval comparisons give `10^10 < (prefix objective)/(best objective)
<10^11`. Thus the improvement exceeds ten billionfold, but the new
primitive residual is still larger than10^60. The exact rational roots,
intervals and complete denominator factors are in PARENT_RESULTS.json.

## What the arithmetic saving buys

Compared with the uniform prefix, the best denominator loses one power
of2, ten of3, one each of5,7,11, two each of17,19; it gains one each
of29,31. Its large-prime exponents for23,29,31,37 are7,7,7,6, compared
with7,6,6,6 for the prefix. The finite improvement therefore does not
repair the large-prime cost highlighted by E715. It mainly reduces
other prime costs. These exact comparisons do not imply an asymptotic
valuation statement.

## One explicit scaling, checked separately

The driver defines `K_n=36n+4` and repeats each of the15 multiplicities
n times. This preserves `deg A_n=36n=K_n-4` and matches the best K40
profile at n1. It is not the template K=40n and is not claimed optimal.

| n | K_n | q digits | Raw-error decade | Primitive-residual decade |
|---:|---:|---:|---:|---:|
|1|40|103|-43|60|
|2|76|224|-80|143|
|3|112|331|-117|214|
|4|148|427|-153|273|
|5|184|544|-190|353|
|6|220|637|-227|410|

Here decade d means a value in `[10^d,10^(d+1))`, certified by rational
comparison. The raw errors shrink while the normalized integer values
remain enormous in every tested case. Six finite cases establish no
asymptotic growth theorem. Reproduce with `python3 scale_profile.py`.

## Analytic budget and receiving checks

**PROOF-DRAFT.** E717's exact finite Jensen bound extends additively,
replacing `nu*sum_{j<=N}Delta(j/K)` by `sum_j v_j*Delta(j/K)`.
PARENT_SCREEN.md derives a rational necessary screen. Combined with each
computed q, this screen already rejects `q*e<1` for all reported
candidates and all six scaled cases, conditional on that written
analytic inequality. It is not a lower bound on q for all profiles.

The corrected Kimi script was replayed unmodified in an isolated folder:
all mathematical JSON fields match (only run timestamps and duration
are excluded). Codex's separate full-A closed-factorial residues
reconstruct every reported root, enclosure, denominator factor and
in-domain prime tail. All prime identities checked use only
K/2<p<=K,p>7,p^2>2K. Run `python3 receive.py` for both checks.
The zeta enclosure code is the inherited, credited
`evidence/witness/zeta_rig.py`; its remainder theorem is a dependency.

## Corrections, provenance and limits

The first worker turn used the wrong sign in positive-root factors,
corrupting its E709 control, and applied a prime-tail identity outside
its domain. The driver caught both before crediting results. The full
first-turn files are retained in initial-run/ and are invalid for the
E709-derived claims; worker/ contains the corrected pass and ERRATUM.md.
Every searched candidate has J empty, so its numerical data were
unaffected, which the exact corrected replay confirms. Full OMOS
archives are chat-956a095bd5 sequences0 and4406:28+14Kimi calls.

This experiment shows a finite gain from a previously unsearched
vanishing profile, followed by failure of one explicit scaling in six
finite cases. It neither restores H nor excludes all thin families.
No irrationality, novelty, human-proof or Lean-status claim follows.
The original zeta(7) determinant breakpoint is unchanged.
