# evidence/certify: the decisive #108 margin signs, by interval arithmetic

**EVENT WORK** (Fri Nov 13 2026, 23:41-23:59 PT). Experimenter: Claude Opus 5.5. Answers the synthesis red flag
"Rule 5: the decisive ζ(7) sign … uses theta.py's float64 tail beyond x = 200 and a 40-digit mpmath dual bound
… not interval arithmetic" (dossier red_flags; skeptic2 issue 4).

Inputs, imported read-only: `../margin/theta.py` (sha256 `2f1f90ad…3b015`, the package's exact arithmetic side, reading 'S')
and its comparison measures `../margin/out/U_cache.json` (sha256 `e6e6272a…20ecb4`, unchanged). No randomness in
`run.py` (`selftest.py` uses seed 108; it is a bug detector, not part of any proof). Python 3.14, mpmath 1.3.0.

## Result (COMPUTED, interval arithmetic; the theory each number feeds is labelled in §5)

Package: α = 3/40, λ = 37/40, even ν ≤ 10, theta.py reading 'S' (= E13's general outer function), M → ∞
(and every M ≥ 40, §3.6). Every number below is an endpoint of a rigorous enclosure; the margins are exact rational
sums of those endpoints.

| claim | certified value | float value it replaces |
|---|---|---|
| **ζ(7) fails, every comparison measure**: A*(7,ν) + LB(ν) > 0 | ν = 2: **+1.077080**, 4: **+0.961062**, 6: **+0.904155**, 8: **+0.906723**, 10: **+1.021455** | +1.077, +0.961, +0.904, +0.906, +1.021 (criterion5) |
| **ζ(5), ν = 6 closes** (Fauzan's 16-component ρ): A*(5,6) + U(6) < 0 | **≤ −0.058068** (M → ∞); A_200(5,6) + U(6) **≤ −0.026007** (M = 200, A_200 exact) | −0.058, −0.026 |
| ζ(5), ν = 4 closes too (opt36 measure) | A*(5,4) + U(4) ≤ −0.044104 | −0.044 |
| ζ(5) fails at ν = 2, 8, 10 for every measure | lower ends +0.0428, +0.0167, +0.2219 | +0.043, +0.016, +0.222 |
| ζ(9) fails at every even ν ≤ 10; ζ(3) closes at every even ν ≤ 10 | min lower end +1.9245 (ν = 8); max upper end −0.3761 (ν = 10) | same |
| theta.py's grid M₀ are valid upper bounds | all five, **at theta's own rational M₀** (no rounding up needed); so theta's U(ν) are certified upper bounds, unchanged to 1e−10 | |
| A_M ≥ A* for every real M ≥ 40 (all 20 (s, ν) pairs) | K₂/c ≤ 3.5945 < 40 (§3.6) | derivation.md Thm 3(ii): "(ν+1)λ/M + O(M⁻²), positive … in the computed rows" |

**Every decisive sign the task names is certified; none failed.** Full bracket table (certified ends, M → ∞):

| s \ ν | 2 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|
| 3 | [−0.8637, −0.8202] | [−0.8937, −0.8850] | [−0.8111, −0.7955] | [−0.6464, −0.6053] | [−0.4463, −0.3761] |
| 5 | [+0.0428, +0.0863] | [−0.0529, −0.0441] | [−0.0737, −0.0581] | [+0.0167, +0.0577] | [+0.2219, +0.2920] |
| 7 | [+1.0771, +1.1206] | [+0.9611, +0.9699] | [+0.9042, +0.9198] | [+0.9067, +0.9478] | [+1.0215, +1.0916] |
| 9 | [+2.1382, +2.1817] | [+2.0184, +2.0272] | [+1.9503, +1.9659] | [+1.9245, +1.9656] | [+1.9620, +2.0321] |

Lower end = A*(s,ν) + LB(ν) (no comparison measure does better); upper end = A*(s,ν) + U(ν; ρ_θ) (achieved by theta's
measure). The package closes iff < 0. So in this slice, **certified** for s ∈ {3, 5, 7, 9}: 5 is the largest of them at which
the package closes (at ν = 4 and 6), and ζ(7), ζ(9) fail at every even ν ≤ 10.

The certified dual bound is *tighter* than criterion5's: LB(ν) moved up by 0.00016-0.00037 (second-order cells, §3.4).
LB(6) = −1.3871640 agrees with skeptic2's independent Gauss–Chebyshev float −1.387163. The decisive ζ(7) minimum stays
**+0.904155** (ν = 6).

## Commands → expected output

Run from this folder. Total about 6 minutes.

| step | command | expected output (key lines) |
|---|---|---|
| M₀ | `python3 run.py M0` (12 s) | `nu= 6 fauzan16 CERTIFIED sup_[0,oo) 2U-V <= -6.649893079020 <= tau = -6649893/1000000`; five CERTIFIED lines → `out/M0.json`, `out/M0.log` |
| LB | `python3 run.py LB N=2000` (3 min) | `nu= 6 fauzan16 N=2000: CERTIFIED LB(nu) >= -1.387164049`; `nu= 2 … >= -2.512144377` → `out/LB.json`, `out/LB.log` |
| A* | `python3 run.py A` (2 min) | `s=7 nu= 6: A* in [2.291318581348, 2.291318589499]`, `s=5 nu= 6: A* in [1.313453998015, 1.313454006166]` → `out/A.json`, `out/A.log` |
| signs | `python3 run.py margins` | `zeta(7), nu= 6: … >= +0.904155 CERTIFIED > 0`, `zeta(5), nu= 6: … <= -0.058068; A_200(5,6) + U <= -0.026007 CERTIFIED < 0`, `ALL DECISIVE SIGNS CERTIFIED: True` → `out/margins.json`, `out/margins.log` |
| figure | `python3 run.py figure && rsvg-convert -o out/certified_brackets.png out/certified_brackets.svg` | `out/certified_brackets.svg` |
| bug check | `python3 selftest.py` | 900 random cells: float sample max − certified cell bound ≤ 0 (−3.6e−15, 0, −7.1e−15); iv point values = theta float to 3.6e−15 |

Hashes of the outputs: §6.

## 3. Methods: every enclosure and how it is obtained

### 3.1 Interval primitives (`ivlib.py`)
mpmath.iv at **113 bits** (about 34 digits), outward rounding for +, −, ×, ÷, sqrt, log, cos, sin, π. Rationals enter as
[floor, ceil] roundings (`libmp.from_rational`). mpmath.iv has no atan, so atan is built inside iv: two argument
reductions atan z = 2 atan(z/(1 + √(1+z²))) (and atan z = π/2 − atan(1/z) for z > 1) bring |y| ≤ 0.2, then the alternating
Taylor series to 30 terms plus its remainder interval ±|y|⁶¹/61. No float or non-interval function value enters any
bound. Interval endpoints are read as exact mpf numbers and converted to exact Fractions for the final sums.

### 3.2 M₀: a certified upper bound on sup_{t≥0} f(t), f = 2U^ρ − V_ν (branch and bound)
f = Σⱼ 2cⱼUⱼ − V_inc + νJ_α with Uⱼ the arcsine potential of [aⱼ, bⱼ] (theta's `np_Uarc`), V_inc = 2π√t + J₁, J_a(t) =
∫₀^a log(t+u²)du. Facts used (each elementary): Uⱼ is decreasing on [0, aⱼ], constant on [aⱼ, bⱼ], increasing on [bⱼ, ∞)
(so its sup on any interval is at an endpoint); Uⱼ' = ±1/√|(t−aⱼ)(t−bⱼ)| outside [aⱼ, bⱼ], monotone decreasing in t on each
side; −V_inc is decreasing with increasing derivative −π/√t − J₁'(t); νJ_α is increasing with decreasing derivative
ν·atan(α/√t)/√t.
- **Cell bound** on [t₀, t₁] = min of (i) the *monotone bound* (endpoint values) and (ii) a *hybrid mean-value bound*:
  components whose derivative is bounded on the cell are summed and bounded by g(c) + (w/2)·max(0, Hi, −Lo), where [Lo, Hi]
  is the sum of their derivative enclosures (from the endpoint values, by monotonicity of each derivative) and c the
  midpoint; components with an unbounded derivative (cell touching aⱼ, bⱼ or t = 0) use their monotone bound.
- **Domain**: [0, 4] is split at 0, at the 113-bit roundings of every aⱼ, bⱼ, and bisected until each cell bound is
  ≤ τ. For t ≥ 4: Uⱼ(t) ≤ log(t − mⱼ) ≤ log t, J₁(t) ≥ log t, J_α(t) ≤ α log(t+α²), so
  f(t) ≤ B(t) = (2λ−1) log t + να log(t+α²) − 2π√t, decreasing for t ≥ 1 when ν ≤ 10; B(4) ≤ −10.3 < τ.
- **Target** τ = theta.py's own M₀ (its float grid sup rounded up to 10⁻⁶). The script would retry τ + 10⁻⁶ and
  τ + 10⁻⁵ on failure; no retry was needed.

| ν | measure (components) | theta grid sup | τ = M̄₀ certified | max cell bound | cells | I(ρ) (enclosure, lower end) | C*(ν) | **U(ν) ≤** | **LB(ν) ≥** | criterion5 float LB |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | opt36 (25) | −6.1245787884 | −3062289/500000 | −6.1245783023 | 267 | −2.536144558555 | 0.660437713518 | −2.4686523779 | −2.5121443774 | −2.512301 |
| 4 | opt36 (29) | −6.4014790396 | −6401479/1000000 | −6.4014790295 | 301 | −2.305538713385 | 1.656736851929 | −1.9590925097 | −1.9678890603 | −1.968096 |
| 6 | fauzan16 (16) | −6.6498938806 | −6649893/1000000 | −6.6498930790 | 286 | −2.126593445147 | 2.653035990340 | −1.3715215895 | −1.3871640488 | −1.387407 |
| 8 | opt36 (24) | −6.8600887337 | −857511/125000 | −6.8600881053 | 262 | −1.962143152479 | 3.649335128752 | −0.7341031188 | −0.7751727496 | −0.775484 |
| 10 | opt36 (22) | −7.0502570036 | −7050257/1000000 | −7.0502570020 | 288 | −1.815838149322 | 4.645634267163 | −0.0600153085 | −0.1301639932 | −0.130530 |

At ν = 10 theta's rounding left only 3.6·10⁻⁹ of slack. The certified cell bound −7.0502570020 still fits under it.

### 3.3 I(ρ), C*(ν), U(ν)
I(ρ) = Σⱼ (Sⱼ² − Sⱼ₋₁²) log((bⱼ − aⱼ)/4) (Lai (91)). Nesting inner → outer is checked exactly, the weights exactly
(Σcⱼ = 37/40), and the logs by iv. C*(ν) is the closed form in theta.py, evaluated in iv. U(ν; ρ) = λM̄₀ − I(ρ) + C*(ν):
upper end taken. The enclosures have width < 10⁻³⁰.

### 3.4 LB(ν): a certified dual lower bound (second-order cells)
LB(ν) = I(σ) − ∫V_ν dσ + C*(ν), with σ = theta's stored measure (the same choice as criterion5). The weak-duality
inequality LB ≤ U(ν; ρ) for every comparison measure ρ is derivation.md Lemma 2 (PROOF-DRAFT; skeptic pass). Only
∫V dσ needs an upper bound. Each arcsine component is ∫V dω = (1/N) Σₖ avg over θ ∈ [πk/N, π(k+1)/N] of V(m + h cos θ).
- **V_inc is concave in t** (√t concave; J₁ an average of the concave functions log(t+u²)). So by Jensen, the cell
  average of V_inc is ≤ V_inc(t̄ₖ), where t̄ₖ = m + h(sin θₖ₊₁ − sin θₖ)/Δθ is the exact cell mean of t.
- **−νJ_α is convex in t** (J_α concave), so on a cell it lies below its chord, and the cell average is ≤ μₖψ(tₖ) + (1−μₖ)ψ(tₖ₊₁)
  with μₖ = (cbarₖ − cos θₖ₊₁)/(cos θₖ − cos θₖ₊₁), independent of the component.
Both bounds are second order in 1/N (criterion5's monotone cells are first order), so N = 2000 suffices. The N = 200
run gives LB(6) ≥ −1.3872456 and N = 2000 gives ≥ −1.3871640, against skeptic2's float −1.387163.

### 3.5 A*(s, ν) = I_out + ∫₃^∞ R(x)/x³ dx
- I_out and ∫₃²⁰⁰ R/x³ are **exact rationals** from theta.py (`I_out`, `int_R_x3`). The I_out values equal criterion5's
  `sstep_exact.out` (e.g. 27071/16000 at (7, 6), 127751/96000 at (5, 6)).
- **Beyond 200.** On the base period [200, 240], theta's pieces give R = a + bx. Write F = f₀ + f₁x from R(x+40) (theta's
  `affine_fit`). Then **R(x + 40k) = R(x) + 40k·F(x) for every integer k**. Reason: in theta's formula every floor term
  shifts by an integer multiple of k when x → x + 40k (80H, 40α·2 = 6, 80, 74 are integers), and d₀({x}), d₀({αx}), sl and
  n₊ are 40-periodic. So R(x + 40k) is a polynomial of degree ≤ 2 in k, and its agreement with a degree-1 polynomial at
  k = 0, 1, 2, 3 forces equality for all k (PROOF-DRAFT, argued here). This is checked exactly at 7 points per piece for
  k = 1, 2, 3, 1000, 10⁶ and k = −1, …, −4.
- Hence R(w) = wF(w) + Q(w), with F and Q 40-periodic and Q = a + (b−f₀)x − f₁x². Periods k = 0…44 are summed term by
  term (each an exact rational, accumulated in iv). The rest uses X = 2000 and two integrations by parts against the
  periodic antiderivatives G = ∫F̃ (with F̃ = F − F̄), H = ∫(G − Ḡ) and P₁ = ∫(Q − Q̄), all vanishing at X:
  ∫_X^∞ R/w³ ∈ F̄/X + (Ḡ + Q̄/2)/X² + (2[min H, max H] + [min P₁, max P₁])/X³.
  F̄, Ḡ and Q̄ are exact rationals (F̄ = (s − ν)λ, asserted). The ranges of H and P₁ are rigorous piecewise-cubic bounds:
  Taylor coefficients at the left end of each piece, |Σ dᵢyⁱ| ≤ Σ|dᵢ|δⁱ.
- Enclosure width 2.7·10⁻⁹ to 1.4·10⁻⁸. Every theta float A_inf lies inside its enclosure.

| (s, ν) | I_out (exact) | A* enclosure | theta float A_inf | A_200 (exact, shown rounded) |
|---|---|---|---|---|
| (3, 2) | 363463/288000 | [1.6484782866, 1.6484782894] | 1.6484782880 | 1.6622523267 |
| (3, 4) | 347173/288000 | [1.0741415986, 1.0741416040] | 1.0741416012 | 1.0970603039 |
| (3, 6) | 174239/144000 | [0.5760408036, 0.5760408117] | 0.5760408076 | 0.6081015704 |
| (3, 8) | 90427/72000 | [0.1287881869, 0.1287881978] | 0.1287881923 | 0.1699889321 |
| (3, 10) | 1453/1125 | [−0.3160976304, −0.3160976167] | −0.3160976236 | −0.2657589900 |
| (5, 2) | 9311/6000 | [2.5549539811, 2.5549539838] | 2.5549539824 | 2.5687280212 |
| (5, 4) | 68623/48000 | [1.9149922930, 1.9149922984] | 1.9149922957 | 1.9379109984 |
| (5, 6) | 127751/96000 | [1.3134539980, 1.3134540062] | 1.3134540021 | 1.3455147648 |
| (5, 8) | 125021/96000 | [0.7918263814, 0.7918263922] | 0.7918263867 | 0.8330271265 |
| (5, 10) | 42977/32000 | [0.3520447307, 0.3520447444] | 0.3520447375 | 0.4023833711 |
| (7, 2) | 31511/16000 | [3.5892248144, 3.5892248171] | 3.5892248158 | 3.6029988545 |
| (7, 4) | 29231/16000 | [2.9289506263, 2.9289506317] | 2.9289506290 | 2.9518693317 |
| (7, 6) | 27071/16000 | [2.2913185813, 2.2913185895] | 2.2913185854 | 2.3233793482 |
| (7, 8) | 453803/288000 | [1.6818958258, 1.6818958367] | 1.6818958312 | 1.7230965709 |
| (7, 10) | 878941/576000 | [1.1516193835, 1.1516193972] | 1.1516193903 | 1.2019580239 |
| (9, 2) | 347599/144000 | [4.6503359255, 4.6503359282] | 4.6503359269 | 4.6641099656 |
| (9, 4) | 326539/144000 | [3.9863117374, 3.9863117429] | 3.9863117401 | 4.0092304428 |
| (9, 6) | 305479/144000 | [3.3374296925, 3.3374297006] | 3.3374296965 | 3.3694904593 |
| (9, 8) | 11861/6000 | [2.6996909647, 2.6996909755] | 2.6996909701 | 2.7408917098 |
| (9, 10) | 177581/96000 | [2.0921488974, 2.0921489111] | 2.0921489042 | 2.1424875378 |

### 3.6 Every finite M ≥ 40
A_M − A* = c_cr·λ/M − ∫_M^∞ R/w³ (theta's `A_M`). One integration by parts with the periodic G gives
∫_M^∞ R/w³ ≤ F̄/M + K₂/M², where K₂ = (max G − min G) + max(Q, 0)/2, valid for real M ≥ 40 because the periodic identity
holds down to w = 40 (k ≥ −4). Since c_cr·λ − F̄ = (s+1)λ − (s−ν)λ = (ν+1)λ =: c (asserted exactly),
A_M − A* ≥ (cM − K₂)/M² ≥ 0 whenever M ≥ K₂/c. The largest K₂/c over the 20 pairs is 3.5945, so **A_M ≥ A* for every
M ≥ 40**. Every "ζ(7) > 0" therefore holds at every finite M too, which is the hypothesis "M with A_M ≥ A*" of derivation.md Thm 3(ii).

### 3.7 Combination
Margins are exact Fraction sums of the enclosure endpoints, e.g. lower(7, ν) = lo(A*(7, ν)) + lo(LB(ν)). For ζ(5), ν = 6,
both hi(A*) + hi(U) and A_200 + hi(U) (A_200 exact) are below 0.

## 4. Figure
`out/certified_brackets.svg` (PNG: `out/certified_brackets.png`, checked with rsvg-convert).
- **Left panel**: for each even ν ≤ 10, the certified bracket [A* + LB, A* + U] for ζ(3) (grey), ζ(5) (blue), ζ(7) (red)
  and ζ(9) (green), against the zero line. The four families are flat bands about one unit apart: ζ(3) at −0.4 to −0.9,
  ζ(5) straddling 0, ζ(7) at +0.90 to +1.12, ζ(9) at +1.92 to +2.18.
- **Right panel**: ζ(5) alone, with numeric labels. Its brackets lie entirely below 0 at ν = 4 and 6 (the package
  closes) and entirely above 0 at ν = 2, 8 and 10 (it fails for every measure).
- **The mechanism**: the s-step (≈ 0.8-1.06 per two units of s) is far larger than the bracket widths (≤ 0.07), so the
  sign is set by s.

## 5. What is certified, and what is not
- **Certified (COMPUTED, interval arithmetic)**: the numerical values of the package's formulas as coded in theta.py
  reading 'S' (A_M, A*, I_out, R), of U(ν; ρ) for theta's stored measures with a certified M₀, and of LB(ν) for the same
  σ. In particular rule 5 is now met for every decisive sign: no float decides any of them.
- **Not certified here (labels unchanged):**
  - that these formulas are Fauzan's bounds for general (s, ν) (E13, PROOF-DRAFT; derivation.md);
  - that U(ν; ρ) bounds the analytic exponent (Lai Lemma 11.4 / Xu (12): CITED);
  - weak duality LB ≤ U* (derivation.md Lemma 2, PROOF-DRAFT; standard);
  - the potential formula for arcsine measures (standard, used as in theta.py).
  The periodic-identity argument of §3.5 is mine (PROOF-DRAFT, here), and backed by exact checks.
- **Inherited exactness**: I_out and ∫₃²⁰⁰ R/x³ are theta.py's exact rationals. theta integrates piecewise-affine
  functions between a breakpoint set it builds, and checks every piece at 11 interior points. That method is theta's
  claim (README of ../margin). It was reproduced by independent code (skeptics) and, for the I_out values and the
  inner shifts, in Lean (E27). It is not re-derived here.
- **Rigor assumption**: mpmath.iv's directed rounding for sqrt, log, cos, sin is correct; this is mpmath's interval
  context, not formally verified software. atan is built from iv arithmetic alone.
- Scope as in E15: α = 3/40, even ν ≤ 10, Fauzan's package with the rank clamp. A different σ would give a different
  (valid) LB; theta's σ is close to optimal (gap to U: 0.009-0.07).

## 6. Hashes (sha256, Fri 23:56 PT)
```
613012a920634f1a27b6639550d42ed024a2be2e9d5d9e771ac632f9f772d07d  out/A.json
c3a6916d7ec18b70ac91608ccbc9029c940b3299e7f7283009f7083739665362  out/LB.json
c9a927145d2dbe8a5a3f9dd84de5616810cb160c0edbfeeffb2ed206c82338be  out/M0.json
a2f650fdd4b3cd225a23a8fa3a418371f0bbe9a03e7fedc6a34166148a274cfd  out/margins.json
2f1f90ade5ea082c73259fc16b9494692e8ad546197b08739b20e324e4e3b015  ../margin/theta.py (unchanged, read-only)
e6e6272ae5aaa0456810c1ebf993212ffae3e0e80e7f587550f2b9f9b720ecb4  ../margin/out/U_cache.json (unchanged)
```

**Erratum (orchestrator, Claude Opus 5.5, Sat 02:30 PT).** The table row "ζ(5), ν = 4 closes too" prints ≤ −0.044104; the certified value in `out/margins.json` (`bracket_5_4[1]`) is −0.0441002, so it reads **≤ −0.044100**. The sign is unaffected. Found by the row 13 experimenter (`../admissible_support/`, E36), which also shows the opt36 measures with support at t = 0 are admissible.
