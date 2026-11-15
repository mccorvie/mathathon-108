"""COMPUTED: exact arithmetic for a conditional primitive-growth reduction.

No determinant, Lean gate or interval energy computation is run here.
The repaired energy endpoint is a read-back from the pinned source.
All logarithmic bounds for C_infinity are independently recomputed using
finite positive rational series and explicit remainder bounds.
"""
from fractions import Fraction as F
import json
from pathlib import Path


def add(*xs):
    return sum(x[0] for x in xs), sum(x[1] for x in xs)


def scale(a, x):
    return (a*x[0], a*x[1]) if a >= 0 else (a*x[1], a*x[0])


def log_unit(x, n=24):
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    s = 2*sum((z**(2*j+1)/F(2*j+1) for j in range(n)), F(0))
    err = 2*z**(2*n+1)/(F(2*n+1)*(1-z*z))
    return s, s+err


def log_rat(x):
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x > 2:
        x /= 2
        k += 1
    return add(log_unit(x), scale(F(k), log_unit(F(2))))


def G(x):
    return add(scale(x*x/2, log_rat(x)), (-3*x*x/4, -3*x*x/4))


def show(q):
    return {"exact": str(q), "decimal_diagnostic": float(q)}


alpha, lam, nu = F(3,40), F(37,40), 6
I = add(G(1+alpha), scale(-1, G(1-alpha)), scale(-1, G(2*alpha)))
constant = 2*lam-2*nu*lam*alpha-3*lam*lam
C = add((constant, constant), scale(2*nu*lam*alpha, log_rat(alpha)),
        scale(2*lam*lam, log_rat(2*lam)), scale(-(nu-1), I))
coarse_C = -F(523707,250000)
assert C[0] > coarse_C
assert C[1] < -F(2094827,1000000)

# Existing draft strip integrals (input facts, not re-proved by this script).
known = F(5663,6400)+F(9289,11520)
assert known == F(24353,14400)
remaining_H0 = 7*(lam*alpha + (F(1,3)-F(1,18)) - (alpha-alpha*alpha/2))
assert remaining_H0 == F(55433,28800)

# Fresh repaired endpoint in U-e49-reproduction/summary.json, nu6_dual.
# This exact comparison is not a reproduction of its interval integration.
repaired_LB = -F(7194429009109924539696843951238889,
                 5192296858534827628530496329220096)
assert repaired_LB > -F(693,500)

cases=[]
for cutoff, analytic_lower in [(48,-F(693,500)), (50,-F(139,100))]:
    loss = 7*lam/cutoff
    growth = coarse_C+known+remaining_H0-loss+analytic_lower
    assert growth > 0
    cases.append({"cutoff":cutoff,"analytic_lower":show(analytic_lower),
                  "discarded_H0_budget":show(loss),"growth_lower":show(growth),
                  "remaining_integer_quotients":[3,cutoff-1]})
assert F(cases[0]["growth_lower"]["exact"]) == F(641,3000000)
assert F(641,3000000) > F(1,5000)

# Smallest cutoff supported by each coarse rational budget, not a theorem
# that any smaller cutoff is intrinsically impossible.
minimum_cutoffs={}
for lower in [-F(693,500),-F(139,100)]:
    minimum_cutoffs[str(lower)] = next(c for c in range(14,200)
        if coarse_C+known+remaining_H0-7*lam/c+lower > 0)
assert minimum_cutoffs == {"-693/500":48,"-139/100":50}
deficit_budgets = {str(c):show(coarse_C+known+remaining_H0-7*lam/c-F(693,500))
                   for c in [48,50,60,100]}

out={"status":"COMPUTED exact rational comparisons; conditional mathematics in primitive-review.md",
     "source_snapshot":"dc1a24b4bbe420688f533c0fc68e19bc53d9a224",
     "log_series_terms":24,
     "C_infinity_lower":show(C[0]),"C_infinity_upper":show(C[1]),
     "coarse_C_lower":show(coarse_C),"inherited_known_polarity":show(known),
     "remaining_H0_integral":show(remaining_H0),"repaired_energy_endpoint":show(repaired_LB),
     "cases":cases,"minimum_cutoffs_for_these_coarse_budgets":minimum_cutoffs,
     "aggregate_deficit_budgets_with_lower_minus_693_over_500":deficit_budgets}
target=Path(__file__).with_name("primitive-budget.json")
target.write_text(json.dumps(out,indent=2)+"\n")
print("PASS: exact C_infinity enclosure, source-endpoint comparison, and both cutoff budgets")
for c in cases:
    print("cutoff",c["cutoff"],"growth lower",c["growth_lower"]["exact"])
