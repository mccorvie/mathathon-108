#!/usr/bin/env python3
"""Independent COMPUTED checks; no determinant computation or Lean verification.

The logarithm enclosure uses the unreduced arguments and 96 odd-series terms,
independent of primitive-budget.py's range-reduced 24-term implementation.
Pole counts are constructed by enumerating signed integer poles, not floors.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import math


def log_bounds(x):
    z = (x - 1) / (x + 1)
    mid = 2 * sum((z ** (2 * j + 1) / (2 * j + 1)
                   for j in range(96)), Q(0))
    err = 2 * abs(z) ** 193 / (193 * (1 - z * z))
    return mid - err, mid + err


alpha, lam = Q(3, 40), Q(37, 40)
# Expanded directly from the frozen root-polarity Lemma 2.
constant = 2 * lam - 12 * lam * alpha - 3 * lam * lam + 15 * alpha * (1-alpha)
log_terms = [(12 * lam * alpha, alpha), (2 * lam * lam, 2 * lam),
             (-Q(5, 2) * (1+alpha)**2, 1+alpha),
             (Q(5, 2) * (1-alpha)**2, 1-alpha),
             (Q(5, 2) * (2*alpha)**2, 2*alpha)]
c_lo = c_hi = constant
for coefficient, argument in log_terms:
    lo, hi = log_bounds(argument)
    c_lo += coefficient * (lo if coefficient >= 0 else hi)
    c_hi += coefficient * (hi if coefficient >= 0 else lo)
assert -Q(523707, 250000) < c_lo <= c_hi < -Q(2094827, 1000000)
assert c_hi-c_lo < Q(1, 10**12)

known = Q(5663, 6400) + Q(9289, 11520)
assert known == Q(24353, 14400)
# Integrate the retained profile directly, rather than subtracting the lost band.
retained = 7 * (lam * (alpha-Q(1,48))
                + Q(1,3)-Q(1,18)-alpha+alpha*alpha/2)
assert retained == Q(55433,28800)-Q(259,1920)
base = -Q(523707,250000)+known+Q(55433,28800)
budgets = {c: base-7*lam/c-Q(693,500) for c in (48,50,60,100)}
assert budgets[48] == Q(641,3000000) > Q(1,5000)
assert base-7*lam/50-Q(139,100) == Q(3219,2000000)
endpoint = -Q(7194429009109924539696843951238889,
              5192296858534827628530496329220096)
assert endpoint > -Q(693,500)


def prime(p):
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p)+1))


pairs = 0
class_count = 0
smallest_p = None
largest_ordinary_degree = largest_zero_degree = 0
for n in range(1, 61):
    K, N, h = 40*n, 3*n, 37*n
    for p in range(K//3+1, 17*n+1):
        if not prime(p):
            continue
        pairs += 1
        smallest_p = min(smallest_p or p, p)
        assert p >= 17 and 2*N < p and 2*p < K < 3*p and p*p > 5*K
        m = (p-1)//2
        # Full near-root sets for each source c, from signed poles +/-j.
        roots = [[] for _ in range(p)]
        ell = [0] * (m+1)
        ell_n = [0] * (m+1)
        for j in range(1, K+1):
            for sign in (-1,1):
                v = sign*j
                c = v % p
                roots[c].append((v-c)//p)
            a = min(j%p, (-j)%p)
            ell[a] += 1
            if j <= N:
                ell_n[a] += 1
        assert roots[0] == [-1,1,-2,2]
        assert ell[0] == 2 and ell_n[0] == 0
        for c in range(1,p):
            assert len(roots[c]) == len(set(roots[c]))
            assert min(roots[c]) >= -3 and max(roots[c]) <= 2
            assert max(roots[c])-min(roots[c]) < p
            assert all(abs(r) < p for r in roots[c])
        T, E = divmod(h-2+4*N,m)
        eps = [0]*(m+1)
        for a in sorted(range(1,m+1), key=lambda a: (-ell[a],a))[:E]:
            eps[a]=1
        allocation = [2] + [T-4*ell_n[a]+eps[a] for a in range(1,m+1)]
        assert sum(allocation)==h and min(allocation)>=1 and 5<=T<=7
        q = 5 if p<16*n else 4
        assert all(ell[a] in (q,q+1) for a in range(1,m+1))
        if p<16*n:
            assert T>=6
        else:
            assert T<=6
        source_halves2=[]
        row_tops2=[]
        for a in range(1,m+1):
            # Degree after extracting the source valuation from both rows.
            degree = 2*allocation[a]+8*ell_n[a]
            assert degree<=2*(T+1)<=16<=p+1
            largest_ordinary_degree=max(largest_ordinary_degree, degree)
            source_halves2.append(2*allocation[a]+8*ell_n[a]-ell[a]-4)
            row_tops2.append(2*(allocation[a]-1)+8*ell_n[a]-ell[a]-4)
        assert min(source_halves2)>=max(row_tops2)
        assert min(source_halves2)>=1 and max(row_tops2)<=5
        assert 5+4*allocation[0]==13<=p+1
        largest_zero_degree=max(largest_zero_degree, 5+4*allocation[0])
        class_count += m

out = {
    'status':'COMPUTED; mathematical deductions remain PROOF-DRAFT',
    'frozen_source':'dc1a24b4bbe420688f533c0fc68e19bc53d9a224',
    'constant_enclosure_diagnostic':[float(c_lo),float(c_hi)],
    'constant_enclosure_width_less_than':'1/1000000000000',
    'cutoff_budgets':{str(c):str(v) for c,v in budgets.items()},
    'nu8_n_range':[1,60], 'nu8_pairs':pairs,
    'ordinary_classes_checked':class_count, 'smallest_prime':smallest_p,
    'largest_ordinary_leading_degree':largest_ordinary_degree,
    'largest_zero_leading_degree':largest_zero_degree,
    'scope':'Exact logarithm/budget arithmetic, enumerated local-pole hypotheses, CRT allocation and source inequalities. No determinant valuations, interval-energy recomputation or Lean gate.'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
