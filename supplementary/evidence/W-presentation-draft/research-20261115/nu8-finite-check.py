#!/usr/bin/env python3
"""Exact finite checks of the nu=8 range proof; no determinant valuations are computed.

Codex, 15 Nov 2026 UTC. Independent implementation from the displayed definitions.
This checks admissibility, the finite allocation sum, and the full normalizer offset.
It does not prove the p-adic local lemma or the determinant valuation inequality.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def primes(bound):
    sieve = bytearray(b"\1") * (bound + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, int(bound**0.5) + 1):
        if sieve[p]:
            sieve[p*p::p] = b"\0" * len(sieve[p*p::p])
    return [i for i in range(2, bound + 1) if sieve[i]]


def vp_factorial(n, p):
    total = 0
    while n:
        n //= p
        total += n
    return total


def gamma_integral(K, p):
    """Direct exact integration of Gamma, not the five-case error formula."""
    x, alpha, H = F(K, p), F(3, 40), F(49, 40)
    T0, q = (2*H*x).__floor__(), (2*x).__floor__()
    sigma, nplus = H*x - F(T0, 2), x - F(q, 2)
    cuts = {F(0), F(1, 2)}
    for u in [x, alpha*x]:
        for k in range(u.__floor__() - 1, u.__floor__() + 3):
            for z in [u-k, k-u]:
                if 0 < z < F(1, 2):
                    cuts.add(z)
    cuts = sorted(cuts)
    integral = F(0)
    for left, right in zip(cuts, cuts[1:]):
        z = (left + right)/2
        ell = (x-z).__floor__() + (x+z).__floor__() + 1
        b = 4*((alpha*x-z).__floor__() + (alpha*x+z).__floor__() + 1)
        integral += (right-left)*(T0-b)*(T0+b-ell-5)
    return integral + sigma*(2*T0-q-5) + max(sigma-nplus, F(0))


def Nfun(K, p):
    x, lam = F(K, p), F(37, 40)
    j = (2*lam*x).__floor__()
    J = j*lam*x - F(j*(j+1), 4)
    return 2*lam*x*x.__floor__() - 16*lam*x*(F(3,40)*x).__floor__() - 2*J


def expected_offset(y):
    if y < F(7, 20): return F(18)
    if y <= F(43, 120): return F(33, 2)
    if y < F(37, 100): return F(25, 2)
    if y < F(2, 5): return F(23, 2)
    if y < F(49, 120): return F(12)
    return F(11)


def check(n, p):
    K, N, h, m = 40*n, 3*n, 37*n, (p-1)//2
    T, E = divmod(h-2+4*N, m)
    ell = [(K-a)//p + 1 + (K+a)//p for a in range(1,m+1)]
    b = [4*int(a<=N) for a in range(1,m+1)]
    eps = [0]*m
    for a in sorted(range(m), key=lambda a: (-ell[a], a))[:E]: eps[a]=1
    L = [T-b[a]+eps[a] for a in range(m)]
    half2 = [2*(T+eps[a])-ell[a]-4 for a in range(m)]
    tops2 = [2*(T+eps[a]-1)-ell[a]-4 for a in range(m)]
    assert p>=17 and N*2<p and 2*p<K<3*p and p*p>5*K
    assert 5<=T<=7 and min(L)>=1 and 2+sum(L)==h
    assert 2*(T+1)<=p+1 and 13<=p+1
    assert min(half2)>=max(tops2) and max(tops2)<=5 and min(half2)>=1
    assert set(ell).issubset({4,5}) if p>16*n else set(ell).issubset({5,6})
    gamma = sum(L[a]*(L[a]+2*b[a]-ell[a]-5) for a in range(m))-2
    pGamma = p*gamma_integral(K,p)
    vS = 2*h*vp_factorial(K,p)-16*h*vp_factorial(N,p)-2*sum(vp_factorial(2*i,p) for i in range(1,h))
    scalar_offset = vS-p*Nfun(K,p)
    assert scalar_offset == F(((2*h//p)+1)//2)
    offset = gamma-pGamma+scalar_offset
    assert offset==expected_offset(F(p,K)), (K,p,offset)
    return offset, (T != (F(98*n,p)).__floor__())


if __name__ == '__main__':
    nmax=200
    ps=primes(17*nmax)
    histogram={}
    count=exceptions=0
    for n in range(1,nmax+1):
        for p in ps:
            if 40*n<3*p and p<=17*n:
                offset, exceptional=check(n,p)
                count+=1; exceptions+=exceptional
                histogram[str(offset)]=histogram.get(str(offset),0)+1
    result={'status':'COMPUTED','nmax':nmax,'Kmax':40*nmax,'pairs':count,
            'exceptional_T_cases':exceptions,'full_normalizer_offsets':histogram,
            'all_checks_passed':True,
            'scope':'Admissibility, allocation and scalar identities only; no determinant valuation computation or Lean gate.'}
    out=Path(__file__).with_name('nu8-finite-check.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
