"""III (2.10): exact polynomial congruences for 1 ≤ n ≤ 12 over Z.

The finite range checks the binomial construction and its compatibility.
It does not prove the lifting theorem for arbitrary n or adic completeness.
"""
import json
from sage.all import PolynomialRing, ZZ, binomial
from sage.env import SAGE_VERSION


def check():
    ring = PolynomialRing(ZZ, 'a')
    a = ring.gen()
    previous = None
    results = []
    for n in range(1, 13):
        f = sum(binomial(2*n, j) * a**(2*n-j) * (1-a)**j
                for j in range(n+1))
        assert f % a**n == 0
        assert (f-1) % (1-a)**n == 0
        assert (f*f-f) % (a*(1-a))**n == 0
        assert (f-a) % (a*(1-a)) == 0
        if previous is not None:
            assert (f-previous) % (a*(1-a))**(n-1) == 0
        results.append({'n': n, 'degree': int(f.degree())})
        previous = f
    assert a*a + 2*a*(1-a) == 2*a-a*a
    assert a*a-a == a*(a-1)
    assert a*a-a != a*(1-a)
    return results


if __name__ == '__main__':
    print(json.dumps({'sage': SAGE_VERSION, 'ring': 'Z[a]',
                      'checked_polynomials': check()}, indent=2))
