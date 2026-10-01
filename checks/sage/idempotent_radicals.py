"""III §3, p.96: radical of an idempotent ideal in finite nonreduced rings.

Exhaustive checks in F_p[t]/(t²) and F_p × F_p[t]/(t²), p=2,3,5.
They verify sqrt(eA)=eA+nil(A), and uniqueness from equal radicals, in
these rings only. The general radical equality is not proved by this test.
"""
from itertools import product
import json
from sage.env import SAGE_VERSION


def check_ring(p, extra_factor):
    elements = list(product(range(p), repeat=3 if extra_factor else 2))
    zero = elements[0]

    def add(x, y):
        return tuple((a+b) % p for a, b in zip(x, y))

    def mul(x, y):
        dual = ((x[-2]*y[-2]) % p,
                (x[-2]*y[-1]+x[-1]*y[-2]) % p)
        return ((x[0]*y[0] % p,) + dual) if extra_factor else dual

    def radical(ideal):
        answer = set()
        for x in elements:
            power = x
            seen = set()
            while power not in seen:
                if power in ideal:
                    answer.add(x)
                    break
                seen.add(power)
                power = mul(power, x)
        return answer

    nil = radical({zero})
    idempotents = [e for e in elements if mul(e, e) == e]
    radicals = {}
    for e in idempotents:
        ideal = {mul(e, a) for a in elements}
        rad = radical(ideal)
        assert rad == {add(a, n) for a in ideal for n in nil}
        radicals[e] = rad
    for e, f in product(idempotents, repeat=2):
        assert (radicals[e] == radicals[f]) == (e == f)
    epsilon = (0,)*(len(zero)-1)+(1,)
    assert epsilon != zero and mul(epsilon, epsilon) == zero
    assert radical({zero}) != {zero}
    return {'p': p, 'product_factor': extra_factor,
            'elements': len(elements), 'idempotents': len(idempotents)}


if __name__ == '__main__':
    print(json.dumps({'sage': SAGE_VERSION,
                      'rings': [check_ring(p, extra) for p in (2, 3, 5)
                                for extra in (False, True)]}, indent=2))
