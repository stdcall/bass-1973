"""Exact finite counterexample to the module-extension step in IX (5.9).

k=F2, B=k[x]/(x^8), A=k+x^2 B, I=x^4 A, M=A/I.
N=M(x^2 B) has basis x^2,x^3,x^5. Every 3x3 matrix over k is
checked as a possible action of x extending the given A-action on N.
This does not disprove the epimorphisms asserted by the proposition.
"""
from itertools import product
import json
from sage.all import GF, PolynomialRing, MatrixSpace, vector
from sage.env import SAGE_VERSION

k = GF(2)
P = PolynomialRing(k, 'x')
x = P.gen()
B = P.quotient(x**8, 't')
t = B.gen()
degrees_A = (0, 2, 3, 4, 5, 6, 7)
degrees_I = (4, 6, 7)
degrees_M = (0, 2, 3, 5)
degrees_N = (2, 3, 5)
assert all((a+b >= 8 or a+b in degrees_A) for a in degrees_A for b in degrees_A)
assert all((a+b >= 8 or a+b in degrees_I) for a in degrees_I for b in degrees_A)

def action(power):
    columns = []
    for degree in degrees_N:
        exponent = degree + power
        columns.append(vector(k, [int(exponent == target) for target in degrees_N]))
        assert exponent >= 8 or exponent in degrees_I or exponent in degrees_N
    return MatrixSpace(k, 3)(columns).transpose()

X2, X3 = action(2), action(3)
v = vector(k, (1, 0, 0))
assert X2*v == 0
assert X3*v != 0
assert X2*X3 == X3*X2
space = MatrixSpace(k, 3)
checked = 0
for coefficients in product(k, repeat=9):
    X = space(coefficients)
    checked += 1
    assert not (X**2 == X2 and X**3 == X3)
assert checked == 512
print(json.dumps({
    'sage': SAGE_VERSION,
    'field': 'F2',
    'ring': 'F2[x]/(x^8)',
    'basis_N': ['x^2', 'x^3', 'x^5'],
    'possible_x_actions_checked': checked,
    'extending_actions': 0,
    'scope': 'One counterexample to the printed module-extension step only',
}))
