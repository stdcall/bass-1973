"""Page 572: the missing odd-prime hypothesis in the norm-symbol formula.

For C_2^4 the nontrivial rational characters form 15 points. The parity
q_a(chi)=(a_chi-1)/2 mod 2 of any Z_2[C_2^4] unit is an affine function
of chi. For odd a_chi,b_chi, the quadratic Hilbert symbol is
(-1)^(q_a(chi)*q_b(chi)). Its exponent therefore has degree at most two.

This finite calculation verifies the dimension of that exponent space.
It does not compute a K-group or prove the general repaired theorem.
"""
from sage.all import GF, VectorSpace, matrix

field = GF(2)
characters = [x for x in VectorSpace(field, 4) if x]
assert len(characters) == 15

affine_functions = []
for coefficients in VectorSpace(field, 5):
    affine_functions.append([
        coefficients[0] + sum(coefficients[i + 1] * x[i] for i in range(4))
        for x in characters
    ])
products = matrix(field, [
    [a[i] * b[i] for i in range(15)]
    for a in affine_functions for b in affine_functions
])
assert products.nrows() == 1024
assert products.rank() == 11

monomials = [[field.one()] * 15]
monomials.extend([[x[i] for x in characters] for i in range(4)])
monomials.extend([
    [x[i] * x[j] for x in characters]
    for i in range(4) for j in range(i + 1, 4)
])
quadratics = matrix(field, monomials)
assert quadratics.rank() == 11
assert products.row_space() == quadratics.row_space()
assert 15 - products.rank() == 4

print('Page 572: 1024 products of affine functions on 15 characters; '
      'rank 11, quotient dimension 4; exact check passed')
