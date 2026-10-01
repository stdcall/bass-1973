"""Exact finite checks of elementary and Whitehead block identities.

Passages: prop:elementary-matrix-identities, especially
cond:elementary-upper-triangular-conjugation (V1.2(c)), and
prop:whitehead-lemma (V1.7), printed pages182–183,186–187.

The commutator convention is [x,y]=x^{-1}y^{-1}xy and x^y=y^{-1}xy.
Blocks are 2 by2 matrices, so their products need not commute.
The upper triangular check uses a fixed, explicitly specified family over
F3. Whitehead factorizations use every a,b in GL2(F3), then every a in
GL2(Z/4) and every b congruent to I modulo2. The latter checks the
nonzero proper two-sided ideal2(Z/4).
These finite matrix identities do not prove the general statements for
arbitrary rings or the classification of normal subgroups.
"""

from itertools import product
from sage.all import GF, Integers, MatrixSpace, block_matrix, identity_matrix, matrix, zero_matrix

checks = 0


def equal(actual, expected):
    global checks
    assert actual == expected
    checks += 1


def block(a, b, c, d):
    return block_matrix([[a, b], [c, d]])


def commutator(x, y):
    return x.inverse() * y.inverse() * x * y


def conjugate(x, y):
    return y.inverse() * x * y


def all_units(ring):
    entries = list(ring)
    return [a for row in product(entries, repeat=4)
            if (a := matrix(ring, 2, 2, row)).det().is_unit()]


field = GF(3)
space = MatrixSpace(field, 2)
one = identity_matrix(field, 2)
zero = zero_matrix(field, 2)
upper = lambda x: block(one, x, zero, one)
family = [zero, one] + list(space.basis())
family += [matrix(field, [[1, 1], [1, 0]]),
           matrix(field, [[0, 1], [2, 1]])]
units = [one, -one, matrix(field, [[1, 1], [0, 1]]),
         matrix(field, [[1, 0], [1, 1]]),
         matrix(field, [[0, 1], [2, 0]])]
triangular_cases = 0
for a, b, u, v in product(family, family, units, units):
    x = upper(a)
    y = block(u, b, zero, v)
    expected = upper(u.inverse() * a * v)
    equal(conjugate(x, y), expected)
    equal(commutator(x, y), upper(u.inverse() * a * v - a))
    left = upper(b * v.inverse())
    right = block(u, zero, zero, v)
    equal(y, left * right)
    equal(left * x, x * left)
    triangular_cases += 1

# Refutation of the printed "last factor commutes": the diagonal factor
# fails already for u=diag(1,2), v=I, a=I. The corrected first factor is
# verified in every triangular case above.
bad_diagonal = block(matrix(field, [[1, 0], [0, 2]]), zero, zero, one)
assert bad_diagonal * upper(one) != upper(one) * bad_diagonal
checks += 1


def whitehead(ring, a_values, b_values, relative=False):
    one = identity_matrix(ring, 2)
    zero = zero_matrix(ring, 2)
    up = lambda x: block(one, x, zero, one)
    low = lambda x: block(one, zero, x, one)
    equal(up(one) * low(-one) * up(one), block(zero, one, -one, zero))
    first_cases = 0
    last_cases = 0
    for b in b_values:
        q = b - one
        bi = b.inverse()
        expected = block(b, zero, zero, bi)
        equal(up(q) * low(one) * up(-bi * q) * low(-b), expected)
        equal(up(q) * conjugate(up(-bi * q), low(-one)) * low(-q), expected)
        if relative:
            assert all(int(x) % 2 == 0 for x in q.list())
            assert all(int(x) % 2 == 0 for x in (bi * q).list())
        first_cases += 1
        for a in a_values:
            ai = a.inverse()
            equal(block(a, zero, zero, b) * expected,
                  block(a * b, zero, zero, one))
            last = up((b * a).inverse() * q)
            last *= conjugate(up(-ai * q), low(a))
            last *= low(-bi * q * a)
            equal(last, block(ai * bi * a, zero, zero, b))
            equal(block(b * a, zero, zero, one).inverse()
                  * block(a, zero, zero, b), last)
            if relative:
                for coefficient in [(b * a).inverse() * q, ai * q, bi * q * a]:
                    assert all(int(x) % 2 == 0 for x in coefficient.list())
            last_cases += 1
    return first_cases, last_cases


field_units = all_units(field)
assert len(field_units) == 48
field_first, field_last = whitehead(field, field_units, field_units)
ring = Integers(4)
ring_units = all_units(ring)
one4 = identity_matrix(ring, 2)
congruence_units = [b for b in ring_units
                   if all(int(x) % 2 == 0 for x in (b - one4).list())]
assert len(ring_units) == 96 and len(congruence_units) == 16
relative_first, relative_last = whitehead(ring, ring_units, congruence_units, relative=True)
print(f"ok linear_block_identities: {checks} checks; "
      f"triangular={triangular_cases}, "
      f"Whitehead(F3)={field_first}+{field_last}, "
      f"Whitehead(Z/4,2)={relative_first}+{relative_last}")
