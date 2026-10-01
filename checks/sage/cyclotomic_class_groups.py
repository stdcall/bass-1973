"""XI (6.2): class numbers for the two specified cyclotomic rings.

Sage's unconditional class-group computation is requested explicitly.
This check says nothing about other group rings or other cyclotomic fields.
"""
from sage.all import CyclotomicField, QQ, RealIntervalField, Zmod, factorial

for conductor, discriminant in ((3, -3), (9, -19683)):
    field = CyclotomicField(conductor)
    assert field.discriminant() == discriminant
    assert field.class_group(proof=True).order() == 1

# The second field has degree six and three pairs of complex embeddings.
# Its Minkowski bound is below 9/2. There are no ideals of norm two or four:
# the prime two has residue degree six. The prime above three is principal.
intervals = RealIntervalField(100)
bound = (4 / intervals.pi())**3 * (QQ(factorial(6)) / 6**6) * intervals(19683).sqrt()
assert bound.upper() < QQ(9) / 2
assert Zmod(9)(2).multiplicative_order() == 6
assert (1 - CyclotomicField(9).gen()).norm() == 3

print('XI (6.2): class numbers of Z[zeta_3] and Z[zeta_9] are one; '
      'exact checks passed')
