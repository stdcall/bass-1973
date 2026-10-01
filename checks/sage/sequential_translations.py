"""I (8.6), prop:sequential-cofinal-translations: a concrete counterexample.

The commutative monoid is the nonnegative integers with an absorbing
infinity. Put a_0=0; a_i=infinity if i=1 modulo4, and a_i=2^i otherwise.
Every tail contains infinity. For each a,n, taking m to be the next
index congruent to1 modulo4 and b=infinity proves condition(S).

All partial sums s_n for n>=1 equal infinity. The selected intervals
a_(1,3)=12 and a_(1,4)=28 are loops at infinity, but their composite has
label40. No interval has that label: an interval containing infinity
cannot; a finite interval containing a term with index>=6 is at least64;
the finite intervals within indices0 through5 are enumerated below.
Thus the selected arrows are not closed under composition.

The enumeration and some cofinal witnesses are checked exactly. The
two general tail bounds above are elementary arguments, not an infinite
enumeration. This does not prove the general cofinality theorem.
"""
from sage.all import ZZ

INF = None


def add(a, b):
    return INF if a is INF or b is INF else a + b


def term(i):
    if i == 0:
        return ZZ(0)
    return INF if i % 4 == 1 else ZZ(2) ** i


def interval(n, m):
    total = ZZ(0)
    for i in range(n + 1, m + 1):
        total = add(total, term(i))
    return total


assert interval(0, 1) is INF
assert interval(1, 3) == 12 and interval(1, 4) == 28
assert interval(0, 3) is INF and interval(0, 4) is INF
assert add(interval(1, 3), interval(1, 4)) == 40
finite_labels = {interval(n, m) for n in range(6) for m in range(n, 6)}
finite_labels.discard(INF)
assert finite_labels == {0, 4, 8, 12, 16, 24, 28}
assert 40 not in finite_labels
assert ZZ(2) ** 6 == 64 > 40

witnesses = 0
for n in range(32):
    m = 4 * (n // 4) + 1
    if m <= n:
        m += 4
    assert m > n and m % 4 == 1 and term(m) is INF
    assert interval(n, m) is INF
    for a in [ZZ(i) for i in range(129)] + [INF]:
        assert add(a, INF) == interval(n, m)
        witnesses += 1
print(f'ok sequential_translations: {witnesses} cofinal witnesses; '
      '12+28=40 is absent from all possible finite interval labels')
