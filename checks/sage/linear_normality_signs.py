"""Exact finite checks for V, proof of Lemma (5.2), final paragraph.

The convention is [x,y]=x^(-1)y^(-1)xy and x^y=y^(-1)xy.
The matrices epsilon=I-s1*e31-s2*e32 and tau=I+t*e12 satisfy
epsilon*t*e12*epsilon^(-1)=t*e12-s1*t*e32. Consequently the bottom
row of epsilon*tau^(-1)*epsilon^(-1) is (0,s1*t,1).

Coverage: all triples over F5 and 125 triples from an explicit five-element
subset of M2(F3). This verifies the written block identities on these finite
inputs only. It also exhibits counterexamples to the two printed intermediate
equalities. The general identities follow by multiplication and e_ij e_kl
=delta_jk e_il; the finite computation is not a proof over arbitrary rings.
"""

import json
from itertools import product
from sage.all import GF, MatrixSpace, block_matrix, identity_matrix, zero_matrix


count = 0


def equal(left, right):
    global count
    assert left == right
    count += 1


def checks(field, block_size, coefficients):
    one = identity_matrix(field, block_size)
    zero = zero_matrix(field, block_size)
    identity = identity_matrix(field, 3 * block_size)

    def blocks(rows):
        return block_matrix(rows)

    for s1, s2, t in product(coefficients, repeat=3):
        epsilon = blocks([[one, zero, zero], [zero, one, zero], [-s1, -s2, one]])
        inverse = blocks([[one, zero, zero], [zero, one, zero], [s1, s2, one]])
        te12 = blocks([[zero, t, zero], [zero, zero, zero], [zero, zero, zero]])
        s1te32 = blocks([[zero, zero, zero], [zero, zero, zero], [zero, s1 * t, zero]])
        tau = identity + te12
        equal(epsilon * inverse, identity)
        equal(epsilon * te12 * inverse, te12 - s1te32)
        conjugate = epsilon * tau.inverse() * inverse
        equal(conjugate, identity - te12 + s1te32)
        bottom_row = conjugate[2 * block_size:3 * block_size, :]
        equal(bottom_row, block_matrix([[zero, s1 * t, one]]))

    s1 = one
    s2 = zero
    t = one
    epsilon = blocks([[one, zero, zero], [zero, one, zero], [-s1, -s2, one]])
    te12 = blocks([[zero, t, zero], [zero, zero, zero], [zero, zero, zero]])
    s1te32 = blocks([[zero, zero, zero], [zero, zero, zero], [zero, s1 * t, zero]])
    tau = identity + te12
    actual = epsilon * te12 * epsilon.inverse()
    assert actual != te12 + s1te32
    assert epsilon * tau.inverse() * epsilon.inverse() != tau.inverse() + actual
    return {
        "triples": len(coefficients) ** 3,
        "s1": str(s1), "s2": str(s2), "t": str(t),
        "epsilon_te12_epsilon_inverse": str(actual),
        "epsilon_tau_inverse_epsilon_inverse_bottom_row": str(
            (epsilon * tau.inverse() * epsilon.inverse())[2 * block_size:3 * block_size, :]
        ),
        "refuted_readings": [
            "epsilon*t*e12*epsilon^(-1)=t*e12+s1*t*e32",
            "epsilon*tau^(-1)*epsilon^(-1)=tau^(-1)+epsilon*t*e12*epsilon^(-1)",
        ],
    }


field5 = GF(5)
scalar = [MatrixSpace(field5, 1)([a]) for a in field5]
field3 = GF(3)
space = MatrixSpace(field3, 2)
basis = list(space.basis())
noncommutative = [space.zero(), space.one(), basis[0], basis[1], basis[2]]
results = {
    "passage": "V, Lemma (5.2), final paragraph",
    "declarations": ["lem:noncentral-elementary-normalized-subgroup"],
    "scalar_F5": checks(field5, 1, scalar),
    "matrix_ring_M2_F3": checks(field3, 2, noncommutative),
    "limitations": "Finite inputs; no conclusion for all rings from enumeration.",
}
results["checked_equalities"] = count
print(json.dumps(results, ensure_ascii=False, indent=2))
