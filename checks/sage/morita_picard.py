"""Глава II, (3.3) и (5.1): два точных контрпримера к исходным чтениям.

1. Ситуация Мориты A=B=P=Q=F_5 с f=g=0. Тензорный функтор
   с единичным модулем сохраняет морфизмы, но g не разделяет элементы Q.
   Проверяются все четыре скаляра в ассоциативных тождествах.
2. Для A=F_5^3 обратимые бимодули переставляют простые слагаемые.
   Их тензорное произведение соответствует произведению матриц слева
   направо в размерностной строке правого модуля. Композиция функторов
   меняет порядок. Две перестановки дают разные результаты.

Это проверки конкретных примеров; общие теоремы Мориты, плоскость и
классификация всех обратимых бимодулей здесь не доказываются.
"""
import json
from sage.all import GF, matrix, vector
from sage.env import SAGE_VERSION


def degenerate_context():
    k = GF(5)
    f = lambda p, q: k.zero()
    g = lambda q, p: k.zero()
    count = 0
    for p in k:
        for q in k:
            for pp in k:
                for qq in k:
                    assert f(p, q) * pp == p * g(q, pp)
                    assert g(q, p) * qq == q * f(p, qq)
                    count += 1
    d = k.one()
    assert d != 0
    assert all(g(d, p) == 0 for p in k)
    # Tensoring a scalar map with the unit module is the same scalar map.
    assert all(matrix(k, [[a]]) == matrix(k, [[a]]).tensor_product(
        matrix(k, [[1]])) for a in k)
    return {'field': 'F_5', 'associativity_cases': count,
            'nonzero_unseparated_element': str(d)}


def reversed_composition():
    k = GF(5)
    sigma = matrix(k, [[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    tau = matrix(k, [[1, 0, 0], [0, 0, 1], [0, 1, 0]])
    assert sigma.is_invertible() and tau.is_invertible()
    x = vector(k, [1, 0, 0])
    tensor_product = x * (sigma * tau)
    # h(P ⊗ Q)=h(Q)∘h(P), as follows from associativity of tensor products.
    assert tensor_product == (x * sigma) * tau
    usual_product_of_functors = (x * tau) * sigma
    assert tensor_product != usual_product_of_functors
    return {'ring': 'F_5 × F_5 × F_5',
            'h_PQ': list(map(int, tensor_product)),
            'h_P_after_h_Q': list(map(int, usual_product_of_functors))}


if __name__ == '__main__':
    print(json.dumps({'sage': SAGE_VERSION,
                      'morita_context': degenerate_context(),
                      'picard_composition': reversed_composition()},
                     ensure_ascii=False, indent=2))
