#import "commutative.typ": cd, edge

#let matrix-notation() = cd(
  cell-size: (23mm, 17mm),
  $D & & & & E \ A_1 product.co A_2 & & C & & B_1 product B_2 \ & A_i & & B_j
  & \ & A'_i & & B'_j & \ A'_1 product.co A'_2 & & & & B'_1 product B'_2$,
  edge((0, 1), (0, 0), $(d a_1, d a_2)$, "->", label-side: right),
  edge((2, 1), (0, 0), $d$, "->"),
  edge((4, 0), (2, 1), $e$, "->"),
  edge((4, 0), (4, 1), $mat(b_1 e; b_2 e)$, "->"),
  edge((0, 1), (2, 1), $a = (a_1, a_2)$, "->"),
  edge((2, 1), (4, 1), $b = mat(b_1; b_2)$, "->"),
  edge((1, 2), (0, 1), $q_i$, "->", label-side: right),
  edge((1, 2), (2, 1), $a_i$, "->", label-side: right),
  edge((2, 1), (3, 2), $b_j$, "->"),
  edge((4, 1), (3, 2), $p_j$, "->", label-side: right),
  edge((1, 3), (1, 2), $s_i$, "->"),
  edge((3, 2), (3, 3), $t_j$, "->"),
  edge((1, 3), (0, 4), $q'_i$, "->", label-side: right),
  edge((4, 4), (3, 3), $p'_j$, "->", label-side: right),
  edge((0, 4), (0, 1), $s_1 product.co s_2$, "->", label-side: right),
  edge((0, 4), (2, 1), $(a_1 s_1, a_2 s_2)$, "->", label-side: right),
  edge((2, 1), (4, 4), $mat(t_1 b_1; t_2 b_2)$, "->", label-side: right),
  edge((4, 1), (4, 4), $t_1 product t_2$, "->"),
)

#let addition-definition() = cd(
  cell-size: (25mm, 16mm),
  $A & & & & B \ & A product A & A xor A & A product.co A & \ & B product B &
  B xor B & B product.co B &$,
  edge((0, 0), (4, 0), $a + b$, "->"),
  edge((0, 0), (1, 1), $Delta_A$, "->"),
  edge((0, 0), (1, 2), $mat(a; b)$, "->", label-side: right),
  edge((1, 1), (2, 1), "="),
  edge((2, 1), (3, 1), "="),
  edge((1, 1), "d", $a product b$, "->", label-side: right),
  edge((2, 1), "d", $a xor b$, "->"),
  edge((3, 1), "d", $a product.co b$, "->"),
  edge((1, 2), (2, 2), "="),
  edge((2, 2), (3, 2), "="),
  edge((3, 1), (4, 0), $(a, b)$, "->"),
  edge((3, 2), (4, 0), $Sigma_B$, "->"),
)

#let addition-zero() = cd(
  cell-size: (35mm, 18mm),
  $A & A \ A product A & A product.co A$,
  edge((0, 0), "r", $1$, "->"),
  edge((0, 0), "d", $Delta_A$, "->", label-side: right),
  edge((0, 1), (1, 0), $p_1$, "->"),
  edge((1, 1), "u", $mat(1; 0)$, "->", label-side: right),
  edge((1, 1), "l", $phi_(A, A)$, "->"),
)

#let matrix-composition() = cd(
  cell-size: (35mm, 19mm),
  $C & A_1 xor A_2 & D \ C xor C & & D xor D$,
  edge((0, 0), "r", $mat(c_1; c_2)$, "->"),
  edge((1, 0), "r", $(d_1, d_2)$, "->"),
  edge((0, 0), "d", $Delta_C$, "->", label-side: right),
  edge((2, 0), "d", $Sigma_D$, "->"),
  edge((0, 1), (1, 0), $c_1 xor c_2$, "->"),
  edge((1, 0), (2, 1), $d_1 xor d_2$, "->", label-side: right),
  edge((0, 1), (2, 1), $d_1 c_1 xor d_2 c_2$, "->", label-side: right),
)

#let biproduct-identities() = cd(
  cell-size: (28mm, 14mm),
  $A_1 & A & A_2$,
  edge((0, 0), "r", $q_1$, "->", shift: 1.4mm, label-side: left),
  edge((1, 0), "l", $p_1$, "->", shift: 1.4mm, label-side: left),
  edge((1, 0), "r", $p_2$, "->", shift: 1.4mm, label-side: left),
  edge((2, 0), "l", $q_2$, "->", shift: 1.4mm, label-side: left),
)

#let additive-square() = cd(
  cell-size: (28mm, 17mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", $b_2$, "->"),
  edge((0, 0), "d", $b_1$, "->", label-side: right),
  edge((1, 0), "d", $a_2$, "->"),
  edge((0, 1), "r", $a_1$, "->", label-side: right),
)
