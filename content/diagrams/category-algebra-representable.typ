#import "commutative.typ": cd, edge
#import "../main-defs.typ": Coim, Coker, Im, Ker, coker, ker

#let yoneda-naturality() = cd(
  cell-size: (34mm, 17mm),
  $overline(A)(A) & F(A) \ overline(A)(B) & F(B)$,
  edge((0, 0), "r", $alpha_A$, "->"),
  edge((0, 0), "d", $overline(A)(h)$, "->", label-side: right),
  edge((1, 0), "d", $F(h)$, "->"),
  edge((0, 1), "r", $alpha_B$, "->", label-side: right),
)

#let pullback-square(
  object: $A_1 product_(A') A_2$,
  upper: $p_2$,
  left: $p_1$,
) = cd(
  cell-size: (36mm, 17mm),
  $#object & A_2 \ A_1 & A'$,
  edge((0, 0), "r", upper, "->"),
  edge((0, 0), "d", left, "->", label-side: right),
  edge((1, 0), "d", $f_2$, "->"),
  edge((0, 1), "r", $f_1$, "->", label-side: right),
)

#let pushout-square() = cd(
  cell-size: (36mm, 17mm),
  $A_1 product.co_(A') A_2 & A_2 \ A_1 & A'$,
  edge((1, 0), "l", "->"),
  edge((0, 1), "u", "->"),
  edge((1, 1), "u", "->"),
  edge((1, 1), "l", "->"),
)

#let kernel-cokernel() = cd(
  cell-size: (28mm, 14mm),
  $Ker(a) & A & B & Coker(a)$,
  edge((0, 0), "r", $ker(a)$, "->"),
  edge((1, 0), "r", $a$, "->"),
  edge((2, 0), "r", $coker(a)$, "->"),
)

#let image-coimage() = cd(
  cell-size: (33mm, 15mm),
  $Ker(a) & Coker(a) \ A & B \ Coim(a) & Im(a)$,
  edge((0, 0), "d", "->"),
  edge((1, 1), "u", "->"),
  edge((0, 1), "r", $a$, "->"),
  edge((0, 1), "d", "->"),
  edge((1, 2), "u", "->"),
  edge((0, 2), "r", $i$, "->"),
)
