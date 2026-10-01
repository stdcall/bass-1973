#import "commutative.typ": cd, edge

#let mayer-vietoris-square() = cd(
  cell-size: (42mm, 24mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", $c_2$, "->"),
  edge((0, 0), "d", $c_1$, "->"),
  edge((1, 0), "d", $c'_2$, "->"),
  edge((0, 1), "r", $c'_1$, "->", label-side: right),
)

#let mayer-vietoris-unlabelled-square() = cd(
  cell-size: (42mm, 24mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)
