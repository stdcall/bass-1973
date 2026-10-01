#import "commutative.typ": cd, edge

#let adjoint-pair() = cd(
  cell-size: (31mm, 14mm),
  $bold(A) & bold(B)$,
  edge((0, 0), "r", $T$, "->", shift: 1.4mm),
  edge((1, 0), "l", $S$, "->", shift: 1.4mm),
)

#let adjunction-naturality() = cd(
  cell-size: (50mm, 20mm),
  $bold(A)(A, S B) & bold(B)(T A, B) \ bold(A)(A', S B') & bold(B)(T A', B')$,
  edge((0, 0), "r", $gamma_(A, B)$, "->"),
  edge((0, 1), "r", $gamma_(A', B')$, "->", label-side: right),
  edge((0, 0), "d", $bold(A)(a, S b)$, "->", label-side: right),
  edge((1, 0), "d", $bold(B)(T a, b)$, "->"),
)
