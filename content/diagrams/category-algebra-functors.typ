#import "commutative.typ": cd, edge

#let functor-composition() = cd(
  cell-size: (17mm, 10mm),
  $bold(A) & bold(B) & bold(C) & bold(D)$,
  edge((0, 0), "r", $S$, "->"),
  edge((1, 0), "r", $T_1$, "->", shift: 1.4mm),
  edge((1, 0), "r", $T_2$, "->", shift: -1.4mm, label-side: right),
  edge((2, 0), "r", $U$, "->"),
)

#let equivalence-criterion() = cd(
  cell-size: (23mm, 20mm),
  $bold(B)(B, B') & & bold(A)(S B, S B') \ & bold(B)(T S B, T S B')$,
  edge((0, 0), "rr", $S_(B, B')$, "->"),
  edge(
    (0, 0),
    "dr",
    $bold(B)(beta_B^(-1), beta_(B'))$,
    "->",
    label-side: right,
  ),
  edge((2, 0), "dl", $T_(S B, S B')$, "->", label-side: left),
)

#let commutative-triangle() = cd(
  cell-size: (9mm, 9mm),
  $& A_1 \ A_0 & & A_2$,
  edge((0, 1), "ur", "->"),
  edge((1, 0), "dr", "->"),
  edge((0, 1), "rr", "->"),
)
