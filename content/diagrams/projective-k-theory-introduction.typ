#import "commutative.typ": cd, edge
#import "../main-defs.typ": HCat, K, res

#let projective-ring-square() = cd(
  cell-size: (25mm, 17mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", $f_2$, "->"),
  edge((0, 1), "r", $f_1$, "->"),
)

#let projective-category-square() = cd(
  cell-size: (31mm, 19mm),
  $bold(P)(A) & bold(P)(A_2) \ bold(P)(A_1) & bold(P)(A')$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let projective-quotient-triangle() = cd(
  cell-size: (21mm, 17mm),
  $& bold(P)(A slash frak(q)) & \ bold(P)(A) & & bold(P)(A slash frak(q)')$,
  edge((0, 1), "ur", "->"),
  edge((1, 0), "dr", "->"),
  edge((0, 1), "rr", "->"),
)

#let projective-restriction-square() = cd(
  cell-size: (34mm, 18mm),
  $K_i (B) & K_i (A) \ K_i (HCat(B)) & K_i (HCat(A))$,
  edge((0, 0), "r", $res$, "->"),
  edge((0, 0), "d", $tilde$, "->"),
  edge((1, 0), "d", $tilde$, "->"),
  edge((0, 1), "r", $res$, "->", label-side: right),
)
