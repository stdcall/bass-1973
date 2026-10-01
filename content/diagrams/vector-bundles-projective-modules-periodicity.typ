#import "commutative.typ": cd, edge
#import "../main-defs.typ": K

#let algebraic-topological-periodicity() = cd(
  cell-size: (42mm, 19mm),
  $K_1 (A[t,t^(-1)]) & K_1 (A) \
  K_1 (B) & K_1 (A) \
  K_1 (X times S^1) & K_1 (X)$,
  edge((0, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((0, 2), "r", "->"),
  edge((0, 0), "d", $j$, "->"),
  edge((1, 0), "d", $=$, "->", label-side: right),
  edge((0, 1), "d", "->"),
  edge((1, 1), "d", "->"),
)
