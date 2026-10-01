#import "commutative.typ": cd, edge
#import "../main-defs.typ": K, tensor

#let graded-projective-lift() = cd(
  cell-size: (31mm, 22mm),
  $T(P) tensor_(A_0) A & & P \ & P tensor_(A_0) A$,
  edge((0, 0), "rr", $h$, "->"),
  edge((0, 0), "dr", $g tensor_(A_0) A$, "->"),
  edge((1, 1), "ur", "->"),
)

#let nilpotent-polynomial-square() = cd(
  cell-size: (38mm, 20mm),
  $K_0 (B) & K_0 (B[T]) \ K_0 (A) & K_0 (A[T])$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)
