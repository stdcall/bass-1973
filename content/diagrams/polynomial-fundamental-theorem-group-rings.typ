#import "commutative.typ": cd, edge
#import "../main-defs.typ": K, U, det

#let quasiregular-k-zero-square() = cd(
  cell-size: (44mm, 23mm),
  $K_0 (A) & K_0 (A[T_+]) & K_0 (A[T]) \ K_0 (B) & K_0 (B[T_+]) & K_0 (B[T])$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", "->"),
)

#let quasiregular-relative-determinant() = cd(
  cell-size: (0pt, 27mm),
  spacing: (6mm, 0pt),
  $0 & K_1 (A[T_+],J A[T_+]) & K_1 (A[T_+]) & K_1 (B[T_+]) & 0 \ 0 & U(A[T_+],J A[T_+]) & U(A[T_+]) & U(B[T_+]) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((1, 0), "d", $det$, "->"),
  edge((2, 0), "d", $det$, "->"),
  edge((3, 0), "d", $det$, "->"),
)

#let quasiregular-pullback-square() = cd(
  cell-size: (42mm, 24mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", $f_2$, "->"),
  edge((0, 1), "r", $f_1$, "->", label-side: right),
)

#let conductor-k-augmentation-square() = cd(
  cell-size: (53mm, 27mm),
  $K_1 (B'[G]) & K_0 (A[G]) & K_0 (A'[G]) plus.o K_0 (B[G]) \ K_1 (B') & K_0 (A) & K_0 (A') plus.o K_0 (B)$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", "->"),
)
