#import "commutative.typ": cd, edge

#let projective-line-ring-square() = cd(
  cell-size: (44mm, 24mm),
  $A & A[T_-] \ A[T_+] & A[T]$,
  edge((0, 0), "r", "hook->"),
  edge((0, 0), "d", "hook->"),
  edge((1, 0), "d", $tau_-$, "hook->"),
  edge((0, 1), "r", $tau_+$, "hook->", label-side: right),
)

#let projective-line-category-cospan() = cd(
  cell-size: (46mm, 23mm),
  $& bold(P)(A[T_-]) \ bold(P)(A[T_+]) & bold(P)(A[T])$,
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let projective-line-category-square() = cd(
  cell-size: (51mm, 26mm),
  $bold(P)(P^1 (A)) & bold(P)(A[T_-]) \ bold(P)(A[T_+]) & bold(P)(A[T])$,
  edge((0, 0), "r", $g_-$, "->"),
  edge((0, 0), "d", $g_+$, "->"),
  edge((1, 0), "d", $tau_-$, "->"),
  edge((0, 1), "r", $tau_+$, "->", label-side: right),
)
