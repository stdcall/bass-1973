#import "commutative.typ": cd, edge

#let characteristic-sequence() = cd(
  cell-size: (29mm, 12mm),
  $0 & M[t] & M[t] & M_f & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", $t dot 1_(M[t]) - f[t]$, "->"),
  edge((2, 0), "r", $phi_f$, "->"),
  edge((3, 0), "r", "->"),
)
