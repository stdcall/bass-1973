#import "commutative.typ": cd, edge

#let bundle-pullback() = cd(
  cell-size: (27mm, 17mm),
  $g^* E & E \
  X' & X$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", $g^* p$, "->"),
  edge((1, 0), "d", $p$, "->", label-side: right),
  edge((0, 1), "r", $g$, "->", label-side: right),
)
