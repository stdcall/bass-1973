#import "commutative.typ": cd, edge
#import "../main-defs.typ": alg, aug, moduleCategory

#let map-arrow(label) = math.class("relation", cd(
  cell-size: (14mm, 4mm),
  $&$,
  edge((0, 0), "r", label, "->"),
))

#let augmentation-ideal-functor() = cd(
  cell-size: (65mm, 12mm),
  $aug R hyph alg & R hyph moduleCategory$,
  edge((0, 0), "r", [переход], "->"),
  edge((0, 0), "r", [к пополняющему идеалу], label-side: right, stroke: none),
)

#let augmentation-monoid-functor() = cd(
  cell-size: (58mm, 12mm),
  $aug R hyph alg & italic("полугруппы")$,
  edge((0, 0), "r", $A arrow.r.bar (1 + overline(A))$, "->"),
)
