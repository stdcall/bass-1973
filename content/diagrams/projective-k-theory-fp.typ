#import "commutative.typ": cd, edge
#import "../main-defs.typ": Rk, tensor

#let fp-exponential-isomorphism() = cd(
  cell-size: (48mm, 18mm),
  $QQ tensor Rk_0 (A) & 1 + (QQ tensor Rk_0 (A))$,
  edge((0, 0), "r", $exp$, "->", shift: 1.4mm),
  edge((1, 0), "l", $log$, "->", shift: 1.4mm, label-side: left),
)

#let fp-transition-square() = cd(
  cell-size: (35mm, 22mm),
  $W_n & W_n \ W_(n m) & W_(n m)$,
  edge((0, 0), "r", $n 1$, "->"),
  edge((0, 0), "d", $f_(n, n m)$, "->"),
  edge((1, 0), "d", $f'_(n, n m) = m f_(n, n m)$, "->", label-side: right),
  edge((0, 1), "r", $n m 1$, "->"),
)
