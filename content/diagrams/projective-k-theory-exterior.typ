#import "commutative.typ": cd, edge
#import "../main-defs.typ": K, U

#let exterior-operation-naturality() = cd(
  cell-size: (46mm, 22mm),
  $K_0 (A) & K_0 (B) \ U_1 (K_0 (A)[[t]]) & U_1 (K_0 (B)[[t]])$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", $L_A$, "->"),
  edge((1, 0), "d", $L_B$, "->", label-side: right),
  edge((0, 1), "r", "->"),
)

#let exterior-koszul-complex() = cd(
  cell-size: (26mm, 17mm),
  $dots & Lambda^n (P) & Lambda^(n-1) (P) & dots & Lambda^1 (P) & Lambda^0 (P) & 0 dots \ & & & & P & A$,
  ..range(6).map(i => edge((i, 0), "r", "->")),
  edge((4, 0), "d", "="),
  edge((5, 0), "d", "="),
  edge((4, 1), "r", $d$, "->"),
)
