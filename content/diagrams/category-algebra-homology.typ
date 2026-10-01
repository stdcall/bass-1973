#import "commutative.typ": cd, edge
#import "../main-defs.typ": MC

#let homology-snake() = cd(
  cell-size: (26mm, 17mm),
  $& C' slash B(C') & C slash B(C) & C'' slash B(C'') & 0 \ 0 & Z(C') & Z(C) &
  Z(C'') &$,
  ..range(1, 4).map(i => edge((i, 0), "r", "->")),
  ..range(3).map(i => edge((i, 1), "r", "->")),
  ..range(1, 4).map(i => edge((i, 0), "d", "->")),
)

#let nine-lemma() = cd(
  cell-size: (21mm, 14mm),
  $& 0 & 0 & 0 & \ 0 & C'_2 & C_2 & C''_2 & 0 \ 0 & C'_1 & C_1 & C''_1 & 0 \ 0
  & C'_0 & C_0 & C''_0 & 0 \ & 0 & 0 & 0 &$,
  ..range(1, 4).map(j => range(4).map(i => edge((i, j), "r", "->"))).flatten(),
  ..range(1, 4).map(i => range(4).map(j => edge((i, j), "d", "->"))).flatten(),
)

#let cone-boundary() = cd(
  cell-size: (28mm, 17mm),
  $0 & C_n & MC(a)_n & C'_(n - 1) & 0 \ 0 & C_(n - 1) & MC(a)_(n - 1) & C'_(n
  - 2) & 0$,
  ..range(4).map(i => edge((i, 0), "r", "->")),
  ..range(4).map(i => edge((i, 1), "r", "->")),
  edge((1, 0), "d", $d$, "->"),
  edge((2, 0), "d", $d(a)$, "->"),
  edge((3, 0), "d", $-d'$, "->"),
)
