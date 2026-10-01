#import "commutative.typ": cd, edge
#import "../main-defs.typ": G, K

#let g-zero-nilpotent-square() = cd(
  cell-size: (43mm, 21mm),
  $G_0 (A) & G_0 (A[t]) \ G_0 (A/N) & G_0 ((A/N)[t])$,
  edge((0, 0), "r", $i$, "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", $i_N$, "->", label-side: right),
)

#let g-zero-localization-comparison() = cd(
  cell-size: (45mm, 22mm),
  $K_0 (bold(M)_S (A)) & G_0 (A) & G_0 (S^(-1) A) & 0 \ K_0 (bold(M)_S (A[t])) & G_0 (A[t]) & G_0 (S^(-1) A[t]) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((0, 0), "d", $i'$, "->"),
  edge((1, 0), "d", $i$, "->"),
  edge((2, 0), "d", $i''$, "->"),
)
