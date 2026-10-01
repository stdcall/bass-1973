#import "commutative.typ": cd, edge

#let cofinal-limit() = cd(
  cell-size: (29mm, 17mm),
  $(G F)_(arrow.r) & G_(arrow.r) \ G F A$,
  edge((0, 0), "r", $alpha$, "->"),
  edge((0, 1), "u", $gamma_A$, "->", label-side: left),
  edge((0, 1), "ur", $gamma'_(F A)$, "->", label-side: right),
)

#let translations-pair() = cd(
  cell-size: (27mm, 15mm),
  $a_1 & a_1 + a_2 & a_2$,
  edge((0, 0), "r", $a_2$, "->"),
  edge((2, 0), "l", $a_1$, "->"),
)

#let translations-equalizer() = cd(
  cell-size: (24mm, 15mm),
  $a & b & a$,
  edge((0, 0), "r", $c_1$, "->"),
  edge((2, 0), "l", $c_2$, "->"),
)

#let cofinal-translation() = cd(
  cell-size: (31mm, 18mm),
  $f(a) & a' \ & f(c)$,
  edge((0, 0), "r", $b'$, "->"),
  edge((1, 0), "d", $c'$, "->", label-side: right),
  edge((0, 0), "dr", $f(d)$, "->", label-side: right),
)

#let sequential-translation() = cd(
  cell-size: (29mm, 18mm),
  $s_n & a \ & s_m$,
  edge((0, 0), "r", $b$, "->"),
  edge((1, 0), "d", $c$, "->", label-side: right),
  edge((0, 0), "dr", $a_(n, m)$, "->", label-side: right),
)
