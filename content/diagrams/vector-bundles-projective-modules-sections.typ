#import "commutative.typ": cd, edge

#let section-map-lift() = cd(
  cell-size: (46mm, 21mm),
  $Gamma(E) & Gamma(E') \
  Gamma(E) slash (frak(m)_x Gamma(E)) &
  Gamma(E') slash (frak(m)_x Gamma(E')) \
  E_x & E'_x$,
  edge((0, 0), "r", $overline(f)$, "->"),
  edge((0, 1), "r", "->"),
  edge((0, 2), "r", $overline(f)_x$, "->", label-side: right),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "d", $approx$, "->"),
  edge((1, 1), "d", $approx$, "->", label-side: right),
)
