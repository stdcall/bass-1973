#import "commutative.typ": cd, edge
#import "../main-defs.typ": SK, SL

#let first-row-arrow() = math.class("relation", cd(
  cell-size: (17mm, 4mm),
  $&$,
  edge((0, 0), "r", [1-я строка], "->"),
))

#let first-row-factorization() = cd(
  cell-size: (27mm, 18mm),
  $SL_2 (A, frak(q)) & & C \ & W_frak(q) &$,
  edge((0, 0), "rr", $k$, "->"),
  edge((0, 0), "dr", [1-я строка], "->"),
  edge((1, 1), "ur", $[ ]$, "->"),
)

#let universal-first-row-factorization() = cd(
  cell-size: (29mm, 18mm),
  $SL_2 (A, frak(q)) & & SK_1 (A, frak(q)) \ & W_frak(q) &$,
  edge((0, 0), "rr", $k_frak(q)$, "->"),
  edge((0, 0), "dr", [1-я строка], "->"),
  edge((1, 1), "ur", $[ ]_frak(q)$, "->"),
)
