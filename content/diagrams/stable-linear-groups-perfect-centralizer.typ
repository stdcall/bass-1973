#import "commutative.typ": cd, edge

#let diagram-perfect-centralizer() = [
  $
    #cd(
      cell-size: (22mm, 12mm),
      $& G & C_1 \ E & & \ & {1} & C$,
      edge((0, 1), "ur", "-"),
      edge((1, 0), "r", "-"),
      edge((2, 0), "dd", "-"),
      edge((0, 1), "dr", "-"),
      edge((1, 2), "r", "-"),
    )
  $
]
