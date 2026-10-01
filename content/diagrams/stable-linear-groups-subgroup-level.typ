#import "../main-defs.typ": E, GL
#import "commutative.typ": cd, edge

#let diagram-subgroup-level() = [
  $
    #cd(
      cell-size: (40mm, 13mm),
      $& GL_m (A) & GL'_m (A, frak(q)) \ E_m (A) & & \ & E_m (A, frak(q)) & GL_m (A, frak(q))$,
      edge((0, 1), "ur", "-"),
      edge((2, 0), "l", "-"),
      edge((2, 0), "dd", "-"),
      edge((0, 1), "dr", "-"),
      edge((1, 2), "r", "-"),
    )
  $
]
