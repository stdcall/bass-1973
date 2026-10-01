#import "../main-defs.typ": GL
#import "commutative.typ": cd, edge

#let diagram-opposite-ring() = [
  $
    #cd(
      cell-size: (39mm, 12mm),
      $GL_m (A, frak(q)) & GL_m (A^o, frak(q))$,
      edge((0, 0), "r", $T$, "->", shift: 0.5mm),
      edge((1, 0), "l", "->", shift: 0.5mm),
    )
  $
]
