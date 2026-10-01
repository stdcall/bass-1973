#import "../main-defs.typ": GL
#import "commutative.typ": cd, edge

#let diagram-opposite-character() = [
  $
    #cd(
      cell-size: (22mm, 17mm),
      $GL_n (A, frak(q)) & & GL_n (A^o, frak(q)) \ C & "\"=\"" & C^o$,
      edge((0, 0), "rr", $T$, "->"),
      edge((0, 0), "d", $chi$, "->", label-side: right),
      edge((2, 0), "d", $chi^o$, "->", label-side: left),
    )
  $
]
