#import "commutative.typ": cd, edge
#import "../main-defs.typ": Hom, Pic, moduleCategory, tensor

#let map-arrow(label) = math.class("relation", cd(
  cell-size: (14mm, 4mm),
  $&$,
  edge((0, 0), "r", label, "->"),
))

#let left-exact-comparison() = cd(
  cell-size: (18mm, 12mm),
  $0 & T Z & T Y & T X \ 0 & S Z & S Y & S X$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((1, 0), "d", $alpha_Z$, "->"),
  edge((2, 0), "d", $alpha_Y$, "->"),
  edge((3, 0), "d", $alpha_X$, "->"),
)

#let homothety-square() = cd(
  cell-size: (22mm, 14mm),
  $A & A \ M & M$,
  edge((0, 0), "r", $t_A$, "->"),
  edge((0, 0), "d", $f$, "->", label-side: right),
  edge((1, 0), "d", $f$, "->"),
  edge((0, 1), "r", $t_M$, "->", label-side: right),
)

#let tensor-natural-square() = cd(
  cell-size: (32mm, 14mm),
  $M & N \ A tensor_A M & A tensor_A N$,
  edge((0, 0), "r", $f$, "->"),
  edge((0, 0), "d", $tilde.eq$, "->", label-side: right),
  edge((1, 0), "d", $tilde.eq$, "->"),
  edge((0, 1), "r", $t_A$, "->", label-side: right),
)

#let module-equivalence() = cd(
  cell-size: (38mm, 9mm),
  $moduleCategory hyph A & moduleCategory hyph B$,
  edge((0, 0), "r", $T$, "->", shift: 1.2mm),
  edge((1, 0), "l", $S$, "->", shift: 1.2mm, label-side: left),
)

#let morita-square-p() = cd(
  cell-size: (46mm, 17mm),
  $P tensor_B Q tensor_A P & A tensor_A P \ P tensor_B B & P$,
  edge((0, 0), "r", $f tensor 1_P$, "->"),
  edge((0, 0), "d", $1_P tensor g$, "->", label-side: right),
  edge((1, 0), "d", $alpha$, "->"),
  edge((0, 1), "r", $beta$, "->", label-side: right),
)

#let morita-square-q() = cd(
  cell-size: (46mm, 17mm),
  $Q tensor_A P tensor_B Q & B tensor_B Q \ Q tensor_A A & Q$,
  edge((0, 0), "r", $g tensor 1_Q$, "->"),
  edge((0, 0), "d", $1_Q tensor f$, "->", label-side: right),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let split-projective() = cd(
  cell-size: (22mm, 9mm),
  $P & B^((I))$,
  edge((0, 0), "r", $e$, "->", shift: 1.2mm),
  edge((1, 0), "l", $h$, "->", shift: 1.2mm, label-side: left),
)

#let generated-equivalence() = cd(
  cell-size: (46mm, 10mm),
  $moduleCategory hyph A & moduleCategory hyph B$,
  edge((0, 0), "r", $tensor_A P$, "->", shift: 1.2mm),
  edge((1, 0), "l", $Hom_B (P, dot)$, "->", shift: 1.2mm, label-side: left),
)

#let projective-dual-basis() = cd(
  cell-size: (25mm, 9mm),
  $P & B^((I)) & P$,
  edge((0, 0), "r", $e = (q_i)$, "->"),
  edge((1, 0), "r", $h = (p_i)$, "->"),
)

#let picard-equivalence() = cd(
  cell-size: (43mm, 9mm),
  $Pic_R (A) & Pic_R (moduleCategory hyph A)$,
  edge((0, 0), "r", $alpha$, "->", shift: 1.2mm),
  edge((1, 0), "l", $beta$, "->", shift: 1.2mm, label-side: left),
)
