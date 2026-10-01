#import "commutative.typ": cd, edge, node
#import "../main-defs.typ": K, Ker

#let category-fiber-square() = cd(
  cell-size: (28mm, 18mm),
  $bold(A) & bold(A)_2 \ bold(A)_1 & bold(A)'$,
  edge((0, 0), "r", $G_2$, "->"),
  edge((0, 0), "d", $G_1$, "->", label-side: right),
  edge((1, 0), "d", $F_2$, "->"),
  edge((0, 1), "r", $F_1$, "->", label-side: right),
)

#let permuted-morphism-square() = cd(
  cell-size: (57mm, 19mm),
  $A_1 perp dots.c perp A_n & B_1 perp dots.c perp B_n \
  A_(s(1)) perp dots.c perp A_(s(n)) & B_(s(1)) perp dots.c perp B_(s(n))$,
  edge((0, 0), "r", $alpha_1 perp dots.c perp alpha_n$, "->"),
  edge((0, 0), "d", $s$, "->", label-side: right),
  edge((1, 0), "d", $s$, "->"),
  edge(
    (0, 1),
    "r",
    $alpha_(s(1)) perp dots.c perp alpha_(s(n))$,
    "->",
    label-side: right,
  ),
)

#let fiber-functor-cospan() = cd(
  cell-size: (27mm, 18mm),
  $& bold(A)_2 \
  bold(A)_1 & bold(A)'$,
  edge((1, 0), "d", $F_2$, "->"),
  edge((0, 1), "r", $F_1$, "->", label-side: right),
)

#let fiber-morphism-square() = cd(
  cell-size: (30mm, 18mm),
  $F_1 A_1 & F_2 A_2 \
  F_1 B_1 & F_2 B_2$,
  edge((0, 0), "r", $alpha$, "->"),
  edge((0, 0), "d", $F_1 f_1$, "->", label-side: right),
  edge((1, 0), "d", $F_2 f_2$, "->"),
  edge((0, 1), "r", $beta$, "->", label-side: right),
)

#let universal-fiber-square() = cd(
  cell-size: (28mm, 18mm),
  $bold(B) & bold(A)_2 \
  bold(A)_1 & bold(A)'$,
  edge((0, 0), "r", $H_2$, "->"),
  edge((0, 0), "d", $H_1$, "->", label-side: right),
  edge((1, 0), "d", $F_2$, "->"),
  edge((0, 1), "r", $F_1$, "->", label-side: right),
)

#let diagonal-fiber-square() = cd(
  cell-size: (28mm, 18mm),
  $italic("co")(F) & bold(A) \
  bold(A) & bold(A)'$,
  edge((0, 0), "r", $G_2$, "->"),
  edge((0, 0), "d", $G_1$, "->", label-side: right),
  edge((1, 0), "d", $F$, "->"),
  edge((0, 1), "r", $F$, "->", label-side: right),
)

#let automorphism-fiber-square() = cd(
  cell-size: (30mm, 18mm),
  $F A & F B \
  F A & F B$,
  edge((0, 0), "r", $gamma$, "->"),
  edge((0, 0), "d", $F alpha$, "->", label-side: right),
  edge((1, 0), "d", $F beta$, "->"),
  edge((0, 1), "r", $gamma$, "->", label-side: right),
)

#let exact-k-quotient-diagram() = cd(
  cell-size: (25mm, 21mm),
  $K_1 (bold(A)) & K_1 (bold(A)) & 0 & K_0 (bold(A)) & K_0 (bold(A)) & 0 \
  K_1 (italic("co")(F)) & K_1 (bold(A)) xor K_1 (bold(A)) & K_1 (bold(A)') &
  K'_0 (italic("co")(F)) & K_0 (bold(A)) xor K_0 (bold(A)) & K_0 (bold(A)') \
  K_1 (F) & K_1 (bold(A)) & K_1 (bold(A)') & K'_0 (F) & K_0 (bold(A)) & K_0
  (bold(A)')$,
  node((-.65, 1.6), $K_1 (bold(A), F)$),
  edge((0, 0), "r", $=$),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $=$),
  edge((4, 0), "r", "->"),
  edge((0, 0), "d", $Delta_1$, "->", label-side: right),
  edge((1, 0), "d", $d_1$, "->"),
  edge((2, 0), "d", "->"),
  edge((3, 0), "d", $Delta_0$, "->", label-side: right),
  edge((4, 0), "d", $d_0$, "->"),
  edge((5, 0), "d", "->"),
  edge((0, 1), "r", $g_1$, "->"),
  edge((1, 1), "r", $f_1$, "->"),
  edge((2, 1), "r", $partial$, "->"),
  edge((3, 1), "r", $g_0$, "->"),
  edge((4, 1), "r", $f_0$, "->"),
  edge((0, 1), "d", "->"),
  edge((1, 1), "d", $s_1$, "->"),
  edge((2, 1), "d", $=$),
  edge((3, 1), "d", "->"),
  edge((4, 1), "d", $s_0$, "->"),
  edge((5, 1), "d", $=$),
  edge((0, 2), "r", "->"),
  edge((1, 2), "r", "->"),
  edge((2, 2), "r", $partial'$, "->"),
  edge((3, 2), "r", "->"),
  edge((4, 2), "r", "->"),
  edge((-.65, 1.6), (0, 1), $H$, "->"),
  edge((-.65, 1.6), (0, 2), $h$, "->", label-side: right),
)

#let natural-exact-functor-square() = cd(
  cell-size: (30mm, 18mm),
  $bold(B) & bold(B)' \
  bold(A) & bold(A)'$,
  edge((0, 0), "r", $G$, "->"),
  edge((0, 0), "d", $J$, "->", label-side: right),
  edge((1, 0), "d", $J'$, "->"),
  edge((0, 1), "r", $F$, "->", label-side: right),
)

#let natural-k-sequence-diagram() = cd(
  cell-size: (22mm, 22mm),
  $K_1 (G) & K_1 (bold(B)) & K_1 (bold(B)') & K'_0 (G) & K_0 (bold(B)) & K_0
  (bold(B)') \
  K_1 (F) & K_1 (bold(A)) & K_1 (bold(A)') & K'_0 (F) & K_0 (bold(A)) & K_0
  (bold(A)')$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", $partial'$, "->"),
  edge((3, 0), "r", "->"),
  edge((4, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", $partial'$, "->"),
  edge((3, 1), "r", "->"),
  edge((4, 1), "r", "->"),
  edge((0, 0), "d", $j'_1$, "->", label-side: right),
  edge((1, 0), "d", $J$, "->"),
  edge((2, 0), "d", $J'$, "->"),
  edge((3, 0), "d", $j_0$, "->"),
  edge((4, 0), "d", $J$, "->"),
  edge((5, 0), "d", $J'$, "->"),
)

#let exact-functor-triangle() = cd(
  cell-size: (23mm, 17mm),
  $& bold(B) \
  bold(A) && bold(C)$,
  edge((0, 1), "ur", $F$, "->"),
  edge((1, 0), "dr", $G$, "->"),
  edge((0, 1), "rr", $H = G F$, "->", label-side: right),
)

#let exact-k-triangle-diagram() = cd(
  cell-size: (19mm, 19mm),
  $K_1 (F) && K_1 (bold(A)) && K_1 (bold(C)) && K'_0 (G) \
  & K_1 (H) && K_1 (bold(B)) && K'_0 (H) && K_0 (bold(B)) \
  && K_1 (G) && K'_0 (F) && K_0 (bold(A)) && K_0 (bold(C))$,
  edge((0, 0), "rr", $d_F$, "->"),
  edge((2, 0), "rr", $H_1$, "->"),
  edge((4, 0), "rr", $delta_G$, "->"),
  edge((0, 0), "dr", $partial$, "->"),
  edge((1, 1), "ur", $d_H$, "->"),
  edge((2, 0), "dr", $F_1$, "->"),
  edge((3, 1), "ur", $G_1$, "->"),
  edge((4, 0), "dr", $delta_H$, "->"),
  edge((5, 1), "ur", $delta$, "->"),
  edge((6, 0), "dr", $d_G$, "->"),
  edge((7, 1), "dr", $G_0$, "->"),
  edge((1, 1), "dr", $delta$, "->"),
  edge((2, 2), "ur", $d_G$, "->"),
  edge((3, 1), "dr", $delta_F$, "->"),
  edge((4, 2), "ur", $partial$, "->"),
  edge((5, 1), "dr", $d_H$, "->"),
  edge((6, 2), "ur", $F_0$, "->"),
  edge((2, 2), "rr", $Delta$, "->"),
  edge((4, 2), "rr", $d_F$, "->"),
  edge((6, 2), "rr", $H_0$, "->"),
)

#let excision-k-sequence-diagram() = cd(
  cell-size: (26mm, 21mm),
  $K_1 (bold(A)) & K_1 (bold(A)_2) & K'_0 (G_2) & K_0 (bold(A)) & K_0
  (bold(A)_2) \
  K_1 (bold(A)_1) & K_1 (bold(A)') & K'_0 (F_1) & K_0 (bold(A)_1) & K_0
  (bold(A)')$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", $partial'$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", $partial'$, "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", $phi$, "->"),
  edge((3, 0), "d", "->"),
  edge((4, 0), "d", "->"),
)

#let excision-surjectivity-triangle() = cd(
  cell-size: (26mm, 18mm),
  $F_1 (A_1 perp A'_1) && F_1 (B_1 perp A'_1) \
  & F_2 A_2$,
  edge((0, 0), "rr", $gamma perp 1_(F_1 A'_1)$, "->"),
  edge((0, 0), "dr", $alpha$, "->", label-side: right),
  edge((2, 0), "dl", $beta$, "->"),
)

#let excision-stabilized-isomorphism() = cd(
  cell-size: (29mm, 24mm),
  $U perp Delta C = (A perp C, 1_(A_2 perp C_2), A(F_1 alpha_1)epsilon perp C) \
  V = (A perp C, epsilon_2, A perp C)$,
  edge(
    (0, 0),
    "d",
    $((1_(A_1 perp C_1), 1_(A_2 perp C_2)),
      ((alpha_1 perp 1_(C_1))epsilon_1, epsilon_2))$,
    "->",
  ),
)

#let excision-topological-diagram() = cd(
  cell-size: (22mm, 22mm),
  $& K_1 (bold(A)_1) && K_0 G_1 = K_0 F_2 && K_0 (bold(A)_2) \
  K_1 (bold(A)) & K_1 (bold(A)_1) xor K_1 (bold(A)_2) & K_1 (bold(A)') && K_0
  (bold(A)) & K_0 (bold(A)_1) xor K_0 (bold(A)_2) & K_0 (bold(A)') \
  & K_1 (bold(A)_2) && K_0 G_2 = K_0 F_1 && K_0 (bold(A)_1)$,
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "rr", "->"),
  edge((4, 1), "r", "->"),
  edge((5, 1), "r", "->"),
  edge((0, 1), "ur", $G_1$, "->"),
  edge((0, 1), "dr", $G_2$, "->", label-side: right),
  edge((1, 0), "rr", "->"),
  edge((3, 0), "rr", "->"),
  edge((1, 2), "rr", "->"),
  edge((3, 2), "rr", "->"),
  edge((1, 0), "dr", $F_1$, "->"),
  edge((1, 2), "ur", $F_2$, "->"),
  edge((2, 1), "ur", "->"),
  edge((2, 1), "dr", "->"),
  edge((3, 0), "dr", "->"),
  edge((3, 2), "ur", "->"),
  edge((4, 1), "ur", $G_2$, "->"),
  edge((4, 1), "dr", $G_1$, "->", label-side: right),
  edge((5, 0), "dr", $F_2$, "->"),
  edge((5, 2), "ur", $F_1$, "->"),
)
