#import "commutative.typ": cd, edge
#import "../main-defs.typ": Cart, Div, Hom, Im, Pic, U, tensor

#let fractional-submodule-isomorphisms() = cd(
  cell-size: (18mm, 10mm),
  $M & A$,
  edge((0, 0), "r", $b'$, "->", shift: -1.6pt, label-side: left),
  edge((1, 0), "l", $b$, "->", shift: -1.6pt, label-side: left),
)

#let divisor-class-square() = cd(
  cell-size: (21mm, 14mm),
  $U(A) & U(L) & D(A) & C(A) & 0 \ U(A) & U(L) & Cart(A) & Pic(A) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", $Div$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((0, 0), "d", "="),
  edge((1, 0), "d", "="),
  edge((2, 1), "u", "->"),
  edge((3, 1), "u", "->"),
)

#let localized-divisor-class-square() = cd(
  cell-size: (21mm, 14mm),
  $U(A) & U(S^(-1)A) & D(A,S) & C(A) & C(S^(-1)A) & 0 \ U(A) & U(S^(-1)A) &
  Pic(A, S) & Pic(A) & Pic(S^(-1)A) &$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", $Div$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((4, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((0, 1), "u", "->"),
  edge((1, 1), "u", "->"),
  edge((2, 1), "u", "->"),
  edge((3, 1), "u", "->"),
  edge((4, 1), "u", "->"),
)

#let localization-tensor-square() = cd(
  cell-size: (58mm, 19mm),
  $M tensor_R N & S^(-1)(M tensor_R N) \ S^(-1)M tensor_R S^(-1)N & S^(-1)M
  tensor_(S^(-1)R) S^(-1)N$,
  edge((0, 0), "r", $h_(M tensor_R N)$, "->"),
  edge((0, 0), "d", $h_M tensor_R h_N$, "->"),
  edge((1, 0), "d", $g_M$, "->"),
  edge((0, 1), "r", $f$, "->"),
)

#let localization-hom-square() = cd(
  cell-size: (61mm, 19mm),
  $Hom_A (M,N) & S^(-1)Hom_A (M,N) \ Hom_A (S^(-1)M,S^(-1)N) &
  Hom_(S^(-1)A)(S^(-1)M,S^(-1)N)$,
  edge((0, 0), "r", $h_(Hom_A (M,N))$, "->"),
  edge((0, 0), "dr", $S^(-1)$, "->"),
  edge((1, 0), "d", $g_M$, "->"),
  edge((1, 1), "l", $f$, "->"),
)

#let localization-submodule-square() = cd(
  cell-size: (22mm, 15mm),
  $N & H_0 \ S^(-1)N & S^(-1)H_0$,
  edge((0, 0), "r", $i$, "->"),
  edge((0, 0), "d", $h_N$, "->"),
  edge((1, 0), "d", $h_(H_0)(approx.eq)$, "->"),
  edge((0, 1), "r", $S^(-1)i$, "->"),
)

#let localization-pullback-square() = cd(
  cell-size: (24mm, 15mm),
  $M_0 & M \ N & Im(h_M)$,
  edge((0, 0), "r", $d_0$, "->"),
  edge((0, 0), "d", $f$, "->"),
  edge((1, 0), "d", $h_M$, "->"),
  edge((0, 1), "r", $d'$, "->"),
)

#let projective-reduction-square() = cd(
  cell-size: (13mm, 13mm),
  $P & Q \ overline(P) & overline(Q)$,
  edge((0, 0), "r", $f$, "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", $overline(f)$, "->"),
)

#let chain-module-quotients() = cd(
  cell-size: (22mm, 11mm),
  $0 & X slash (X inter Y) & M slash Y & M slash (X + Y) & 0 \ 0 & X slash
  (X inter Y') & M slash Y' & M slash (X + Y') & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", "->"),
  edge((3, 0), "d", "->"),
)
