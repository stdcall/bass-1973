#import "../main-defs.typ": G, H, K, Ker, SK, id, maxSpec
#import "commutative.typ": cd, edge, node

#let conductor-projection-triangle() = cd(
  cell-size: (38mm, 18mm),
  $& A'=R [pi slash pi_i] & \
  A=R pi & & A_i,$,
  edge((0, 1), (1, 0), $f$, "->"),
  edge((1, 0), (2, 1), $rho'_i$, "->"),
  edge((0, 1), (2, 1), $rho_i$, "->"),
)

#let abelian-group-g-one-triangle() = cd(
  cell-size: (35mm, 18mm),
  $G_1 (B) & & G_1 (A) \
  & G_1 (L pi) &$,
  edge((0, 0), (2, 0), $f$, "->"),
  edge((0, 0), (1, 1), $g_1$, "->"),
  edge((2, 0), (1, 1), "->"),
)

#let finite-group-k-one-cartan() = cd(
  cell-size: (29mm, 18mm),
  $0 & SK_1 (ZZ pi) & K_1 (ZZ pi) & K_1 (QQ pi) \
  & & G_1 (ZZ pi) & G_1 (QQ pi)$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", $k_1$, "->"),
  edge((2, 0), "d", $c_1 (ZZ pi)$, "->", label-side: left),
  edge((3, 0), "d", $c_1 (QQ pi)$, "->", label-side: right),
  edge((2, 1), "r", $g_1$, "->"),
)

#let rank-localization-square() = cd(
  cell-size: (35mm, 14mm),
  $K_0 (R pi) & K_0 (L pi) \ H_0 (R pi) & H_0 (L pi)$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let trivial-frobenius-module() = cd(
  cell-size: (30mm, 15mm),
  $T (pi') & T (pi).$,
  edge((0, 0), "r", $[pi:pi']$, "->", shift: 1.4mm),
  edge((1, 0), "l", $id$, "->", shift: 1.4mm, label-side: left),
)

#let group-cartan-localization() = cd(
  cell-size: (32mm, 21mm),
  $K_1 (R pi) & K_1 (L pi) & K_0 (R pi,S) & K_0 (R pi) & K_0 (L pi) & \
  & G_1 (L pi) & G_0 (R pi,S) & G_0 (R pi) & G_0 (L pi) & 0 \
  & & & & &$,
  edge((0, 0), "r", $k_1 (R pi)$, "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $k_0 (R pi)$, "->"),
  edge((1, 0), "d", $c_1 (L pi)$, "=>", label-side: right),
  edge((2, 0), "d", $c_0 (R pi,S)$, "->"),
  edge((3, 0), "d", $c_0 (R pi)$, "->"),
  edge((4, 0), "d", $c_0 (L pi)$, "=>"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", $g_0 (R pi)$, "->"),
  edge((4, 1), "r", "->"),
  edge((2, 1), "d", "="),
  node(
    (2, 2),
    $(union.sq.big_(frak(p) in maxSpec (R)) G_0 ((R slash frak(p)) pi))$,
  ),
)

#let group-cartan-primary-splitting() = cd(
  cell-size: (36mm, 19mm),
  $0 & K_0 (R pi,T) & K_0 (R pi,S) & K_0 (T^(-1) R pi,S) & 0 \
  0 & G_0 (R pi,T) & G_0 (R pi,S) & G_0 (T^(-1) R pi,S) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", "->"),
  edge((1, 0), "d", $c_0 (R pi,T)$, "->"),
  edge((2, 0), "d", $c_0 (R pi,S)$, "->"),
  edge((3, 0), "d", $c_0 (T^(-1) R pi,S)$, "->"),
)

#let group-cartan-semilocal-surjection() = cd(
  cell-size: (45mm, 19mm),
  $K_1 (L pi) & K_0 (T^(-1) R pi,S) & 0 \ G_1 (L pi) & G_0 (T^(-1) R pi,S) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", $c_1 (L pi)$, "=>", label-side: right),
  edge((1, 0), "d", $c_0 (T^(-1) R pi,S)$, "->"),
)

#let group-cartan-kernel-comparison() = cd(
  cell-size: (38mm, 18mm),
  $
      &                  &                  & 0                &   \
    0 & Ker (c_0 (R pi)) & Ker (k_0 (R pi)) & Ker (g_0 (R pi)) & 0 \
      & 0                &    Ker (k_0 (B)) & Ker (g_0 (B))    & 0 \
      &                  &                0 &                  &
  $,
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", $c_0 (R pi)$, "->"),
  edge((3, 1), "r", "->"),
  edge((1, 2), "r", "->"),
  edge((2, 2), "r", $c_0 (B)$, "->", label-side: right),
  edge((3, 2), "r", "->"),
  edge((2, 1), "d", "->"),
  edge((2, 2), "d", "->"),
  edge((3, 2), "u", "->"),
  edge((3, 1), "u", "->"),
)

#let conductor-square() = cd(
  cell-size: (27mm, 14mm),
  $A & B \ A slash frak(c) & B slash frak(c)$,
  edge((0, 0), "r", "hook->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "hook->"),
)

#let milnor-cyclotomic-square() = cd(
  cell-size: (30mm, 18mm),
  $A_(n+1) & A_n \ R_(n+1) & FF pi_n$,
  edge((0, 0), "r", $f$, "->"),
  edge((0, 0), "d", $g$, "->", label-side: right),
  edge((1, 0), "d", $g'$, "->"),
  edge((0, 1), "r", $f'$, "->", label-side: right),
)
