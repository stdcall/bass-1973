#import "commutative.typ": cd, edge, node
#import "../main-defs.typ": MC

#let resolution-lift-start() = cd(
  cell-size: (30mm, 16mm),
  $C'_0 & & A' \ & B & \ C_0 & & A$,
  edge((0, 0), (2, 0), $epsilon'$, "->"),
  edge((0, 0), (0, 2), $F_0$, "->", label-side: right),
  edge((2, 0), (2, 2), $f$, "->"),
  edge((0, 2), (2, 2), $epsilon$, "->", label-side: right),
  edge((0, 0), (1, 1), "->"),
  edge((1, 1), (0, 2), "->"),
  edge((1, 1), (2, 0), "->"),
)

#let resolution-lift-induction() = cd(
  cell-size: (24mm, 17mm),
  $& C'_(n - 1) & dots & C'_0 & A' & 0 \ dots & C_(n - 1) & dots & C_0 & A & 0$,
  edge((1, 0), "r", $d'_(n - 1)$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $epsilon'$, "->"),
  edge((4, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", $d_(n - 1)$, "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", $epsilon$, "->"),
  edge((4, 1), "r", "->"),
  edge((1, 0), "d", $F_(n - 1)$, "->"),
  edge((3, 0), "d", $F_0$, "->"),
  edge((4, 0), "d", "->"),
)

#let resolution-lift-step() = cd(
  cell-size: (31mm, 17mm),
  $C'_n & Z'_(n - 1) & 0 \ C_n & Z_(n - 1) & 0$,
  edge((0, 0), "r", $d'$, "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", $d$, "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", $F_n$, "->", label-side: right),
  edge((1, 0), "d", $F'$, "->"),
)

#let resolution-square() = cd(
  cell-size: (31mm, 17mm),
  $C' & C \ A' & A$,
  edge((0, 0), "r", $F$, "->"),
  edge((0, 0), "d", $epsilon'$, "->", label-side: right),
  edge((1, 0), "d", $epsilon$, "->"),
  edge((0, 1), "r", $f$, "->", label-side: right),
)

#let cone-resolution-homology() = cd(
  cell-size: (22mm, 15mm),
  $dots 0 & H_1(MC(F)) & H_0(C') & H_0(C) & H_0(MC(F)) & 0 \ & & A' & A & &$,
  ..range(5).map(i => edge((i, 0), "r", "->")),
  edge((2, 0), "d", "="),
  edge((3, 0), "d", "="),
  edge((2, 1), "r", $f$, "->"),
)

#let schanuel-pullback() = cd(
  cell-size: (23mm, 14mm),
  $& & 0 & 0 & \ & & P'_1 & P'_1 & \ 0 & P_1 & Q & P'_0 & 0 \ 0 & P_1 & P_0 &
  A & 0$,
  edge((2, 0), "d", "->"),
  edge((3, 0), "d", "->"),
  edge((2, 1), "r", "="),
  edge((2, 1), "d", "->"),
  edge((3, 1), "d", "->"),
  ..range(4).map(i => edge((i, 2), "r", "->")),
  edge((1, 2), "d", "="),
  edge((2, 2), "d", "->"),
  edge((3, 2), "d", "->"),
  ..range(4).map(i => edge((i, 3), "r", "->")),
)

#let projective-lift(
  objects: $P'_0 & A' \ P_0 & A$,
  top: $epsilon'$,
  bottom: $epsilon$,
  left-label: $F_0$,
  right-label: $f$,
) = cd(
  cell-size: (32mm, 17mm),
  objects,
  edge((0, 0), "r", top, "->"),
  edge((0, 1), "r", bottom, "->"),
  edge((0, 0), "d", left-label, "->", label-side: right),
  edge((1, 0), "d", right-label, "->"),
)

#let homotopy-lift(initial: false) = cd(
  cell-size: (29mm, 17mm),
  if initial { $& P'_0 & A' \ P_1 & P_0 & A$ } else {
    $& P'_n & P'_(n - 1) \ P_(n + 1) & P_n & P_(n - 1)$
  },
  edge((1, 0), "r", if not initial { $d'_n$ }, "->"),
  edge((0, 1), "r", if not initial { $d_(n + 1)$ }, "->"),
  edge((1, 1), "r", if not initial { $d_n$ }, "->"),
  edge((1, 0), "d", if initial { $F_0$ } else { $F_n$ }, "->"),
  edge((2, 0), "d", if initial { $0$ } else { $F_(n - 1)$ }, "->"),
  edge((1, 0), (0, 1), if initial { $s_0$ } else { $s_n$ }, "-->"),
  ..if initial { () } else { (edge((2, 0), (1, 1), $s_(n - 1)$, "->"),) },
)

#let horseshoe-start() = cd(
  cell-size: (27mm, 17mm),
  $0 & P'_0 & P'_0 xor P''_0 & P''_0 & 0 \ 0 & A' & A & A'' & 0$,
  ..range(4).map(i => edge((i, 0), "r", "->")),
  ..range(4).map(i => edge(
    (i, 1),
    "r",
    if i == 1 { $a$ } else if i == 2 { $b$ },
    "->",
  )),
  edge((1, 0), "d", $epsilon'$, "->"),
  edge((2, 0), "d", $epsilon$, "->"),
  edge((3, 0), "d", $epsilon''$, "->"),
)
