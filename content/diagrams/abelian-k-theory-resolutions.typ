#import "commutative.typ": cd, edge

#let resolution-fiber() = cd(
  cell-size: (25mm, 16mm),
  $C'_0 & & A' \ & B & \ C_0 & & A$,
  edge((0, 0), (2, 0), $epsilon'$, "->"),
  edge((0, 0), (1, 1), "->"),
  edge((0, 0), (0, 2), $F_0$, "->"),
  edge((2, 0), (2, 2), $f$, "->"),
  edge((1, 1), (0, 2), "->"),
  edge((1, 1), (2, 0), "->"),
  edge((0, 2), (2, 2), $epsilon$, "->"),
)

#let resolution-induction() = cd(
  cell-size: (22mm, 19mm),
  $& C'_(n-1) & dots & C'_0 & A' & 0 \
  C_n & C_(n-1) & dots & C_0 & A & 0$,
  edge((1, 0), "r", $d'_(n-1)$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $epsilon'$, "->"),
  edge((4, 0), "r", "->"),
  edge((0, 1), "r", $d_n$, "->"),
  edge((1, 1), "r", $d_(n-1)$, "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", $epsilon$, "->"),
  edge((4, 1), "r", "->"),
  edge((1, 0), "d", $F_(n-1)$, "->"),
  edge((3, 0), "d", $F_0$, "->"),
  edge((4, 0), "d", $f$, "->"),
)

#let resolution-kernel-step() = cd(
  cell-size: (33mm, 20mm),
  $C'_n & Z'_(n-1) & 0 \ C_n & Z_(n-1) & 0$,
  edge((0, 0), "r", $"«"d'_n"»"$, "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", $"«"d_n"»"$, "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", $F_n$, "->"),
  edge((1, 0), "d", $"«"F_(n-1)"»"$, "->"),
)

#let resolution-lift-square() = cd(
  cell-size: (30mm, 18mm),
  $C' & C \ A' & A$,
  edge((0, 0), "r", $I$, "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", $i$, "->"),
)

#let projective-isomorphism-lift(transformed: false) = {
  if transformed {
    cd(
      cell-size: (70mm, 26mm),
      $P_1 plus.o P_2 & P_1 plus.o P_2 \ A_2 plus.o A_2 & A_2 plus.o A_2$,
      edge((0, 0), "d", $alpha f_1 plus.o f_2$, "->"),
      edge((1, 0), "d", $alpha f_1 plus.o f_2$, "->"),
      edge(
        (0, 1),
        "r",
        $
          mat(alpha, 0; 0, 1) mat(0, -alpha^(-1); alpha, 0)
          mat(alpha^(-1), 0; 0, 1)=mat(0, -1; 1, 0)
        $,
        "->",
      ),
    )
  } else {
    cd(
      cell-size: (42mm, 26mm),
      $P_1 plus.o P_2 & P_1 plus.o P_2 \
      A_1 plus.o A_2 & A_1 plus.o A_2 \ A_1 & A_2$,
      edge((0, 0), "r", $alpha'$, "->"),
      edge((0, 0), "d", $f_1 plus.o f_2$, "->"),
      edge((1, 0), "d", $f_1 plus.o f_2$, "->"),
      edge((0, 1), "r", $mat(0, -alpha^(-1); alpha, 0)$, "->"),
      edge((0, 1), "d", $(1,0)$, "->"),
      edge((1, 1), "d", $(0,1)$, "->"),
      edge((0, 2), "r", $alpha$, "->"),
    )
  }
}

#let projective-inverse-lifts() = cd(
  cell-size: (30mm, 22mm),
  $P_1 & P_2 \ A_2 & A_2$,
  edge((0, 0), "r", $h_1$, "->", shift: 1.4mm),
  edge((1, 0), "l", $h_2$, "->", shift: 1.4mm, label-side: left),
  edge((0, 0), "d", $alpha f_1$, "->"),
  edge((1, 0), "d", $f_2$, "->"),
  edge((0, 1), "r", $1$, "->"),
)

#let relative-resolution-functors() = cd(
  cell-size: (28mm, 19mm),
  $bold(C) & bold(C)' \ bold(C)_0 & bold(C)'_0$,
  edge((0, 0), "r", $F$, "->"),
  edge((0, 1), "r", $F_0$, "->"),
  edge((0, 1), "u", "hook->"),
  edge((1, 1), "u", "hook->"),
)

#let relative-resolution-lift() = cd(
  cell-size: (32mm, 22mm),
  $F Q & F Q \ F A_1 & F A_2$,
  edge((0, 0), "r", $alpha'_1$, "->"),
  edge((0, 0), "d", $F(f_1,0)$, "->"),
  edge((1, 0), "d", $F(0,f_2)$, "->"),
  edge((0, 1), "r", $alpha_1$, "->"),
)
