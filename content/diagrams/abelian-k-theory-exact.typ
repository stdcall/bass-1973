#import "commutative.typ": cd, edge
#import "../main-defs.typ": K

#let exact-quotient-square() = cd(
  cell-size: (36mm, 20mm),
  $K'_0 (F,plus.o) & K_0 (bold(C),plus.o) \ K'_0 (F) & K_0 (bold(C))$,
  edge((0, 0), "r", $d_(plus.o)$, "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", $d$, "->"),
)

#let cofinal-exact-comparison(kernels: false, semisimple: false) = {
  let n2 = if semisimple { $0$ } else { $N_2$ }
  let n5 = if semisimple { $0$ } else { $N_5$ }
  if kernels {
    cd(
      cell-size: (28mm, 20mm),
      $N_1 & #n2 & N_3 & N_4 & #n5 \
      K_1 (bold(C),plus.o) & K_1 (bold(C)',plus.o) & K'_0 (F,plus.o) & K_0
      (bold(C),plus.o) & K_0 (bold(C)',plus.o) \
      K_1 (bold(C)) & K_1 (bold(C)') & K'_0 (F) & K_0 (bold(C)) & K_0
      (bold(C)')$,
      ..range(5).map(i => edge((i, 0), "d", "->")),
      ..range(5).map(i => edge((i, 1), "d", "->")),
      ..if semisimple { () } else {
        range(4).map(i => edge((i, 0), "r", "->"))
      },
      edge((0, 1), "r", "->"),
      edge(
        (1, 1),
        "r",
        if semisimple { none } else { $partial_(plus.o)$ },
        "->",
      ),
      edge((2, 1), "r", if semisimple { none } else { $d_(plus.o)$ }, "->"),
      edge((3, 1), "r", "->"),
      edge((0, 2), "r", "->"),
      edge((1, 2), "r", if semisimple { none } else { $partial$ }, "->"),
      edge((2, 2), "r", if semisimple { none } else { $d$ }, "->"),
      edge((3, 2), "r", "->"),
    )
  } else {
    cd(
      cell-size: (28mm, 20mm),
      $K_1 (bold(C),plus.o) & K_1 (bold(C)',plus.o) & K'_0 (F,plus.o) & K_0
      (bold(C),plus.o) & K_0 (bold(C)',plus.o) \
      K_1 (bold(C)) & K_1 (bold(C)') & K'_0 (F) & K_0 (bold(C)) & K_0
      (bold(C)')$,
      edge((0, 0), "r", "->"),
      edge((1, 0), "r", $partial_(plus.o)$, "->"),
      edge((2, 0), "r", "->"),
      edge((3, 0), "r", "->"),
      ..range(5).map(i => edge(
        (i, 0),
        "d",
        if i == 2 { $f$ } else { none },
        "->",
      )),
      edge((0, 1), "r", "->"),
      edge((1, 1), "r", $partial$, "..>"),
      edge((2, 1), "r", "->"),
      edge((3, 1), "r", "->"),
    )
  }
}

#let devissage-composition-square() = cd(
  cell-size: (36mm, 20mm),
  $K_0 (Sigma bold(C)_0) & K_0 (Sigma bold(C)) \
  K_1 (bold(C)_0) & K_1 (bold(C))$,
  edge((0, 0), "r", $i$, "->"),
  edge((0, 0), "d", $p_0$, "->", label-side: right),
  edge((1, 0), "d", $p$, "->"),
  edge((0, 1), "r", $j_1$, "->"),
)
