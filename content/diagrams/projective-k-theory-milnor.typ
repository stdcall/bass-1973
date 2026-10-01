#import "commutative.typ": cd, edge
#import "../main-defs.typ": (
  K, Pic, PicCat, Rk, SK, U, moduleCategory, spec, transpose,
)

#let milnor-ring-square() = cd(
  cell-size: (24mm, 17mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", $h_2$, "->"),
  edge((0, 0), "d", $h_1$, "->"),
  edge((1, 0), "d", $f_2$, "->"),
  edge((0, 1), "r", $f_1$, "->"),
)

#let milnor-category-square(fiber: false, modules: false) = {
  let origin = if fiber { $bold(M)$ } else { $moduleCategory-A$ }
  let category = if modules { $bold(M)$ } else { $bold(P)$ }
  let upperLeft = if modules {
    origin
  } else if fiber {
    category
  } else {
    $bold(P)(A)$
  }
  let horizontal = if fiber { $G_2$ } else { $H_2$ }
  let vertical = if fiber { $G_1$ } else { $H_1$ }
  cd(
    cell-size: (24mm, 17mm),
    $upperLeft & category_2 \ category_1 & category'$,
    edge((0, 0), "r", horizontal, "->"),
    edge((0, 0), "d", vertical, "->"),
    edge((1, 0), "d", $F_2$, "->"),
    edge((0, 1), "r", $F_1$, "->"),
  )
}

#let milnor-adjoint-square() = cd(
  cell-size: (22mm, 19mm),
  $S M & & M_2 \ M_1 & F_1 M_1 & F_2 M_2$,
  edge((0, 0), "rr", "->"),
  edge((0, 0), "d", "->"),
  edge((2, 0), "d", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", $alpha_M$, "->", label-side: right),
)

#let milnor-determinant-square(picard: false) = {
  let category = if picard { PicCat } else { $bold(P)$ }
  cd(
    cell-size: (25mm, 15mm),
    $category(A) & category(A_2) \ category(A_1) & category(A')$,
    edge((0, 0), "r", "->"),
    edge((0, 0), "d", "->"),
    edge((1, 0), "d", "->"),
    edge((0, 1), "r", "->"),
  )
}

#let milnor-quotient-square() = cd(
  cell-size: (29mm, 15mm),
  $A & A slash frak(q)_2 \ A slash frak(q)_1 & A slash (frak(q)_1+frak(q)_2)$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let milnor-conductor-square() = cd(
  cell-size: (24mm, 17mm),
  $A & B \ A slash frak(c) & B slash frak(c)$,
  edge((0, 0), "r", $j$, "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", $j'$, "->"),
)

#let milnor-intersection-square() = cd(
  cell-size: (23mm, 14mm),
  $A & A_2 \ A_1 & A'$,
  edge((0, 0), "r", "hook->"),
  edge((0, 0), "d", "hook->"),
  edge((1, 0), "d", "hook->"),
  edge((0, 1), "r", "hook->"),
)

#let milnor-product-induction-square() = cd(
  cell-size: (24mm, 14mm),
  $A & A'_1 \ B_1 & A''$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let milnor-spectrum-square() = cd(
  cell-size: (30mm, 19mm),
  $spec(A) & spec(A_2) \ spec(A_1) & spec(A')$,
  edge((1, 0), "l", $#transpose($h_2$, mark: $a$)$, "->"),
  edge((0, 1), "u", $#transpose($h_1$, mark: $a$)$, "->"),
  edge((1, 1), "u", $#transpose($f_2$, mark: $a$)$, "->"),
  edge((1, 1), "l", $#transpose($f_1$, mark: $a$)$, "->"),
)

#let milnor-two-squares() = cd(
  cell-size: (16mm, 12mm),
  $dot & dot & dot \ dot & dot & dot$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", "->"),
)

#let milnor-reduced-determinant-sequences() = {
  let arrows = ()
  for column in range(1, 7) {
    for row in range(4) {
      arrows.push(edge((column, row), "d", "->"))
    }
  }
  for row in range(1, 4) {
    for column in range(1, 6) {
      arrows.push(edge((column, row), "r", "->"))
    }
  }
  arrows.push(edge((0, 3), "r", "->"))
  cd(
    cell-size: (23mm, 14mm),
    $& 0 & 0 & 0 & 0 & 0 & 0 \ & SK_1 (A) & SK_1 (A_1) plus.o SK_1 (A_2) & SK_1 (A') & SK_0 (A) & SK_0 (A_1) plus.o SK_0 (A_2) & SK_0 (A') \ & K_1 (A) & K_1 (A_1) plus.o K_1 (A_2) & K_1 (A') & Rk_0 (A) & Rk_0 (A_1) plus.o Rk_0 (A_2) & Rk_0 (A') \ 0 & U(A) & U(A_1) plus.o U(A_2) & U(A') & Pic(A) & Pic(A_1) plus.o Pic(A_2) & Pic(A') \ & 0 & 0 & 0 & 0 & 0 & 0$,
    ..arrows,
  )
}
