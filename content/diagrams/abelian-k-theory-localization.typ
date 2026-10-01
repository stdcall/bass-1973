#import "commutative.typ": cd, edge, node
#import "../main-defs.typ": Im, K, Ker

#let localization-refinement() = cd(
  cell-size: (33mm, 20mm),
  $A & B'' \ A' & B' \ A'' & B$,
  edge((0, 0), "r", $f_A$, "->"),
  edge((0, 1), "r", $f$, "->"),
  edge((0, 2), "r", $f_B$, "->"),
  edge((0, 1), "u", $a$, "->"),
  edge((0, 2), "u", $a'$, "->"),
  edge((1, 1), "u", $b'$, "->"),
  edge((1, 2), "u", $b$, "->"),
)

#let localization-composition() = cd(
  cell-size: (22mm, 20mm),
  $A & A' & B' & & \ & A'' & B & C'' & \ & & B_1 & C' & C$,
  edge((1, 0), "l", $a$, "->"),
  edge((1, 0), "r", $f$, "->"),
  edge((1, 1), "r", $f_B$, "->"),
  edge((2, 1), "r", $g_B$, "->"),
  edge((2, 2), "r", $g$, "->"),
  edge((4, 2), "l", $c$, "->"),
  edge((1, 1), "u", "->"),
  edge((2, 1), "u", "->"),
  edge((2, 2), "u", "->"),
  edge((3, 2), "u", $c'$, "->"),
)

#let localization-common-representation() = cd(
  cell-size: (26mm, 20mm),
  $& A'_0 & B'_0 & \ A & A' & B' & B \ & A'_1 & B'_1 &$,
  edge((1, 0), "r", $f_0$, "->"),
  edge((1, 1), "r", $f'$, "->"),
  edge((1, 2), "r", $f_1$, "->"),
  edge((1, 0), (0, 1), $a_0$, "->"),
  edge((1, 1), "l", $a$, "->"),
  edge((1, 2), (0, 1), $a_1$, "->"),
  edge((3, 1), (2, 0), $b_0$, "->"),
  edge((3, 1), "l", $b$, "->"),
  edge((3, 1), (2, 2), $b_1$, "->"),
  edge((1, 1), "u", $alpha_0$, "->"),
  edge((1, 1), "d", $alpha_1$, "->"),
  edge((2, 0), "d", $beta_0$, "->"),
  edge((2, 2), "u", $beta_1$, "->"),
)

#let localization-monic-representation() = cd(
  cell-size: (42mm, 23mm),
  $& A' & B' & \ A & A' slash Ker (a) & B' slash f(Ker (a)) & B \
  & f^(-1)(Im (b_1)) & Im (b_1) &$,
  edge((1, 0), "r", $f$, "->"),
  edge((1, 1), "r", $f_1$, "->"),
  edge((1, 2), "r", $f_2$, "->"),
  edge((1, 0), (0, 1), $a$, "->"),
  edge((1, 1), "l", $a_1$, "->"),
  edge((1, 2), (0, 1), $a_2$, "->"),
  edge((3, 1), (2, 0), $b$, "->"),
  edge((3, 1), "l", $b_1$, "->"),
  edge((3, 1), (2, 2), $b_2$, "->"),
  edge((1, 0), "d", "->"),
  edge((2, 0), "d", "->"),
  edge((1, 2), "u", "hook->"),
  edge((2, 2), "u", "hook->"),
  node((1.5, 0.5), [естественные проекции]),
  node((1.5, 1.5), [вложения]),
)

#let localization-complex-lift(quotient: false) = {
  if quotient {
    cd(
      cell-size: (34mm, 21mm),
      $overline(S) A_2 & overline(S) A_1 & overline(S) A_0 \
      overline(S) B_2 & overline(S) B_1 & overline(S) B_0$,
      edge((0, 0), "r", $overline(S) alpha_1$, "->"),
      edge((1, 0), "r", $overline(S) alpha_0$, "->"),
      edge((0, 1), "r", $overline(S) beta_1$, "->"),
      edge((1, 1), "r", $overline(S) beta_0$, "->"),
      ..range(3).map(i => edge(
        (i, 0),
        "d",
        ($gamma_2$, $gamma_1$, $gamma_0$).at(i),
        "->",
      )),
    )
  } else {
    cd(
      cell-size: (31mm, 18mm),
      $A_2 & A_1 & A_0 \ A'_2 & A'_1 & A'_0 \
      B'_2 & B'_1 & B'_0 \ B_2 & B_1 & B_0$,
      edge((0, 0), "r", $alpha_1$, "->"),
      edge((1, 0), "r", $alpha_0$, "->"),
      edge((0, 1), "r", $alpha'_1$, "->"),
      edge((1, 1), "r", $alpha'_0$, "->"),
      edge((0, 2), "r", $beta'_1$, "->"),
      edge((1, 2), "r", $beta'_0$, "->"),
      edge((0, 3), "r", $beta_1$, "->"),
      edge((1, 3), "r", $beta_0$, "->"),
      ..range(3).map(i => edge(
        (i, 1),
        "u",
        ($a_2$, $a_1$, $a_0$).at(i),
        "->",
      )),
      ..range(3).map(i => edge(
        (i, 1),
        "d",
        ($f_2$, $f_1$, $f_0$).at(i),
        "->",
      )),
      ..range(3).map(i => edge(
        (i, 3),
        "u",
        ($b_2$, $b_1$, $b_0$).at(i),
        "->",
      )),
    )
  }
}

#let localization-exact-functor-square(projective: false, resolved: false) = {
  let top-left = if resolved { $bold(H)$ } else { $bold(A)$ }
  let top-right = if resolved { $bold(H)'$ } else { $bold(A)'$ }
  let bottom-left = if projective { $bold(P)$ } else { $bold(C)$ }
  let bottom-right = if projective { $bold(P)'$ } else { $bold(C)'$ }
  cd(
    cell-size: (30mm, 19mm),
    $#top-left & #top-right \ #bottom-left & #bottom-right$,
    edge((0, 0), "r", if resolved { $T$ } else { $overline(S)$ }, "->"),
    edge((0, 1), "r", $S$, "->"),
    edge((0, 1), "u", "hook->"),
    edge((1, 1), "u", "hook->"),
  )
}

#let localization-exact-comparison(projective: false) = {
  if projective {
    cd(
      cell-size: (28mm, 20mm),
      $K_1 (bold(H)) & K_1 (bold(H)') & K'_0 (T) & K_0 (bold(H)) & K_0
      (bold(H)') \
      K_1 (bold(P)) & K_1 (bold(P)') & K'_0 (S) & K_0 (bold(P)) & K_0
      (bold(P)')$,
      edge((0, 0), "r", "->"),
      edge((1, 0), "r", "->"),
      edge((2, 0), "r", $d''$, "->"),
      edge((3, 0), "r", "->"),
      edge((0, 1), "r", "->"),
      edge((1, 1), "r", $partial'$, "->"),
      edge((2, 1), "r", $d'$, "->"),
      edge((3, 1), "r", "->"),
      ..range(5).map(i => edge((i, 1), "u", "->")),
    )
  } else {
    cd(
      cell-size: (27mm, 20mm),
      $K_1 (bold(A)') & K_0 (bold(S)) & K_0 (bold(A)) & K_0 (bold(A)') & 0 \
      K_1 (bold(C)') & K_0 (bold(S)) & K_0 (bold(C)) & K_0 (bold(C)') & 0$,
      edge((0, 0), "r", $overline(partial)$, "->"),
      edge((1, 0), "r", $overline(d)$, "->"),
      edge((2, 0), "r", "->"),
      edge((3, 0), "r", "->"),
      edge((0, 1), "r", $partial$, "->"),
      edge((1, 1), "r", $d$, "->"),
      edge((2, 1), "r", "->"),
      edge((3, 1), "r", "->"),
      edge((0, 1), "u", "->"),
      edge((1, 1), "u", "="),
      edge((2, 1), "u", $h$, "->"),
      edge((3, 1), "u", "->"),
    )
  }
}

#let localization-k0-triangle() = cd(
  cell-size: (30mm, 23mm),
  $& K_0 (bold(H)_bold(S)) & \ K'_0 (S) & & K'_0 (T)$,
  edge((0, 1), (1, 0), $psi$, "->"),
  edge((1, 0), (2, 1), $phi$, "->"),
  edge((0, 1), (2, 1), $h$, "->"),
)
