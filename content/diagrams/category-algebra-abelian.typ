#import "commutative.typ": cd, edge
#import "../main-defs.typ": Coker, Ker

#let five-lemma() = cd(
  cell-size: (23mm, 17mm),
  $A_1 & A_2 & A_3 & A_4 & A_5 \ B_1 & B_2 & B_3 & B_4 & B_5$,
  ..range(4).map(i => edge((i, 0), "r", $a_(#(i + 1))$, "->")),
  ..range(4).map(i => edge(
    (i, 1),
    "r",
    $b_(#(i + 1))$,
    "->",
    label-side: right,
  )),
  ..range(5).map(i => edge((i, 0), "d", $c_(#(i + 1))$, "->")),
)

#let composite-kernels() = cd(
  cell-size: (24mm, 16mm),
  $& Ker(b) & & Coker(a) & \ & & B & & \ Ker(b a) & A & & C & Coker(b a) \ &
  Ker(a) & & Coker(b) &$,
  edge((1, 3), (0, 2), "->"),
  edge((1, 3), (1, 2), "->"),
  edge((0, 2), (1, 2), "->"),
  edge((0, 2), (1, 0), "->"),
  edge((1, 0), (2, 1), "->"),
  edge((1, 0), (3, 0), "->"),
  edge((1, 2), (2, 1), $a$, "->"),
  edge((1, 2), (3, 2), $b a$, "->", label-side: right),
  edge((2, 1), (3, 0), "->"),
  edge((2, 1), (3, 2), $b$, "->"),
  edge((3, 0), (4, 2), "->"),
  edge((3, 2), (4, 2), "->"),
  edge((3, 2), (3, 3), "->"),
  edge((4, 2), (3, 3), "->"),
)

#let pullback-epi-triangle() = cd(
  cell-size: (29mm, 18mm),
  $& A' xor A_2 & \ A_1 xor A_2 & & A'$,
  edge((0, 1), (1, 0), $a_1 xor 1$, "->"),
  edge((1, 0), (2, 1), $(1, -a_2)$, "->"),
  edge((0, 1), (2, 1), $(a_1, -a_2)$, "->", label-side: right),
)

#let snake-input() = cd(
  cell-size: (23mm, 17mm),
  $(0 ->) & A'_1 & A_1 & A''_1 & 0 \ 0 & A'_2 & A_2 & A''_2 & (-> 0)$,
  ..range(3).map(i => edge(
    (i, 0),
    "r",
    if i == 1 { $a_1$ } else if i == 2 { $a'_1$ },
    "->",
  )),
  edge((3, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", $a_2$, "->"),
  edge((2, 1), "r", $a'_2$, "->"),
  edge((1, 0), "d", $d'$, "->"),
  edge((2, 0), "d", $d$, "->"),
  edge((3, 0), "d", $d''$, "->"),
)

#let snake-pullback() = cd(
  cell-size: (33mm, 17mm),
  $P & Ker(d'') \ A_1 & A''_1$,
  edge((0, 0), "r", $p$, "->"),
  edge((0, 0), "d", $q$, "->", label-side: right),
  edge((1, 0), "d", $j$, "->"),
  edge((0, 1), "r", $a'_1$, "->", label-side: right),
)

#let snake-exact-pullback() = cd(
  cell-size: (25mm, 17mm),
  $0 & Ker(p) & P & Ker(d'') & 0 \ 0 & Ker(a'_1) & A_1 & A''_1 & 0$,
  ..range(4).map(i => edge(
    (i, 0),
    "r",
    if i == 1 { $i$ } else if i == 2 { $p$ },
    "->",
  )),
  ..range(4).map(i => edge((i, 1), "r", if i == 2 { $a'_1$ }, "->")),
  edge((1, 0), "d", $tilde.eq$, "->"),
  edge((2, 0), "d", $q$, "->"),
  edge((3, 0), "d", "->"),
)

#let snake-construction() = cd(
  cell-size: (26mm, 17mm),
  $& 0 & & 0 & \ 0 & Ker(p) & P & Ker(d'') & 0 \ & A'_1 & A_1 & A''_1 & 0 \ 0
  & A'_2 & A_2 & A''_2 & \ & Coker(d') & & & \ & 0 & & &$,
  edge((1, 1), "u", "->"),
  edge((3, 0), "d", "->"),
  ..range(4).map(i => edge(
    (i, 1),
    "r",
    if i == 1 { $i$ } else if i == 2 { $p$ },
    "->",
  )),
  edge((1, 2), "u", $r$, "->", label-side: right),
  edge((1, 2), "r", $a_1$, "->"),
  edge((2, 1), "d", $q$, "->"),
  edge((3, 1), "d", $j$, "->"),
  edge((2, 2), "r", $a'_1$, "->"),
  edge((3, 2), "r", "->"),
  edge((1, 2), "d", $d'$, "->", label-side: right),
  edge((2, 2), "d", $d$, "->"),
  edge((3, 2), "d", $d''$, "->"),
  edge((0, 3), "r", "->"),
  edge((1, 3), "r", $a_2$, "->", label-side: right),
  edge((2, 3), "r", $a'_2$, "->", label-side: right),
  edge((1, 3), "d", $s$, "->", label-side: right),
  edge((1, 4), "d", "->"),
  edge((2, 1), (1, 3), $h$, "-->"),
)
