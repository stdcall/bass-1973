#import "commutative.typ": cd, edge
#import "../main-defs.typ": G, K, Pic, Rk, SK, U, det

#let localization-devissage-sequence(resolution: false) = {
  let lowerCategory = if resolution { $C_0$ } else { $C$ }
  let lowerPrime = if resolution { $C'_0$ } else { $C'$ }
  let upperFirst = if resolution { $K_1 (C')$ } else { $G_1 (S^(-1)A)$ }
  let upperThird = if resolution { $K_0 (C)$ } else { $G_0 (A)$ }
  let upperFourth = if resolution { $K_0 (C')$ } else { $G_0 (S^(-1)A)$ }
  let upperFinal = if resolution { none } else { $0$ }
  cd(
    cell-size: (33mm, 19mm),
    $upperFirst & G_0 (A, S) & upperThird & upperFourth & upperFinal \ K_1 (lowerPrime) & G_0 (A, S) & K_0 (lowerCategory) & K_0 (lowerPrime)$,
    ..range(if resolution { 3 } else { 4 }).map(i => edge((i, 0), "r", "->")),
    ..range(3).map(i => edge((i, 1), "r", "->")),
    ..(0, 2, 3).map(i => edge((i, 1), "u", "->")),
    edge((1, 1), "u", "=", label-side: right),
  )
}

#let localization-divisor-square() = cd(
  cell-size: (33mm, 20mm),
  $G_0 (A, T) & G_0 (A, S) \ D(A, T) & D(A)$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", $chi_T$, "->"),
  edge((1, 0), "d", $chi$, "->", label-side: right),
  edge((0, 1), "r", "->"),
)

#let localization-picard-identification() = cd(
  cell-size: (28mm, 18mm),
  $& Pic(f) \ U(S^(-1)A) & & Pic(A) \ & Pic(A, S)$,
  edge((0, 1), "ur", $partial$, "->"),
  edge((0, 1), "dr", "->"),
  edge((1, 0), "dr", $d$, "->"),
  edge((1, 2), "ur", "->"),
  edge((1, 2), "uu", $h$, "->", label-side: right),
)

#let localization-picard-sequences(regular: false) = {
  let terminalGroup = if regular { Rk } else { K }
  let topGroup = if regular { $G_0 (A, S)$ } else { none }
  let finalGroup = if regular { $0$ } else { none }
  cd(
    cell-size: (34mm, 19mm),
    $& & topGroup \ K_1 (A) & K_1 (S^(-1)A) & K_0 (A, S) & terminalGroup_0 (A) & terminalGroup_0 (S^(-1)A) & finalGroup \ U(A) & U(S^(-1)A) & Pic(A, S) & Pic(A) & Pic(S^(-1)A) & finalGroup$,
    ..range(if regular { 5 } else { 4 }).map(i => edge((i, 1), "r", "->")),
    ..range(if regular { 5 } else { 4 }).map(i => edge((i, 2), "r", "->")),
    ..range(5).map(i => {
      let determinantLabel = if not regular { none } else if i == 0 {
        $det_1 (A)$
      } else if i == 1 { $det_1 (S^(-1)A)$ } else if i == 2 {
        $det_0 (A, S)$
      } else if i == 3 { $det_0 (A)$ } else { $det_0 (S^(-1)A)$ }
      edge((i, 1), "d", determinantLabel, "->", label-side: right)
    }),
    ..if regular { (edge((2, 0), "d", "="),) } else { () },
  )
}

#let localization-dedekind-determinant-diagram() = cd(
  cell-size: (33mm, 20mm),
  $0 & 0 & 0 & 0 & 0 \ SK_1 (A) & SK_1 (B) & union.sq.big_(frak(p) in X) tilde(G)_0 (A slash (frak(p) A)) & tilde(Rk)_0 (A) & tilde(Rk)_0 (B) & 0 \ K_1 (A) & K_1 (B) & union.sq.big_(frak(p) in X) G_0 (A slash (frak(p) A)) & Rk_0 (A) & Rk_0 (B) & 0 \ U(A) & U(B) & D(R) & Pic(A) & Pic(B) & 0 \ 0 & 0 & 0 & 0 & 0$,
  ..range(5).map(i => edge((i, 0), "d", "->")),
  ..range(5).map(i => edge((i, 1), "d", "->")),
  ..range(5).map(i => edge((i, 3), "d", "->")),
  ..range(1, 4).map(j => range(5).map(i => edge((i, j), "r", "->"))).flatten(),
  edge((0, 2), "d", $det_1 (A)$, "->", label-side: right),
  edge((1, 2), "d", $det_1 (B)$, "->", label-side: right),
  edge((2, 2), "d", $delta$, "->", label-side: right),
  edge((3, 2), "d", $det_0 (A)$, "->", label-side: right),
  edge((4, 2), "d", $det_0 (B)$, "->", label-side: right),
)

#let localization-dedekind-kernel-sequence() = cd(
  cell-size: (31mm, 18mm),
  $& & & 0 \ SK_1 (A) & SK_1 (B) & union.sq.big_(frak(p) in X) Pic(A slash (frak(p) A)) & tilde(Rk)_0 (A) & 0 \ & & & Rk_0 (A) \ & & & Pic(A) \ & & & 0$,
  ..range(4).map(i => edge((i, 1), "r", "->")),
  ..range(4).map(j => edge(
    (3, j),
    "d",
    if j == 2 {
      $det_0 (A)$
    } else { none },
    "->",
    label-side: right,
  )),
)

#let localization-injective-square() = cd(
  cell-size: (30mm, 20mm),
  $P & Q \ S^(-1)P & S^(-1)Q$,
  edge((0, 0), "r", $f$, "->"),
  edge((0, 0), "d", $h_P$, "->"),
  edge((1, 0), "d", $h_Q$, "->", label-side: right),
  edge((0, 1), "r", $S^(-1)f$, "->", label-side: right),
)

#let localization-cartan-sequences(complete: false) = {
  let lowerFirst = if complete { $G_1 (A)$ } else { none }
  let upperFinal = if complete { $0$ } else { none }
  cd(
    cell-size: (33mm, 19mm),
    $K_1 (A) & K_1 (S^(-1)A) & K_0 (A, S) & K_0 (A) & K_0 (S^(-1)A) & upperFinal \ lowerFirst & G_1 (S^(-1)A) & G_0 (A, S) & G_0 (A) & G_0 (S^(-1)A) & 0$,
    ..range(if complete { 5 } else { 4 }).map(i => edge((i, 0), "r", "->")),
    ..range(if complete { 0 } else { 1 }, 5).map(i => edge((i, 1), "r", "->")),
    ..range(if complete { 0 } else { 1 }, 5).map(i => {
      let cartanLabel = if complete { none } else if i == 1 {
        $c_1 (S^(-1)A)$
      } else if i == 2 { $c_0 (A, S)$ } else if i == 3 {
        $c_0 (A)$
      } else { $c_0 (S^(-1)A)$ }
      edge((i, 0), "d", cartanLabel, "->", label-side: right)
    }),
  )
}

#let localization-regular-sequence() = cd(
  cell-size: (31mm, 16mm),
  $& & G_0 (A, S) \ K_1 (A) & K_1 (S^(-1)A) & K_0 (A, S) & K_0 (A) & K_0 (S^(-1)A) & 0$,
  edge((2, 0), "d", "="),
  ..range(5).map(i => edge((i, 1), "r", "->")),
)

#let localization-divisor-sequence(restricted: false) = {
  let localizedRing = if restricted { $B$ } else { $L$ }
  let system = if restricted { $T$ } else { $S$ }
  let divisors = if restricted { $D(A, T)$ } else { $D(A)$ }
  let finalClass = if restricted { $C(B)$ } else { $0$ }
  let finalZero = if restricted { $0$ } else { none }
  cd(
    cell-size: (33mm, 20mm),
    $G_1 (localizedRing) & G_0 (A, system) & G_0 (A) & G_0 (localizedRing) & 0 \ U(localizedRing) & divisors & C(A) & finalClass & finalZero$,
    edge((0, 0), "r", $partial$, "->"),
    ..range(1, 4).map(i => edge((i, 0), "r", "->")),
    ..range(if restricted { 4 } else { 3 }).map(i => edge((i, 1), "r", "->")),
    edge((0, 0), "d", $det$, "->"),
    edge(
      (1, 0),
      "d",
      if restricted { $chi_T$ } else { $chi$ },
      "->",
      label-side: right,
    ),
    edge((2, 0), "d", $"cl"$, "->", label-side: right),
    edge(
      (3, 0),
      "d",
      if restricted { $"cl"$ } else { none },
      "->",
      label-side: right,
    ),
  )
}

#let localization-determinant-square(grothendieck: false) = {
  let upperGroup = if grothendieck { G } else { K }
  cd(
    cell-size: (33mm, 20mm),
    $upperGroup_1 (L) & upperGroup_0 (A, S) \ U(L) & D(A)$,
    edge((0, 0), "r", $partial$, "->"),
    edge((0, 0), "d", $det$, "->"),
    edge((1, 0), "d", $chi$, "->", label-side: right),
    edge((0, 1), "r", "->"),
  )
}
