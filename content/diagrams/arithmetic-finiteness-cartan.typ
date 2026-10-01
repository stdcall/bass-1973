#import "../main-defs.typ": G, K, Ker
#import "commutative.typ": cd, edge, node

#let diagram-cartan-localization() = cd(
  cell-size: (26mm, 15mm),
  $K_1(A) & K_1(Lambda) & K_0(A,S) & K_0(A) & K_0(Lambda) \ & G_1(Lambda) & G_0(A,S) & G_0(A) & G_0(Lambda) \ & & union.sq.big_(frak(p) in X) G_0(A slash frak(p) A)$,
  edge((0, 0), "r", $k_1$, "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $k_0$, "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((3, 1), "r", $g_0$, "->", label-side: right),
  edge((1, 0), "d", $c_1(Lambda)$, "->", label-side: left),
  edge((1, 0), "d", $(tilde.eq)$, label-side: right),
  edge((2, 0), "d", $c_0(A,S)$, "->"),
  edge((3, 0), "d", $c_0(A)$, "->"),
  edge((4, 0), "d", $c_0(Lambda)$, "->", label-side: left),
  edge((4, 0), "d", $(tilde.eq)$, label-side: right),
  edge((2, 1), "d", "="),
)

#let diagram-swan-triangle(a) = cd(
  cell-size: (28mm, 15mm),
  $G_0(A) & G_0(Lambda) \ &$,
  edge((0, 0), "r", $g_0$, "->"),
  edge((0, 0), (0.5, 1), $phi_#a$, "->", label-side: right),
  edge((1, 0), (0.5, 1), $delta_#a$, "->"),
  node((0.5, 1), $G_0(A slash A #a)$),
)

#let diagram-swan-local-cartan() = cd(
  cell-size: (30mm, 15mm),
  $& K_0(Lambda) & G_0(Lambda) \ K_0(A) & G_0(A) & \ & K_0(A slash A frak(p)) & G_0(A slash A frak(p))$,
  edge((0, 1), "ur", $k_0$, "->"),
  edge((1, 0), "r", $c_0(Lambda)$, "->"),
  edge((1, 0), "r", $(tilde.eq)$, label-side: right),
  edge((0, 1), "r", $c_0(A)$, "->"),
  edge((1, 1), "ur", $g_0$, "->"),
  edge((0, 1), "dr", $psi_frak(p)$, "->", label-side: right),
  edge((1, 1), "dr", $phi_frak(p)$, "->"),
  edge((2, 0), "dd", $delta_frak(p)$, "->"),
  edge((1, 2), "r", $c_0(frak(p))$, "->", label-side: right),
)

#let diagram-regular-cartan-localization() = cd(
  cell-size: (28mm, 15mm),
  $K_0(A,T) & K_0(A) & K_0(T^(-1) A) & 0 \ G_0(A,T) & G_0(A) & G_0(T^(-1) A) & 0$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((2, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((1, 1), "r", "->"),
  edge((2, 1), "r", "->"),
  edge((0, 0), "d", $c_0(A,T)$, "->", label-side: left),
  edge((0, 0), "d", $(tilde.eq)$, label-side: right),
  edge((1, 0), "d", $c_0(A)$, "->"),
  edge((2, 0), "d", $c_0(T^(-1) A)$, "->"),
)

#let diagram-cartan-order-comparison(kernels: false) = {
  let objects = if kernels {
    $Ker (k_0(A)) & Ker (k_0(B)) \ Ker (g_0(A)) & Ker (g_0(B))$
  } else { $K_0(A) & K_0(B) \ G_0(A) & G_0(B)$ }
  cd(
    cell-size: (32mm, 15mm),
    objects,
    edge((0, 0), "r", "->"),
    edge((1, 1), "l", "->"),
    edge((0, 0), "d", if not kernels { $c_0(A)$ }, "->", label-side: right),
    edge((1, 0), "d", if not kernels { $c_0(B)$ }, "->", label-side: left),
    edge((1, 0), "d", $(tilde.eq)$, label-side: right),
  )
}

#let diagram-conductor-pullback() = cd(
  cell-size: (22mm, 12mm),
  $A & B \ A' & B'$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let diagram-cartan-class-number() = cd(
  cell-size: (30mm, 15mm),
  $K_0(A) & K_0(Lambda) \ G_0(A) & G_0(Lambda)$,
  edge((0, 0), "r", $k_0$, "->"),
  edge((0, 0), "d", $c_0(A)$, "->", label-side: right),
  edge((1, 0), "d", $c_0(Lambda)$, "->", label-side: left),
  edge((1, 0), "d", $(tilde.eq)$, label-side: right),
  edge((0, 1), "r", $g_0$, "->", label-side: right),
)

#let diagram-cartan-kernels() = cd(
  cell-size: (32mm, 15mm),
  $K_0(A,S) & Ker(k_0) & 0 \ G_0(A,S) & Ker(g_0)$,
  edge((0, 0), "r", "->"),
  edge((1, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  edge((0, 0), "d", $c_0(A,S)$, "->", label-side: right),
  edge((1, 0), "d", $h$, "->"),
  edge(
    (1, 0),
    "d",
    block(width: 42mm)[(отображение, индуцированное $c_0(A)$)],
    label-side: left,
  ),
)

#let diagram-cartan-k1-order-comparison() = cd(
  cell-size: (30mm, 15mm),
  $K_1(A) & K_1(B) \ G_1(A) & G_1(B)$,
  edge((0, 0), "r", $j_*$, "->"),
  edge((1, 1), "l", "->"),
  edge((0, 0), "d", $c_1(A)$, "->", label-side: right),
  edge((1, 0), "d", $c_1(B)$, "->", label-side: left),
  edge((1, 0), "d", $(tilde.eq)$, label-side: right),
)
