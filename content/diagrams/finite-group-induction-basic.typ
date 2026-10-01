#import "../main-defs.typ": G, K, moduleCategory, res, tensor
#import "commutative.typ": cd, edge, node

#let induction-pair(kind) = {
  let objects = if kind == "group" {
    $moduleCategory-R pi' & moduleCategory-R pi.$
  } else { $moduleCategory-R' pi & moduleCategory-R pi.$ }
  let direct = if kind == "group" {
    $j_*=(dot tensor_(R pi') R pi)$
  } else { $f_*=(dot tensor_(R') R)$ }
  let inverse = if kind == "group" { $j^*=res$ } else { $f^*=res$ }
  cd(
    cell-size: (60mm, 15mm),
    objects,
    edge((0, 0), "r", direct, "->", shift: 1.4mm),
    edge((1, 0), "l", inverse, "->", shift: 1.4mm, label-side: left),
  )
}

#let scalar-extension-square() = cd(
  cell-size: (25mm, 13mm),
  $R' pi' & R' pi \ R pi' & R pi$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", "->"),
  edge((1, 0), "d", "->"),
  edge((0, 1), "r", "->"),
)

#let frobenius-morphism() = cd(
  cell-size: (24mm, 15mm),
  $A & B,$,
  edge((0, 0), "r", $i_*$, "->", shift: 1.4mm),
  edge((1, 0), "l", $i^*$, "->", shift: 1.4mm, label-side: left),
)

#let frobenius-module-morphism() = cd(
  cell-size: (30mm, 15mm),
  $K (pi') & K (pi),$,
  edge((0, 0), "r", $j_*$, "->", shift: 1.4mm),
  edge((1, 0), "l", $j^*$, "->", shift: 1.4mm, label-side: left),
)

#let swan-group-ring-triangle(frobenius: false) = {
  let objects = if frobenius { $G_R (pi) & G_L (pi) \ &$ } else {
    $G_0 (R pi) & G_0 (L pi) \ &$
  }
  let bottom = if frobenius { $G_(R slash frak(p)) (pi)$ } else {
    $G_0 ((R slash frak(p)) pi)$
  }
  cd(
    cell-size: (40mm, 15mm),
    objects,
    edge((0, 0), "r", if not frobenius { $g_0$ }, "->"),
    edge(
      (0, 0),
      (0.5, 1),
      if not frobenius { $phi_frak(p)$ },
      "->",
      label-side: right,
    ),
    edge((1, 0), (0.5, 1), if not frobenius { $delta_frak(p)$ }, "->"),
    node((0.5, 1), bottom),
  )
}

#let brauer-cartan-diagram() = cd(
  cell-size: (38mm, 19mm),
  $K_0 (R pi) & G_R (pi) & G_L (pi) \ K_0 (k pi) & G_k (pi) &$,
  edge((0, 0), "r", $c_0 (R pi)$, "->"),
  edge((1, 0), "r", $g_0 (pi)$, "->"),
  edge((0, 0), "d", $psi_frak(m)$, "->", label-side: right),
  edge((1, 0), "d", $phi_frak(m)$, "->"),
  edge((2, 0), (1, 1), $delta_frak(m)$, "->"),
  edge((0, 1), "r", $c_0 (k pi)$, "->"),
)

#let restriction-induction-pair(kind) = {
  let objects = if kind == "relative-projective" {
    $bold(M)_0 (R pi') & bold(M)_0 (R pi)$
  } else if kind == "projective" {
    $italic(P) (R pi') & italic(P) (R pi).$
  } else { $K_R (pi') & K_R (pi).$ }
  cd(
    cell-size: (38mm, 15mm),
    objects,
    edge((0, 0), "r", $j_*$, "->", shift: 1.4mm),
    edge((1, 0), "l", $j^*$, "->", shift: 1.4mm, label-side: left),
  )
}
