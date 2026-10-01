#import "commutative.typ": cd, edge
#import "../main-defs.typ": G, K, tensor

#let cartan-naturality() = cd(
  cell-size: (29mm, 19mm),
  $K_i (A) & K_i (B) \ G_i (A) & G_i (B)$,
  edge((0, 0), "r", "->"),
  edge((0, 0), "d", $c_i (A)$, "->"),
  edge((1, 0), "d", $c_i (B)$, "->"),
  edge((0, 1), "r", "->"),
)

#let cartan-radical-base-change(group) = cd(
  cell-size: (36mm, 20mm),
  $group_0 (A) & group_0 (A tensor_R L) \ group_0 (overline(A)) & group_0 (overline(A) tensor_R L)$,
  edge((0, 0), "r", "->"),
  edge((0, 1), "r", "->"),
  ..if group == K {
    (edge((0, 0), "d", "->"), edge((1, 0), "d", "->"))
  } else {
    (edge((0, 1), "u", "->"), edge((1, 1), "u", "->"))
  },
)
