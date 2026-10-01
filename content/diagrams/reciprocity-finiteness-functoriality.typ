#import "commutative.typ": cd, edge
#import "../main-defs.typ": K, SK, res, tensor

#let reciprocity-categories(restriction: false) = {
  let arrow = if restriction { "<-" } else { "->" }
  let label = if restriction { $res$ } else { $tensor_A A'$ }
  cd(
    cell-size: (47mm, 24mm),
    $bold(italic(M))(A,frak(q)) & bold(italic(M))(A',frak(q)') \
    bold(italic(M))_S (A,frak(q)) & bold(italic(M))_(S') (A',frak(q)')$,
    edge((0, 0), "r", label, arrow),
    edge((0, 1), "r", label, arrow, label-side: right),
    edge((0, 1), "u", "hook->"),
    edge((1, 1), "u", "hook->"),
  )
}

#let reciprocity-k-groups(restriction: false) = {
  let arrow = if restriction { "<-" } else { "->" }
  let label = if restriction { $f^*$ } else { $f_*$ }
  cd(
    cell-size: (55mm, 27mm),
    $SK_1 (A,frak(q)) & SK_1 (A',frak(q)') \
    K_1 (bold(italic(M))_S (A,frak(q))) &
    K_1 (bold(italic(M))_(S') (A',frak(q)')) \
    product.co_(frak(p) divides.not frak(q)) K_1 (A slash frak(p)) &
    product.co_(frak(p)' divides.not frak(q)') K_1 (A' slash frak(p)')$,
    edge((0, 0), "r", label, arrow),
    edge((0, 1), "r", arrow),
    edge((0, 2), "r", label, arrow, label-side: right),
    edge((0, 1), "u", $chi(frak(q))$, "->"),
    edge((1, 1), "u", $chi(frak(q)')$, "->", label-side: right),
    edge((0, 2), "u", "="),
    edge((1, 2), "u", "="),
  )
}
