#import "commutative.typ": cd, edge
#import "../main-defs.typ": K, Pic, PicCat, Rk, U, det, tensor

#let picard-quotient-triangle() = cd(
  cell-size: (21mm, 17mm),
  $& PicCat(A slash frak(q)) & \ PicCat(A) & & PicCat(A slash frak(q)')$,
  edge((0, 1), "ur", "->"),
  edge((1, 0), "dr", "->"),
  edge((0, 1), "rr", "->"),
)

#let determinant-naturality() = cd(
  cell-size: (31mm, 20mm),
  $bold(P)(A) & bold(P)(B) \ PicCat(A) & PicCat(B)$,
  edge((0, 0), "r", $tensor_A B$, "->"),
  edge((0, 0), "d", $det(A)$, "->"),
  edge((1, 0), "d", $det(B)$, "->"),
  edge((0, 1), "r", $tensor_A B$, "->", label-side: right),
)

#let determinant-exact-sequences(reduced: false) = {
  let rankGroup = if reduced { Rk } else { K }
  cd(
    cell-size: (25mm, 21mm),
    $K_1 (A) & K_1 (B) & K'_0 (f) & rankGroup_0 (A) & rankGroup_0 (B) \ U(A) & U(B) & Pic(f) & Pic(A) & Pic(B)$,
    edge((0, 0), "r", "->"),
    edge((1, 0), "r", "->"),
    edge((2, 0), "r", "->"),
    edge((3, 0), "r", "->"),
    edge((0, 1), "r", "->"),
    edge((1, 1), "r", "->"),
    edge((2, 1), "r", "->"),
    edge((3, 1), "r", "->"),
    edge((0, 0), "d", $det_1 (A)$, "->"),
    edge((1, 0), "d", $det_1 (B)$, "->"),
    edge((2, 0), "d", $det_0 (f)$, "->"),
    edge((3, 0), "d", $det_0 (A)$, "->"),
    edge((4, 0), "d", $det_0 (B)$, "->"),
  )
}
