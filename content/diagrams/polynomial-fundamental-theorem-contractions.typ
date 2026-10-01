#import "commutative.typ": cd, edge
#import "../main-defs.typ": H, K, NilCat, NilGroup, U, det, rk

#let contraction-cycle-naturality() = cd(
  cell-size: (47mm, 23mm),
  $L_T F(A) & F(A[T]) \ L_S F(A) & F(A[S])$,
  edge((0, 0), "r", $h_(T,A)$, "->"),
  edge((0, 0), "d", $f$, "->"),
  edge((1, 0), "d", $f$, "->"),
  edge((0, 1), "r", $h_(S,A)$, "->", label-side: right),
)

#let contraction-chain() = cd(
  cell-size: (44mm, 20mm),
  $F(A) & F(A[T_+]) plus.o F(A[T_-]) & F(A[T]) & L_T F(A)$,
  edge((0, 0), "r", $e$, "->", shift: 2pt),
  edge((1, 0), "l", $c_2$, "->", shift: 2pt),
  edge((1, 0), "r", $tau$, "->", shift: 2pt),
  edge((2, 0), "l", $c_1$, "->", shift: 2pt),
  edge((2, 0), "r", $p$, "->", shift: 2pt),
  edge((3, 0), "l", $c_0$, "->", shift: 2pt),
)

#let contraction-morphism() = cd(
  cell-size: (54mm, 25mm),
  $L_T F(A) & F(A[T]) \ L_T F'(A) & F'(A[T])$,
  edge((0, 0), "r", $h_(T,A)$, "->"),
  edge((0, 0), "d", $L_T phi_A$, "->"),
  edge((1, 0), "d", $phi_(A[T])$, "->"),
  edge((0, 1), "r", $h'_(T,A)$, "->", label-side: right),
)

#let fundamental-localization() = cd(
  cell-size: (0pt, 28mm),
  spacing: (6mm, 0pt),
  $K_1 (A[T_+]) & K_1 (A[T]) & K_0 (NilCat (bold(P)(A))) & K_0 (A[T_+]) & K_0 (A[T]) \ & K_0 (A) plus.o N_(T_-) K_1 (A) & K_0 (A) plus.o NilGroup (A) & &$,
  edge((0, 0), "r", $tau_+$, "->"),
  edge((1, 0), "r", $delta_+$, "->"),
  edge((2, 0), "r", "->"),
  edge((3, 0), "r", $tau_+$, "->"),
  edge((1, 1), "u", $(h,tau_-)$, "->"),
  edge((2, 0), "d", $(approx)$, "->"),
  edge((1, 1), "r", $1 plus.o partial_-$, "->", label-side: right),
)

#let determinant-contraction() = cd(
  cell-size: (51mm, 25mm),
  $K_1 (A[T]) & U(A[T]) \ K_0 (A) & H_0 (A)$,
  edge((0, 0), "r", $det$, "->"),
  edge((0, 1), "u", $h$, "->", label-side: right),
  edge((1, 1), "u", $D h$, "->"),
  edge((0, 1), "r", $rk$, "->", label-side: right),
)

#let unit-contraction-section() = cd(
  cell-size: (52mm, 25mm),
  $L_T K_1 (A) & L_T U(A) \ K_1 (A[T]) & U(A[T])$,
  edge((1, 0), "l", $L_T g$, "->"),
  edge((0, 0), "d", $h$, "->"),
  edge((1, 0), "d", $h'$, "->"),
  edge((0, 1), "r", $det$, "->", label-side: right),
)
