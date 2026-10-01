// Commutative diagrams of the book, drawn by fletcher (the Typst analogue of
// tikz-cd). A diagram is the grid of its objects, written as in tikz-cd, `&`
// between the columns and `\` between the rows, and the list of its arrows:
// an arrow starts at the cell (column, row) of its object and goes in the
// direction of its target ("r", "d", "dr", "uu", …), and fletcher attaches it
// to the borders of the two objects. A label stands on the `label-side` of the
// direction of travel; fletcher's default puts it above a horizontal arrow.
// Rational maps are dotted arrows, `"..>"`. `shift` separates two opposite
// arrows between the same objects; `shift: (0pt, d)` moves only the end of an
// arrow along the border of its target, where it would meet the head of
// another arrow. An object off the grid (a fractional column or row) is a
// `node` call, and its arrows go between coordinates.
//
//   $
//     #cd(
//       cell-size: (32mm, 24mm),
//       $G times G & G \ G times G\/H & G\/H$,
//       edge((0, 0), "r", $mu$, "->"),
//       edge((0, 0), "d", $id times p$, "->", label-side: right),
//       edge((1, 0), "d", $p$, "->", label-side: left),
//       edge((0, 1), "r", $lambda$, "->"),
//     )
//   $
//
// The grid stays on one line: Typstyle would rewrite a grid of several lines
// inside a display. `cd` is fletcher's `diagram` in the style of the book: a
// diagram gives its `cell-size`, the distance between the centres of
// neighbouring objects, as (column, row). The margin of an object and of a
// label is measured from the bottom of its descenders, as in the book's
// drawings. Set as a stack, the diagram has no baseline, so that a display
// centres it on the math axis and its formula number beside its middle, as
// tikz-cd does.
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let fit-diagram(body) = layout(size => {
  let natural = measure(body)
  if natural.width > size.width {
    scale((size.width / natural.width) * 100%, reflow: true, body)
  } else { body }
})

#let cd(..args) = {
  set text(bottom-edge: "bounds")
  fit-diagram(stack(diagram(
    spacing: 0pt,
    node-shape: rect,
    node-inset: 1.2mm,
    edge-stroke: 0.5pt,
    label-size: 0.8em,
    label-sep: 0.25em,
    ..args,
  )))
}
