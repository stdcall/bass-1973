#import "@preview/cetz:0.3.4": canvas, decorations, draw

#let chapter-graph = (
  vertices: (
    (target: <ch:category-algebra>, position: (0, 0)),
    (target: <ch:module-categories>, position: (1, -1)),
    (target: <ch:rings-modules>, position: (2, -2)),
    (target: <ch:stable-projective-structure>, position: (3, -3)),
    (target: <ch:stable-linear-groups>, position: (4, -4)),
    (target: <ch:mennicke-symbols>, position: (5, -5)),
    (target: <ch:exact-k-sequences>, position: (0, -6)),
    (target: <ch:abelian-k-theory>, position: (2, -7)),
    (target: <ch:projective-k-theory>, position: (4, -8)),
    (target: <ch:arithmetic-finiteness>, position: (2, -9.5)),
    (target: <ch:finite-group-induction>, position: (0, -11)),
    (target: <ch:polynomial-extensions>, position: (4, -12.2)),
    (target: <ch:reciprocity-finiteness>, position: (5, -13.2)),
    (target: <ch:vector-bundles-projective-modules>, position: (4, -15)),
  ),
  edges: (
    (3, 4),
    (4, 5),
    (4, 8),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
    (8, 11),
    (11, 12),
    (5, 12),
  ),
)

#let dependency-diagram() = align(center, canvas(length: 6mm, {
  import draw: *
  let position(i) = {
    let (x, y) = chapter-graph.vertices.at(i).position
    (x * 1.3, y)
  }
  for (a, b) in chapter-graph.edges {
    line(position(a), position(b), stroke: 0.6pt)
  }
  for (i, vertex) in chapter-graph.vertices.enumerate() {
    content(position(i), box(fill: white, inset: 1.5pt, ref(
      vertex.target,
      supplement: none,
    )))
  }
  let groups = (
    (
      start: (-0.5, 0.4),
      end: (-0.5, -2.6),
      body: [Часть @part:preliminaries],
      flip: true,
    ),
    (
      start: (7.1, -2.6),
      end: (7.1, -5.5),
      body: [Часть @part:stable-structure],
      flip: false,
    ),
    (
      start: (-0.5, -5.6),
      end: (-0.5, -7.4),
      body: [Часть @part:algebraic-k-theory],
      flip: true,
    ),
    (
      start: (7.2, -7.5),
      end: (7.2, -13.6),
      body: [Часть @part:computations],
      flip: false,
    ),
    (start: (7.2, -14.3), end: (7.2, -15.7), body: [Приложение], flip: false),
  )
  for group in groups {
    decorations.brace(
      group.start,
      group.end,
      flip: group.flip,
      amplitude: 0.2,
      stroke: 0.55pt,
    )
    let (x, top) = group.start
    let bottom = group.end.at(1)
    content(
      (x + if group.flip { -0.4 } else { 0.4 }, (top + bottom) / 2),
      anchor: if group.flip { "east" } else { "west" },
      text(size: 9pt, style: "italic", group.body),
    )
  }
}))
