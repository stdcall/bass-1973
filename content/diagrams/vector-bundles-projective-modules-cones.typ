#import "@preview/cetz:0.3.4": canvas, draw

#let mapping-cone-picture() = align(center, canvas(length: 8mm, {
  import draw: content, line
  let middle = ((3, 1.3), (3, 0.7), (3, 0), (3, -0.6), (3, -1.3))
  let ends = ((6.8, 0.7), (6.8, 0.45), (6.8, 0), (6.8, -0.7), (6.8, 0.45))
  for (i, point) in middle.enumerate() {
    line((0, 0), point, ends.at(i), stroke: 0.6pt)
  }
  line((3, 1.3), (3, -1.3), stroke: 0.6pt)
  line((6.8, 1.25), (6.8, -1.35), stroke: 0.6pt)
  content((0, 0.35), $Y times {0}$, anchor: "south-east")
  content((3, 1.45), $Y times {1 slash 2}$, anchor: "south")
  content((6.8, 1.4), $X$, anchor: "south")
}))

#let suspension-picture() = align(center, canvas(length: 8mm, {
  import draw: content, line
  for x in (-1.5, -1, -0.5, 0, 0.5, 1, 1.5) {
    line((0, 1.8), (x, 0), (0, -1.8), stroke: 0.6pt)
  }
  line((-1.5, 0), (1.5, 0), stroke: 0.6pt)
  content((0.2, 1.8), $X times {1}$, anchor: "west")
  content((1.7, 0), $X times {1 slash 2}$, anchor: "west")
  content((0.2, -1.8), $X times {0}$, anchor: "west")
}))
