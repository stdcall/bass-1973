#import "../main-defs.typ": source

#let cover() = page(
  margin: 0pt,
  header: none,
  footer: none,
  numbering: none,
  fill: rgb("92928f"),
)[
  #source(1)
  #let title-baseline = 108.2mm
  #place(top + left, dx: 86mm, dy: 69mm, text(
    size: 22pt,
    weight: "bold",
    style: "italic",
    fill: white,
  )[Х. БАСС])
  #place(top + left, dx: 82mm, dy: title-baseline, text(
    size: 100pt,
    style: "italic",
    top-edge: "baseline",
    fill: rgb("c2c2bc"),
  )[K])
  #place(top + left, dx: 7mm, dy: title-baseline, text(
    size: 14pt,
    style: "italic",
    top-edge: "baseline",
    fill: rgb("d0d0c9"),
  )[АЛГЕБРАИЧЕСКАЯ])
  #place(top + left, dx: 104.5mm, dy: title-baseline, text(
    size: 14pt,
    style: "italic",
    top-edge: "baseline",
    fill: rgb("d0d0c9"),
  )[-ТЕОРИЯ])
]
