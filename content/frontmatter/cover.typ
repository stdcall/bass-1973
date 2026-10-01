#import "../main-defs.typ": source

#let cover() = page(
  margin: 0pt,
  header: none,
  footer: none,
  numbering: none,
  fill: rgb("92928f"),
)[
  #source(1)
  #place(top + left, dx: 86mm, dy: 69mm, text(
    size: 22pt,
    weight: "bold",
    style: "italic",
    fill: white,
  )[Х. БАСС])
  #place(top + left, dx: 82mm, dy: 84mm, text(
    size: 100pt,
    style: "italic",
    fill: rgb("c2c2bc"),
  )[K])
  #place(top + left, dx: 7mm, dy: 105mm, text(
    size: 14pt,
    style: "italic",
    fill: rgb("d0d0c9"),
  )[АЛГЕБРАИЧЕСКАЯ])
  #place(top + left, dx: 104.5mm, dy: 105mm, text(
    size: 14pt,
    style: "italic",
    fill: rgb("d0d0c9"),
  )[-ТЕОРИЯ])
]
