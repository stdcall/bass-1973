#import "../main-defs.typ": source

#let english-title() = page(
  margin: 15mm,
  header: none,
  footer: none,
  numbering: "1",
)[
  #source(3)
  #set text(lang: "en", style: "italic", weight: "bold")
  #set par(first-line-indent: 0pt, justify: false)
  #align(center)[
    #text(size: 11pt)[MATHEMATICS LECTURE NOTE SERIES]
    #v(17mm)
    #text(size: 27pt)[Algebraic K-theory]
    #v(20mm)
    #text(size: 17pt)[HYMAN BASS]
    #linebreak()
    #text(size: 14pt)[Columbia University]
  ]
  #place(bottom + center, dy: -4mm, align(center)[
    #text(size: 14pt)[W. A. BENJAMIN, INC.]
    #v(2mm)
    #text(size: 13pt)[New York 1968 #h(5mm) Amsterdam]
  ])
]
