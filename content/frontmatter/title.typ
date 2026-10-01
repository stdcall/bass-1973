#import "../main-defs.typ": source

#let title-page() = page(
  margin: 13mm,
  header: none,
  footer: none,
  numbering: "1",
)[
  #source(4)
  #set text(style: "italic", weight: "bold")
  #set par(first-line-indent: 0pt, justify: false)
  #align(center)[
    #text(size: 23pt)[Х. БАСС]
    #v(10mm)
    #text(size: 21pt)[АЛГЕБРАИЧЕСКАЯ]
    #v(2mm)
    #text(size: 31pt)[К-ТЕОРИЯ]
    #v(6mm)
    #text(size: 13pt)[Перевод с английского]
    #linebreak()
    #text(size: 14pt)[А. В. МИХАЛЁВА]
    #v(4mm)
    #text(size: 13pt)[Под редакцией]
    #linebreak()
    #text(size: 14pt)[Е. С. ГОЛОДА]
  ]
  #place(bottom + center, align(center)[
    #text(size: 14pt)[ИЗДАТЕЛЬСТВО «МИР»]
    #linebreak()
    #text(size: 12pt)[МОСКВА 1973]
  ])
]
