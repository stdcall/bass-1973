// The original publication data and back cover use separate unnumbered pages.
#let colophon(..sections) = page(header: none, footer: none)[
  #set text(size: 9pt)
  #set par(first-line-indent: 0pt, justify: false, spacing: 1em)
  #align(center)[
    #v(1fr)
    #sections.pos().map(section => block(section)).join(v(1em))
    #v(1fr)
  ]
]

#let back-cover(price) = page(header: none, footer: none)[
  #place(top + left, price)
]
