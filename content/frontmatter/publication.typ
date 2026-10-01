#import "../main-defs.typ": source
#import "@preview/cetz:0.3.4": canvas, draw
#let rotate-text = rotate

#let publisher-emblem() = canvas(length: 1mm, {
  import draw: *
  circle((0, 0), radius: (7.5, 9), stroke: 0.7pt)
  circle((0, 0), radius: (4.2, 6), stroke: 0.5pt)
  line(
    (0, 5.8),
    (0.8, 0.7),
    (4, 0),
    (0.8, -0.7),
    (0, -5.8),
    (-0.8, -0.7),
    (-4, 0),
    (-0.8, 0.7),
    close: true,
    stroke: 0.6pt,
  )
  line((0, 5.8), (0, -5.8), stroke: 0.45pt)
  line((-4, 0), (4, 0), stroke: 0.45pt)
  circle((0, 0), radius: (1.1, 1.4), stroke: 0.4pt)
  for (i, letter) in "ИЗДАТЕЛЬСТВО".clusters().enumerate() {
    let angle = 200deg - i * 20deg
    content((5.8 * calc.cos(angle), 7.3 * calc.sin(angle)), rotate-text(
      angle - 90deg,
      text(size: 5.5pt, letter),
    ))
  }
  content((0, -7.3), text(size: 6pt)[МИР])
  for x in (-5, 5) {
    for angle in (0deg, 45deg, 90deg, 135deg) {
      let dx = 0.3 * calc.cos(angle)
      let dy = 0.3 * calc.sin(angle)
      line((x - dx, -5 - dy), (x + dx, -5 + dy), stroke: 0.5pt)
    }
  }
})

#let publisher-page() = page(
  margin: 0pt,
  header: none,
  footer: none,
  numbering: "1",
)[
  #source(2)
  #place(top + center, dy: 60mm, publisher-emblem())
]

#let blank-page() = page(header: none, footer: none, numbering: "1")[]

#let publication-page() = page(header: none, footer: none, numbering: "1")[
  #source(5)
  УДК 512+513.836
  #v(33mm)
  В монографии известного американского математика Х. Басса — одного из
  создателей алгебраической $K$-теории — дано первое систематическое изложение
  этой теории.

  Материал изложен тщательно и подробно, с большим педагогическим мастерством.

  В вводной части приведены необходимые алгебраические сведения из теории колец,
  гомологической алгебры, теории общих линейных групп и теории категорий. Это
  делает книгу доступной студентам старших курсов и аспирантам университетов и
  пединститутов.

  Книга представляет интерес не только для алгебраистов, но и для математиков,
  специализирующихся по топологии, алгебраической геометрии, теории чисел и
  функциональному анализу.
  #place(bottom + left, dy: -24mm, align(center, block(
    width: 100%,
  )[_Редакция литературы по математическим наукам_]))
  #place(bottom + left, dy: -10mm, align(center, block(
    width: 100%,
  )[© Перевод на русский язык, «Мир», 1973]))
  #place(bottom + left, [Б $frac("0223—002", "041(01)—73")$])
]
