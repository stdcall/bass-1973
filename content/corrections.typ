#import "main-defs.typ" as book-defs
#show: book-defs.reference-rules
#let book-scope = dictionary(book-defs)
#let entries = json("../corrections.json").entries
#let markup(field) = eval(field, mode: "markup", scope: book-scope)

#set document(
  title: "Х. Басс. Алгебраическая К-теория. Исправления",
  author: "Х. Басс",
  date: none,
)
#set page(
  width: 145mm,
  height: 225mm,
  margin: (x: 15mm, top: 17mm, bottom: 17mm),
  footer: context align(center, text(size: 10pt, counter(page).display())),
)
#set text(font: "Libertinus Serif", size: 10.5pt, lang: "ru")
#set par(justify: true, leading: 0.62em, spacing: 0.8em)
#show math.equation: set text(
  font: "STIX Two Math",
  top-edge: "bounds",
  bottom-edge: "bounds",
)
#show math.equation: it => {
  show ":": math.class("punctuation", ":")
  show "≥": sym.gt.eq.slant
  show "≤": sym.lt.eq.slant
  it
}

#align(center, text(size: 16pt)[Исправления])

Х.~Басс, _Алгебраическая К-теория_, «Мир», Москва, 1973. Номера страниц ниже
относятся к этому печатному изданию.

#show heading: set text(size: 12pt)
#show heading: set block(above: 1.6em, below: 0.8em)

#if entries.len() == 0 [
  Исправлений нет.
] else {
  let section = none
  for entry in entries {
    if entry.section != section {
      section = entry.section
      heading(level: 1, markup(section))
    }
    block(breakable: false, above: 1em)[
      #metadata((correction: entry.id))
      *#entry.id* · с.~#entry.printed_page#if entry.place != entry.section [,
        #markup(entry.place)]

      Напечатано: #markup(entry.original)

      Исправлено: #markup(entry.corrected)

      #if entry.reason == entry.verified_by {
        text(size: 10pt)[Обоснование и проверка: #markup(entry.reason)]
      } else [
        #text(size: 10pt, markup(entry.reason))

        #text(size: 10pt)[Проверка: #markup(entry.verified_by)]
      ]
    ]
  }
}
