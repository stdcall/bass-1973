#import "numbering.typ": numbered-record, place-key, restart-counters
#import "math-layout.typ": flow-equation
#import "statements.typ": (
  numbered-display, render-named-axiom, render-named-axiom-group,
  render-numbered-condition, render-variant-condition, render-variant-corollary,
  render-variant-definition, render-variant-proposition,
)
#import "main-defs.typ": (
  dedication-text, reference-printing, reference-rules, roman,
)
#let part-counter = counter("part")
#let part-pending = state("part-pending", false)
#let part(title) = {
  part-counter.step()
  heading(level: 1, numbering: none, supplement: [Часть], title)
}
#let appendix(title) = heading(
  level: 1,
  numbering: none,
  supplement: [Приложение],
  title,
)
#let plain-text(body) = {
  if body.has("text") { body.text } else if body.has("children") {
    body.children.map(plain-text).join()
  } else if body.has("body") { plain-text(body.body) } else { "" }
}
#let part-title(it) = {
  if it.supplement == [Приложение] { it.body } else {
    [Часть #part-counter.at(it.location()).first(). #it.body]
  }
}
#let running-chapter = state("running-chapter", none)
#let running-section = state("running-section", none)
#let body-top-margin = 17mm
#let pending-heading-note = state("heading-note", none)
#let heading-note(body) = pending-heading-note.update(body)
#let heading-anchor(it) = {
  restart-counters(it.level)
  [#metadata((kind: "numbered", family: "heading", level: it.level))<numbered>]
}
#let unnumbered-heading-anchor(it) = [#metadata((
  kind: "unnumbered",
  name: plain-text(it.body),
))<unnumbered>]
#let heading-number(it) = counter(heading).at(it.location())
#let section-title(it) = [§ #heading-number(it).at(1). #it.body]
#let opening-page() = {
  query(heading.where(level: 1)).any(it => (
    it.location().page() == here().page()
  ))
}
#let header-content(node, local) = {
  if node.func() == ref {
    let caption = node.fields().at("supplement", default: auto)
    if caption not in (auto, none, []) { upper(caption) } else {
      text(reference-printing(node.target, numbered-record(node.target), local))
    }
  } else if node.func() == math.equation { node } else if node.has("text") {
    upper(node)
  } else if node.has("children") {
    node.children.map(child => header-content(child, local)).join()
  } else if node.func() == math.class {
    math.class(node.class, header-content(node.body, local))
  } else if node.has("body") {
    let fields = node.fields()
    let inner = fields.remove("body")
    node.func()(header-content(inner, local), ..fields)
  } else { node }
}
#let running-header = context {
  if not opening-page() {
    let folio = counter(page).display()
    let chapter = running-chapter.get()
    let section = running-section.get()
    let opening-sections = query(heading.where(level: 2)).filter(it => (
      it.numbering != none
        and it.location().page() == here().page()
        and it.location().position().y <= body-top-margin + 1pt
    ))
    if opening-sections.len() > 0 {
      section = section-title(opening-sections.first())
    }
    let name = if calc.even(counter(page).get().first()) { chapter } else {
      if section != none { section } else { chapter }
    }
    if name != none {
      let body = header-content(name, place-key(here()))
      text(size: 9pt, grid(
        columns: (2em, 1fr, 2em),
        column-gutter: 0.5em,
        if calc.even(counter(page).get().first()) { folio } else { [] },
        align(center, layout(size => {
          let natural = measure(body)
          if natural.width > size.width {
            scale((size.width / natural.width) * 100%, reflow: true, body)
          } else { body }
        })),
        if calc.odd(counter(page).get().first()) { folio } else { [] },
      ))
    }
  }
}
#let book-style(body) = {
  set page(
    width: 145mm,
    height: 225mm,
    margin: (x: 14mm, top: body-top-margin, bottom: 16mm),
    numbering: "1",
    header: counter(footnote).update(0) + running-header,
    footer: context if opening-page() {
      align(center, counter(page).display())
    },
  )
  set text(
    font: "Libertinus Serif",
    size: 10.5pt,
    lang: "ru",
    fill: rgb("202020"),
  )
  set par(
    justify: true,
    leading: 0.62em,
    spacing: 0.62em,
    first-line-indent: (amount: 1.2em, all: true),
  )
  show link: set text(fill: rgb("202020"))
  show regex("^-\\p{L}"): it => sym.wj + it
  set heading(numbering: (..n) => {
    let n = n.pos()
    if n.len() == 1 { "Глава " + roman(n.first()) + "." } else {
      "§ " + str(n.at(1)) + "."
    }
  })
  show heading.where(level: 1): it => {
    let is-part = it.supplement in ([Часть], [Приложение])
    if is-part {
      pagebreak(weak: true)
      part-pending.update(true)
      context {
        if it.supplement == [Часть] {
          [#metadata((
            kind: "numbered",
            family: "part",
            number: (part-counter.at(it.location()).first(),),
          ))<numbered>]
        } else { unnumbered-heading-anchor(it) }
        metadata((
          kind: "major-division",
          title: plain-text(it.body),
          printed-title: if it.supplement == [Часть] {
            (
              "Часть "
                + str(part-counter.at(it.location()).first())
                + ". "
                + plain-text(it.body)
            )
          } else { plain-text(it.body) },
          position: it.location().position(),
        ))
      }
      block(width: 100%, above: 5mm, below: 7mm, align(center, text(
        size: 13pt,
        context upper(part-title(it)),
      )))
    } else {
      context if not part-pending.get() { pagebreak(weak: true) }
      part-pending.update(false)
      context {
        let dedication = dedication-text.get()
        if dedication != none {
          align(right, emph(dedication))
          dedication-text.update(none)
        }
      }
      if it.numbering != none { heading-anchor(it) } else {
        unnumbered-heading-anchor(it)
      }
      let title = if it.numbering != none {
        [Глава #roman(heading-number(it).first()). #it.body]
      } else { it.body }
      running-chapter.update(title)
      running-section.update(none)
      set par(first-line-indent: 0pt, justify: false)
      block(width: 100%, above: 5mm, below: 8mm, align(center, {
        if it.numbering != none {
          text(size: 12pt)[Глава #roman(heading-number(it).first())]
          linebreak()
        }
        text(size: 13pt, upper(it.body))
        context {
          let note = pending-heading-note.get()
          if note != none {
            footnote(note)
            pending-heading-note.update(none)
          }
        }
      }))
    }
  }
  show heading.where(level: 2): it => {
    if it.numbering != none {
      heading-anchor(it)
      running-section.update(section-title(it))
    } else { unnumbered-heading-anchor(it) }
    set par(first-line-indent: 0pt, justify: false)
    block(width: 100%, above: 4mm, below: 3mm, sticky: true, align(center, text(
      size: 11pt,
      if it.numbering == none { it.body } else { section-title(it) },
    )))
  }
  show outline: set par(first-line-indent: 0pt)
  show outline.entry: set block(breakable: false)
  show outline.entry.where(level: 1): set block(above: 0.8em)
  set outline(indent: 1.4em)
  show outline.entry: it => context {
    let is-part = it.element.supplement in ([Часть], [Приложение])
    let previous = query(
      heading
        .where(level: 1)
        .before(
          it.element.location(),
        ),
    ).at(-1, default: none)
    let nested = (
      not is-part
        and (
          it.element.numbering != none
            or (
              it.level == 2 and previous != none and previous.numbering != none
            )
        )
    )
    let entry = outline.entry(it.level + if nested { 1 } else { 0 }, it.element)
    let prefix = if is-part and it.element.supplement == [Часть] {
      [Часть #part-counter.at(it.element.location()).first().]
    } else { it.prefix() }
    link(it.element.location(), entry.indented(prefix, it.inner()))
  }
  set math.equation(numbering: none, supplement: none)
  show figure.where(kind: "numbered-condition"): render-numbered-condition
  show figure.where(kind: "variant-proposition"): render-variant-proposition
  show figure.where(kind: "variant-definition"): render-variant-definition
  show figure.where(kind: "variant-corollary"): render-variant-corollary
  show figure.where(kind: "variant-condition"): render-variant-condition
  show figure.where(kind: "named-axiom"): render-named-axiom
  show figure.where(kind: "named-axiom-group"): render-named-axiom-group
  show math.equation: set text(
    font: "STIX Two Math",
    top-edge: "bounds",
    bottom-edge: "bounds",
  )
  show math.equation: it => {
    show ":": math.class("punctuation", ":")
    show "≥": sym.gt.eq.slant
    show "≤": sym.lt.eq.slant
    it
  }
  show math.mat: math.display
  set math.cases(gap: 0.6em)
  show math.equation.where(block: true): it => {
    if it.has("label") and str(it.label).starts-with("eq:") {
      numbered-display(it)
    } else { flow-equation(it) }
  }
  set table(stroke: 0.5pt, inset: (x: 0.4em, y: 0.4em), align: horizon)
  set table.cell(breakable: false)
  show table: set par(justify: false, first-line-indent: 0pt)
  show: reference-rules
  set footnote(numbering: n => str(n) + ")")
  body
}
