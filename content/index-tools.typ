// Указатели собираются по меткам у соответствующих мест текста.
#let index-page(body) = {
  set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  set text(size: 9pt)
  body
}
#let alphabetical(path) = {
  lower(path.join(" "))
    .replace("ё", "е")
    .replace(regex("\\s*\\([^)]*\\)"), "")
    .replace(regex("[,’'.]"), "")
}

#let locator(location) = box(context {
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    position: here().position(),
    target-position: location.position(),
  ))
  link(location, str(counter(page).at(location).first()))
})

#let collect(marks, key-of, fields-of) = {
  let entries = (:)
  for mark in marks {
    let key = key-of(mark.value)
    let entry = entries.at(key, default: (..fields-of(mark.value), at: ()))
    let number = counter(page).at(mark.location()).first()
    if entry.at.all(l => counter(page).at(l).first() != number) {
      entry.at.push(mark.location())
    }
    entries.insert(key, entry)
  }
  entries.values()
}

#let repeated-prefix(path, previous) = {
  let words = path.join(" ").split(" ")
  if previous == none { return words.join(" ") }
  let before = previous.join(" ").split(" ")
  let shared = true
  let printed = ()
  for (i, word) in words.enumerate() {
    if shared and i < before.len() and word == before.at(i) {
      printed.push("—")
    } else {
      shared = false
      printed.push(word)
    }
  }
  printed.join(" ")
}

#let text-index(kind, repeat: false) = context {
  let entries = collect(
    query(kind),
    v => v.path.join("\u{1f}"),
    v => (path: v.path),
  ).sorted(key: e => alphabetical(e.path))
  let previous = none
  let initial = none
  for entry in entries {
    let letter = upper(alphabetical(entry.path).first())
    if letter != initial {
      if initial != none { v(0.7em, weak: true) }
      initial = letter
      previous = none
    }
    let shown = if repeat { repeated-prefix(entry.path, previous) } else {
      entry.path.join(" ")
    }
    block(above: 0pt, below: 0.25em, par(hanging-indent: 1.2em)[
      #shown #entry.at.map(locator).join([, ])
    ])
    previous = entry.path
  }
}

#let symbol-groups = (
  ("categories", none),
  ("operators", none),
  ("letters", none),
  ("groups", none),
  ("symbols", none),
  ("superscripts", [Надстрочные знаки]),
  ("subscripts", [Подстрочные знаки]),
  ("delimiters", [Обозначения со скобками]),
)
#let symbol-index = context {
  let entries = collect(
    query(<symbol-index-mark>),
    v => (
      v.group + "\u{1f}" + if v.sort == none { repr(v.symbol) } else { v.sort }
    ),
    v => (symbol: v.symbol, group: v.group, order: v.order),
  ).sorted(key: e => if e.order == none { 10000 } else { e.order })
  for (group, title) in symbol-groups {
    let items = entries.filter(e => e.group == group)
    if items.len() == 0 { continue }
    if title != none {
      block(above: 0.7em, below: 0.4em, sticky: true, align(
        center,
        emph(title),
      ))
    }
    block(
      above: 0.5em,
      below: 0.5em,
      items
        .map(e => [
          #e.symbol #e.at.map(locator).join([, ])
        ])
        .join([; ]),
    )
  }
}
