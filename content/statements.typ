// Numbered items, statements, proofs, exercises and figures. Types and
// styles are set here, the counters in numbering.typ; chapter files only
// name the object and give its label, a stable semantic name:
// `#titled[Основные определения] <ss:main-definitions>`,
// `#proposition[…] <prop:interior-realization-bijective>`, `#exercise[…]
// <exc:triangulations-of-surfaces>`. No number is written in a chapter
// file: every number is counted (numbering.typ lists the schemes).
//
// Номера пунктов имеют вид (1.1) и общую серию внутри §.
// Тело теорем, лемм, предложений, следствий и определений — курсивное.
// Остальной текст и заголовки утверждений — прямые.
#import "numbering.typ": (
  axiom-display, condition-number, condition-variants, family-counter,
  formula-display, formula-numbering, formula-tags, formula-variants,
  named-axioms, number-string, numbered-record, object-number, place-key,
  record, record-number, statement-parameters, statement-variants,
)
#import "math-layout.typ": flow-equation

// Head of a numbered object: steps the family's counter, leaves the record
// and shows the object's own number with `format`.
#let counted(family, format, parameter: none) = {
  family-counter(family).step()
  context {
    record(family, parameter: parameter)
    let number = object-number(family, here())
    format(if family in ("bib", "eq", "fig", "exc") {
      str(number.last())
    } else { number-string(number) })
  }
}

// Number of a displayed formula with a label, `$ … $ <eq:gluing-relation>`;
// the show rule of book-style.typ calls this for every labelled display:
// "(1)" at the right margin, the number inside the section. A display
// listed in `formula-tags` (numbering.typ) is tagged with its symbol,
// "(∗)", one in `formula-variants` with the number of its base and a mark;
// neither is counted.
#let numbered-display(it) = {
  let name = str(it.label)
  let tag = formula-tags.at(name, default: none)
  let variant = formula-variants.at(name, default: none)
  if tag == none and variant == none { family-counter("eq").step() }
  context {
    let number = formula-numbering(name, here())
    record("eq", tag: number.tag, parameter: number.parameter)
    flow-equation(math.equation(
      block: true,
      // Upright also inside the italic text of a theorem.
      numbering: _ => text(
        font: "Libertinus Serif",
        style: "normal",
        formula-display(number),
      ),
      number-align: end + horizon,
      it.body,
    ))
  }
}

// Условие в формульной серии: номер и ссылка вычисляются по метке.
#let numbered-condition(body) = figure(
  body,
  kind: "numbered-condition",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let numbered-formula-item(body) = numbered-condition(emph(body))
#let render-numbered-condition(it) = {
  let name = str(it.label)
  if name not in formula-tags and name not in formula-variants {
    family-counter("eq").step()
  }
  context {
    let number = formula-numbering(name, here())
    record("eq", tag: number.tag, parameter: number.parameter)
    set par(first-line-indent: 0pt)
    grid(
      columns: (auto, 1fr),
      column-gutter: 1em,
      align: (left, left),
      text(style: "normal", formula-display(number)), it.body,
    )
  }
}

// Rebuilding a statement's first or last paragraph (to take a head or an
// ending) joins its pieces as `+` and `join` do, flattening nested sequences
// one level, but keeps a labelled sequence whole (an example
// closing a proof): `+` would merge
// it into its neighbours and lose its label. A rebuilt labelled object gets its
// label back.
#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => if it.func() == sequence and not it.has("label") {
      it.children
    } else { (it,) })
    .flatten(),
)
#let keep-label(original, rebuilt) = {
  if original.has("label") [#rebuilt#original.label] else { rebuilt }
}

// Put `head` at the start of the first paragraph of `body`.
#let prepend-heading(body, head) = {
  if body.func() == block {
    let fields = body.fields()
    let inner = fields.remove("body")
    block(prepend-heading(inner, head), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let first = children.position(it => (
      it.func()
        not in (
          [ ].func(),
          parbreak,
        )
    ))
    if first == none { join-pieces((head, body)) } else {
      keep-label(body, join-pieces((
        ..children.slice(0, first),
        prepend-heading(children.at(first), head),
        ..children.slice(first + 1),
      )))
    }
  } else { head + body }
}

// A word spaced out, as the book prints the names of statements and
// "Доказательство": `#spaced[Лемма]`.
#let spaced(word) = text(tracking: 0.22em, word)

// A statement is a run of ordinary paragraphs, not a block of its own: then
// Typst's paragraph indent works as in the book. The head opens an indented
// paragraph, as printed, also after a display, where Typst would not indent
// (`all: true` on the paragraphs before the first display); text that
// continues a sentence after a display stays flush left.
#let indent-first(body) = {
  let styled(it) = {
    set par(first-line-indent: (amount: 1.2em, all: true))
    it
  }
  let breaks(it) = (
    it.func() in (parbreak, block, grid, table, figure, list, enum, terms)
      or (it.func() == math.equation and it.block)
  )
  if body.func() == sequence and body.children.len() > 0 {
    let end = body.children.position(breaks)
    if end == none { styled(body) } else {
      join-pieces((
        styled(join-pieces(body.children.slice(0, end))),
        ..body.children.slice(end),
      ))
    }
  } else { styled(body) }
}
#let statement-block(body) = {
  parbreak()
  indent-first(body)
  parbreak()
}

// "■", the end of a proof, and of a statement printed without one: after
// the last word of the line, or of the display that ends it.
#let qed-mark = [#sym.wj#h(0.9em)#text(font: "Libertinus Serif")[■]]

// Put `ending` after the last word or formula of `body`.
#let append-ending(body, ending) = {
  if body.func() == math.equation and body.block {
    // As printed, the mark follows the display on its line.
    // A labelled display keeps its label (and so its number).
    let fields = body.fields()
    let inner = fields.remove("body")
    let name = fields.remove("label", default: none)
    let shown = math.equation(
      inner + h(0.9em) + ending.children.last(),
      ..fields,
    )
    if name == none { shown } else [#shown#name]
  } else if body.func() in (block, box) {
    let fields = body.fields()
    let inner = fields.remove("body")
    body.func()(append-ending(inner, ending), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let last = children
      .rev()
      .position(it => it.func() not in ([ ].func(), parbreak))
    if last == none { join-pieces((body, ending)) } else {
      let index = children.len() - last - 1
      keep-label(body, join-pieces((
        ..children.slice(0, index),
        append-ending(children.at(index), ending),
        ..children.slice(index + 1),
      )))
    }
  } else { body + ending }
}

// An item of a section with a title, "1. Основные определения.": number
// and title bold, in the line of the text that follows. It shares the
// series of items with the statements: `#titled[Скелет] <ss:skeleton> …`.
// A title that ends with its own sign, "Что делать?", takes no point.
#let titled(title) = {
  let text-of(it) = if it.has("text") { it.text } else if it.has("children") {
    it.children.map(text-of).join()
  } else if it.has("body") { text-of(it.body) } else { "" }
  let closed = text-of(title).trim().ends-with(regex("[?!.]"))
  counted("ss", n => [(#n) #title#if not closed [.]])
}

// Statements: "3. П р е д л о ж е н и е.", the number bold, then the body;
// `title` follows the word in parentheses, "7. Т е о р е м а (…).". `qed:
// true` ends a statement printed without a proof with "■". `word:`
// replaces the printed word ("Замечания и примеры", "План
// доказательства"); `upright: true` sets the body of a theorem-like
// statement upright, as the book does for some definitions.
#let statement(word, family, italic, title, qed, body) = {
  let head = counted(family, n => text(style: "normal")[(#n) #word#if (
      title != none
    ) [ (#title)].#[ ]])
  let body = if qed { append-ending(body, qed-mark) } else { body }
  let shown = statement-block(prepend-heading(body, head))
  // The letters of the parts, "а)", "б)", stay upright in italic text, as
  // printed.
  show regex("\b[а-яё]\)"): set text(style: "normal")
  if italic { text(style: "italic", shown) } else { shown }
}

// An environment printing `single` (`several` with `plural: true`) as the
// word of family `family`, its body italic if `italic`.
#let kind(single, family, italic, several: none) = (
  title: none,
  plural: false,
  qed: false,
  word: none,
  upright: false,
  body,
) => statement(
  if word != none { word } else if plural { several } else { single },
  family,
  italic and not upright,
  title,
  qed,
  body,
)

#let theorem = kind("Теорема", "th", true)
#let unnumbered-theorem(body, title: none) = {
  let head = [#metadata((kind: "unnumbered", family: "th", name: "Теорема"))
    <unnumbered>#text(style: "normal")[Теорема#if title != none [ (#title)]. ]]
  text(style: "italic", statement-block(prepend-heading(body, head)))
}
#let assertion(body, italic: true, parameter: none) = {
  let head = counted(
    "ss",
    n => {
      let base = text(style: "normal")[(#n)]
      let shown = if parameter == none { base } else {
        math.attach(base, b: statement-parameters.at(parameter).body)
      }
      [#shown ]
    },
    parameter: parameter,
  )
  text(
    style: if italic { "italic" } else { "normal" },
    statement-block(prepend-heading(body, head)),
  )
}
#let condition-counter = counter("condition")
#let condition-list(body, start: 1) = {
  assert(
    start >= 0,
    message: "Начальный номер условия должен быть неотрицательным",
  )
  condition-counter.update(start)
  body
}
#let condition-item(body, format: "(1)") = {
  condition-counter.step()
  context {
    [#metadata((
      kind: "numbered",
      family: "cond",
      number: (condition-counter.get().first() - 1,),
      format: format,
    ))<numbered>]
    text(style: "normal", condition-number(
      format,
      condition-counter.get().first() - 1,
    ))
    [ #body]
  }
}
#let lemma = kind("Лемма", "lem", true)
#let variant-condition(body) = figure(
  body,
  kind: "variant-condition",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let render-variant-condition(it) = context {
  let scheme = condition-variants.at(str(it.label))
  let base = numbered-record(label(scheme.first()))
  assert(base != none, message: "Не найдена база варианта условия")
  let number = record-number(base)
  [#metadata((
    kind: "numbered",
    family: "cond",
    derived: true,
    number: number,
    format: scheme.at(1),
  ))<numbered>]
  let head = text(style: "normal", condition-number(
    scheme.at(1),
    number.last(),
  ))
  align(start, statement-block(prepend-heading(it.body, [#head ])))
}
#let proposition = kind("Предложение", "prop", true)
#let hypothesis = kind("Предположение", "ss", true)
#let variant-proposition(body) = figure(
  body,
  kind: "variant-proposition",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let variant-definition(body) = figure(
  body,
  kind: "variant-definition",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let variant-corollary(body) = figure(
  body,
  kind: "variant-corollary",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let render-variant-statement(it, family, word) = context {
  let variant = statement-variants.at(str(it.label))
  let base = numbered-record(label(variant.first()))
  assert(base != none, message: "Не найдена база варианта утверждения")
  let number = record-number(base)
  [#metadata((
    kind: "numbered",
    family: family,
    derived: true,
    number: number,
    suffix: variant.at(1),
  ))<numbered>]
  let head = text(style: "normal")[(#number-string(number))#variant.at(1) #word.
  ]
  align(start, text(style: "italic", statement-block(prepend-heading(
    it.body,
    head,
  ))))
}
#let render-variant-proposition(it) = render-variant-statement(
  it,
  "prop",
  [Предложение],
)
#let render-variant-definition(it) = render-variant-statement(
  it,
  "def",
  [Определение],
)
#let render-variant-corollary(it) = render-variant-statement(
  it,
  "cor",
  [Следствие],
)
#let corollary = kind("Следствие", "cor", true)
#let definition = kind("Определение", "def", true)
// `plural: true` for "2. П р и м е р ы." heading several examples.
#let example = kind("Пример", "exm", false, several: "Примеры")
#let remark = kind("Замечание", "rem", false, several: "Замечания")

// A list labelled "(i)", "(ii)", … (other lists of the book are labelled
// "а)", "б)", …: book-style.typ).
#let conditions = enum.with(numbering: "(i)")

// `head` replaces "Доказательство.": `#proof(head: [#spaced[Доказательство]
// предложения @prop:….])`. A proof that the book numbers as an item of
// the section, "13. Д о к а з а т е л ь с т в о предложения 10.", is
// `#proof(numbered: true, head: […])[…] <ss:…>`: it takes the next number of
// the series and a label of an item.
#let proof(
  body,
  head: [Доказательство.],
  qed: false,
  numbered: false,
) = {
  let body = if qed { append-ending(body, qed-mark) } else { body }
  let head = if numbered {
    counted("ss", n => [#strong[#n.] #head])
  } else { head }
  statement-block(if head == none { body } else {
    prepend-heading(body, [#head ])
  })
}

// The exercises at the end of a section, in small type: `#exercises[
// #exercise[…] <exc:…> …]` prints the heading "ДОПОЛНЕНИЯ И УПРАЖНЕНИЯ" and
// the exercises. An exercise is an indented paragraph "1. …"; `title` is
// printed after the number.
#let exercises(title: [Дополнения и упражнения], body) = {
  block(above: 1.4em, below: 0.9em, sticky: true, par(
    first-line-indent: (amount: 1.2em, all: true),
    upper(title),
  ))
  text(size: 0.87em, body)
}
#let exercise(title: none, numbered: false, body) = {
  let head = if numbered {
    counted("exc", n => [#n. Упражнение.#if title != none [ #title.] ])
  } else {
    [#metadata((kind: "unnumbered", family: "exc", name: "Упражнение"))
      <unnumbered>Упражнение.#if title != none [ (#title).]
    ]
  }
  statement-block(prepend-heading(body, head))
}

// The book's figure: `#book-figure(drawing) <fig:triangulated-spaces>`
// floats to the top or bottom of a page like the printed one, is captioned
// "Рис. 1" (the figures are counted through the book) and is the target of
// `рис.~@fig:…`. The record sits inside the float, so a link leads to where
// the figure is actually placed.
#let book-figure(body) = {
  family-counter("fig").step()
  figure(
    [#record("fig")#body],
    caption: context [Рис. #object-number("fig", here()).last()],
    numbering: none,
    placement: auto,
    supplement: none,
  )
}

// The bibliography (80-references.typ), as printed: the collections, cited
// by their sigla, "[РП] Расслоенные пространства …", then the books and
// papers grouped under their authors and numbered inside each group, "Андре
// М. (André M.)" / "1. Categories of functors …". An entry is `#bib-item[…]
// <bib:Andre1966>` with the key of references.bib; `tag: "AAT"` gives a
// siglum instead of the number; `cite-as: "SGA"` keeps the number of an
// entry that the text cites by a siglum; `level: 1` is an entry printed
// under the one before (the volumes of [SGA]). The number is not written:
// it counts the entries of the author group (`#bib-author[…]` restarts it),
// and it is what `@bib:Andre1966` prints: "Андре [@bib:Andre1966]" gives
// "Андре [1]".
#let bib-author(name, start: 1) = {
  parbreak()
  if start != none { family-counter("bib").update(start - 1) }
  block(above: 0.55em, below: 0.3em, sticky: true, par(
    first-line-indent: 0pt,
    hanging-indent: 0pt,
    name,
  ))
  parbreak()
}
#let item-record(body) = {
  if body.func() == math.equation and body.block {
    family-counter("ss").step()
    context {
      record("ss")
      let number = number-string(object-number("ss", here()))
      flow-equation(math.equation(
        block: true,
        numbering: _ => text(
          font: "Libertinus Serif",
          style: "normal",
          [(#number)],
        ),
        number-align: left + horizon,
        body.body,
      ))
    }
  } else {
    block(grid(
      columns: (auto, 1fr),
      column-gutter: 1em,
      counted("ss", n => [(#n)]), align(center, body),
    ))
  }
}
#let category-axiom(family: "additive", title: none, body) = {
  assert(family in ("additive", "abelian"))
  let prefix = if family == "additive" { "Ад. кат. " } else { "Аб. кат. " }
  let c = counter("category-axiom:" + family)
  c.step()
  let head = context {
    let n = c.get().first() - 1
    [#metadata((
      kind: "numbered",
      family: "ax",
      number: (..place-key(here()), n),
      prefix: prefix,
    ))<numbered>]
    [#prefix#n.#if title != none [ #title.] ]
  }
  statement-block(prepend-heading(body, head))
}
#let named-axiom(body) = figure(
  body,
  kind: "named-axiom",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let named-axiom-group(..rows) = figure(
  math.cases(..rows.pos()),
  kind: "named-axiom-group",
  numbering: none,
  supplement: none,
  outlined: false,
)
#let render-named-axiom(it, grouped: false) = context {
  let scheme = named-axioms.at(str(it.label))
  let prefix = scheme.at(0)
  let n = scheme.at(1)
  let suffix = scheme.at(2)
  let format = scheme.at(3, default: "1")
  let value = (
    kind: "numbered",
    family: "ax",
    number: (..place-key(here()), n),
    prefix: prefix,
    suffix: suffix,
    format: format,
    parameter: scheme.at(4, default: none),
  )
  [#metadata(value)<numbered>]
  let name = text(style: "normal", axiom-display(value))
  if grouped {
    math.equation(block: true, [#name #it.body])
  } else {
    let head = [#name#if format not in ("cyrillic", "condition") [. ] else [ ]]
    align(start, statement-block(prepend-heading(it.body, head)))
  }
}
#let render-named-axiom-group(it) = render-named-axiom(it, grouped: true)
#import "bibliography-tools.typ": bibliography-context, bibliography-details
#let bib-item(
  tag: none,
  cite-as: none,
  star: none,
  level: 0,
  key: none,
  include-doi: true,
  body,
) = {
  if tag == none { family-counter("bib").step() }
  block(above: 0.3em, below: 0.3em, pad(left: level * 1.5em, par(
    first-line-indent: 0pt,
    hanging-indent: 1.5em,
    justify: true,
    context {
      let number-key = if tag != none { tag } else { cite-as }
      [#metadata((
        kind: "numbered",
        family: "bib",
        number: object-number("bib", here(), tag: number-key),
        tag: number-key,
        star: star,
      ))<numbered>]
      let n = family-counter("bib").get().first()
      if tag != none [[#tag]] else if star == "inside" { [\[#n\*\]] } else if (
        star == "outside"
      ) { [\[#n\]\*] } else [\[#n\]]
      [ ]
      // A full citation inside its own entry is not an occurrence in the text.
      metadata((kind: "bibliography-entry-start", key: key))
      bibliography-context.update(key)
      body
      bibliography-context.update(none)
      metadata((kind: "bibliography-entry-end", key: key))
      if key != none { bibliography-details(key, include-doi: include-doi) }
      metadata((kind: "bibliography-entry-finish", key: key))
    },
  )))
}
