// Long displays use the native paragraph breaking of inline mathematics.
// The formula remains in display style; short displays keep their native form.
#let flow-equation(it) = layout(size => {
  let inline = math.equation(block: false, math.display(it.body))
  let reserved = if it.numbering == none { 0pt } else {
    (
      measure(text(font: "Libertinus Serif", style: "normal", numbering(
        it.numbering,
        1,
      ))).width
        + 1em.to-absolute()
    )
  }
  let width = size.width - reserved
  if measure(inline).width <= width { it } else {
    let fields = it.fields()
    let _ = fields.remove("body")
    let name = fields.remove("label", default: none)
    let body = block(width: width, align(center, {
      set text(top-edge: "bounds", bottom-edge: "bounds")
      par(first-line-indent: 0pt, justify: false, inline)
    }))
    let shown = math.equation(body, ..fields)
    if name == none { shown } else [#shown#name]
  }
})
