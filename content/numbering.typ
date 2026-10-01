// Пункты одной общей серии внутри §: (1.1), (1.2), ... .
// Теоремы, леммы и описательные пункты используют один счётчик.
// Глава — I, II, ...; параграф — § 1, § 2, ... .
#let item-families = ("th", "lem", "prop", "cor", "def", "rem", "exm", "ss")
#let family-counter(family) = counter(
  "numbered:" + if family in item-families { "item" } else { family },
)
// The printed series in XII §8 starts with (8.0) and display (3).
#let series-offsets = ("12.8": (item: -1, eq: 2))
#let place-key(location) = {
  let n = counter(heading).at(location)
  (n.at(0, default: 0), n.at(1, default: 0))
}
#let restart-counters(level) = {
  if level <= 2 {
    for family in ("ss", "eq", "exc") {
      family-counter(family).update(0)
    }
    for family in ("additive", "abelian") {
      counter("category-axiom:" + family).update(0)
    }
  }
}
#let formula-tags = (
  "eq:morita-surjectivity-unit": "*",
  "eq:picard-stabilizer-sequence": "*",
  "eq:resolution-cone-sequence": "*",
  "eq:integral-polynomial-factor": "*",
  "eq:homological-dimension-multiplication-sequence": "*",
  "eq:divisorial-double-dual": "*",
  "eq:serre-preserved-congruences": "*",
  "eq:unimodular-adjustment-first-component": "*",
  "eq:unimodular-adjustment-localization-denominator": "**",
  "eq:linear-stability-reduced-character": "*",
  "eq:radical-unit-kernel-standard-form": "*",
  "eq:free-product-reduced-dependence": "*",
  "eq:seshadri-projective-splitting": "1",
  "eq:seshadri-twist-redistribution": "2",
  "eq:seshadri-saturation-splitting": "*",
  "eq:mennicke-square-transfer": "*",
  "eq:mennicke-denominator-multiplicativity": "**",
  "eq:mennicke-small-transvection-invariance": "*",
  "eq:curve-reciprocity-local-norm": "*",
  "eq:curve-reciprocity-uniformizer-polynomial": "**",
  "eq:arithmetic-finiteness-data": "0",
  "eq:arithmetic-base-data": "0′",
  "eq:arithmetic-center-data": "0″",
  "eq:arithmetic-cartan-k1-order-comparison": "*",
  "eq:automorphism-diagonal-factorization": "1",
  "eq:exchange-matrix-factorization": "2",
  "eq:roberts-generalized-eigenspace-decomposition": "1",
  "eq:roberts-inverse-map": "2",
  "eq:serre-subcategory-closure": "*",
  "eq:localization-euler-identity": "**",
  "eq:projective-localization-isomorphism-triangle": "Δ",
  "eq:dedekind-torsion-resolution-class": "*",
  "eq:dedekind-torsion-sk1-surjection": "**",
  "eq:finite-type-scheme-g-zero-localization": "*",
  "eq:mayer-vietoris-contracted-complexes": "*",
  "eq:mayer-vietoris-contracted-tail": "**",
  "eq:bundle-section-map-lift": "*",
  "eq:abelian-group-ring-arithmetic-data": "0",
)
#let formula-parameters = ("eq:homogeneous-koszul-complex": "n")
#let statement-variants = (
  "cor:modular-group-ring-cartan-injectivity": (
    "th:finite-group-cartan-injectivity",
    "",
  ),
  "def:relative-unimodular-transitivity": ("def:relative-stable-rank", "′"),
  "def:relative-linked-matrix-stability": ("def:relative-stable-rank", "″"),
  "prop:relative-linear-normal-subgroup-stability": (
    "th:linear-normal-subgroup-stability",
    "′",
  ),
)
#let condition-variants = (
  "cond:quasiregular-commutative-nil-k-zero-cokernel": (
    "cond:quasiregular-nil-k-zero-cokernel",
    "(1′)",
  ),
  "cond:invertible-module-endomorphisms": (
    "cond:invertible-module-projective-rank-one",
    "(1′)",
  ),
  "cond:nakayama-submodule-equality": (
    "cond:nakayama-quotient-vanishing",
    "(1′)",
  ),
  "cond:reciprocity-integral-product-conditions": (
    "cond:reciprocity-local-product-conditions",
    "cyrillic-prime",
  ),
)
#let named-axioms = (
  "ax:mennicke-invariance": ("MS", 1, ""),
  "ax:mennicke-upper-transvection": ("MS", 1, "a"),
  "ax:mennicke-lower-transvection": ("MS", 1, "b"),
  "ax:mennicke-multiplicativity": ("MS", 2, ""),
  "ax:mennicke-first-multiplicativity": ("MS", 2, "a"),
  "ax:mennicke-second-multiplicativity": ("MS", 2, "b"),
  "ax:mennicke-orbit-invariance": ("MS", 1, ""),
  "ax:mennicke-ideal-principal-normalization": ("M", 0, ""),
  "ax:mennicke-ideal-unit-denominator": ("M", 1, "(а)"),
  "ax:mennicke-ideal-denominator-translation": ("M", 1, "(б)"),
  "ax:mennicke-ideal-numerator-multiplicativity": ("M", 2, "(а)"),
  "ax:mennicke-ideal-denominator-multiplicativity": ("M", 2, "(б)"),
  "ax:reciprocity-vanishing-normalization": ("q-R", 0, ""),
  "ax:reciprocity-product-formula": ("q-R", 1, ""),
  "ax:reciprocity-exponent-normalization": ("q-R", 0, "′"),
  "ax:reciprocity-residue-characteristic-normalization": ("q-R", 0, "″"),
  "ax:reciprocity-local-steinberg": ("(", 0, ")", "condition"),
  "ax:reciprocity-disjoint-product": ("(", 1, ")", "condition"),
  "ax:reciprocity-characteristic-vanishing": ("(", 0, "′)", "condition"),
  "ax:reciprocity-integral-product": ("(", 1, "′)", "condition"),
  "ax:reciprocity-local-filtration": ("(", 0, ")", "condition", "p"),
  "ax:grothendieck-isomorphism": ("К", 1, "", "cyrillic"),
  "ax:grothendieck-product": ("К", 2, "", "cyrillic"),
  "ax:whitehead-isomorphism": ("К", 1, "", "cyrillic"),
  "ax:whitehead-product": ("К", 2, "", "cyrillic"),
  "ax:whitehead-composition": ("К", 3, "", "cyrillic"),
  "ax:abelian-k0-additivity": ("К", 0, ""),
  "ax:abelian-k1-composition": ("К", 1, ""),
  "ax:relative-exact-k0-additivity": ("К", 0, ""),
  "ax:relative-exact-k0-composition": ("К", 1, ""),
  "ax:roberts-exact-additivity": ("К", 0, ""),
  "ax:roberts-multiplicativity": ("К", 1, ""),
)
#let named-axiom-prefixes = ("q-R": [$frak(q)$-R])
#let named-axiom-parameters = (p: (printed: "ₚ", body: $frak(p)$))
#let axiom-prefix(value) = named-axiom-prefixes.at(
  value.prefix,
  default: value.prefix,
)
#let formula-variants = (
  "eq:resolution-finite-kernel-closure": ("eq:resolution-kernel-closure", "′"),
  "eq:projective-line-h-square-zero": (
    "eq:projective-line-h-second-difference",
    "′",
  ),
)
#let statement-parameters = (n: (printed: "ₙ", body: $n$))
#let number-string(number) = number.slice(1).map(str).join(".")
#let condition-letter(n) = {
  let letters = "абвгдежзиклмнопрстуфхцчшщыэюя".clusters()
  assert(
    n > 0 and n <= letters.len(),
    message: "Число буквенных условий вне диапазона",
  )
  letters.at(n - 1)
}
#let axiom-name(value) = {
  let n = value.number.last()
  let base = (
    value.prefix
      + if value.at("format", default: "1") == "cyrillic" {
        condition-letter(n) + ")"
      } else { str(n) + value.at("suffix", default: "") }
  )
  let parameter = value.at("parameter", default: none)
  (
    base
      + if parameter == none { "" } else {
        named-axiom-parameters.at(parameter).printed
      }
  )
}
#let axiom-display(value, number: none) = {
  let body = if value.at("format", default: "1") == "cyrillic" {
    axiom-name(value)
  } else {
    let n = if number == none { str(value.number.last()) } else { number }
    [#axiom-prefix(value)#n#value.at("suffix", default: "")]
  }
  let parameter = value.at("parameter", default: none)
  if parameter == none { body } else {
    math.attach(body, b: named-axiom-parameters.at(parameter).body)
  }
}
#let condition-name(format, n) = {
  if format == "step" { str(n) } else if format == "degree" {
    str(n) + "°"
  } else if format == "cyrillic" {
    "(" + condition-letter(n) + ")"
  } else if format == "cyrillic-prime" {
    "(" + condition-letter(n) + "′)"
  } else if (
    format in ("cyrillic-n", "cyrillic-prime-n")
  ) {
    (
      "("
        + condition-letter(n)
        + if format == "cyrillic-prime-n" { "′ₙ)" } else { "ₙ)" }
    )
  } else { numbering(format, n) }
}
#let condition-number(format, n, reference: false) = {
  if format == "step" {
    if reference { str(n) } else { "Шаг " + str(n) + "." }
  } else if format in ("cyrillic-n", "cyrillic-prime-n") {
    let letter = text(condition-letter(n))
    let subscript = math.italic("n")
    let superscript = if format == "cyrillic-prime-n" { sym.prime }
    [(#math.attach(letter, b: subscript, t: superscript))]
  } else { condition-name(format, n) }
}
#let object-number(family, location, tag: none) = {
  if family == "bib" { return (family-counter("bib").at(location).first(),) }
  let own = if tag != none { tag } else {
    let key = place-key(location).map(str).join(".")
    let series = if family in item-families { "item" } else { family }
    (
      family-counter(family).at(location).first()
        + series-offsets.at(key, default: (:)).at(series, default: 0)
    )
  }
  (..place-key(location), own)
}
#let record(family, tag: none, parameter: none) = context [#metadata((
  kind: "numbered",
  family: family,
  number: object-number(family, here(), tag: tag),
  tag: tag,
  parameter: parameter,
  suffix: if parameter == none { "" } else {
    statement-parameters.at(parameter).printed
  },
))<numbered>]
#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  query(selector(<numbered>).or(<unnumbered>).within(target)).at(
    0,
    default: none,
  )
}
#let record-number(record) = {
  let value = record.value
  if value.kind == "unnumbered" { return (value.name,) }
  if value.family == "ax" { return value.number }
  if value.family == "part" { return value.number }
  if value.family == "cond" { return value.number }
  if value.at("derived", default: false) { return value.number }
  if value.family == "heading" {
    return place-key(record.location()).slice(0, value.level)
  }
  object-number(value.family, record.location(), tag: value.at(
    "tag",
    default: none,
  ))
}
#let formula-numbering(name, location) = {
  let tag = formula-tags.at(name, default: none)
  let variant = formula-variants.at(name, default: none)
  let outside = (
    variant != none and variant.at(2, default: "inside") == "outside"
  )
  let own = if variant == none {
    if tag == none { str(object-number("eq", location).last()) } else { tag }
  } else {
    let found = numbered-record(label(variant.first()))
    if found == none { "?" } else { str(record-number(found).last()) }
  }
  let mark = if variant == none { "" } else { variant.at(1) }
  let base = if outside { "(" + own + ")" + mark } else {
    "(" + own + mark + ")"
  }
  let parameter = formula-parameters.at(name, default: none)
  (
    tag: if tag != none { tag } else if variant != none { own + mark },
    base: base,
    parameter: parameter,
    printed: base
      + if parameter == none { "" } else {
        statement-parameters.at(parameter).printed
      },
  )
}
#let formula-display(number) = if number.parameter == none {
  number.base
} else {
  math.attach(number.base, b: statement-parameters.at(number.parameter).body)
}
