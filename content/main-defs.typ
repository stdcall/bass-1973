#import "numbering.typ": (
  axiom-display, axiom-name, condition-name, condition-number, formula-display,
  formula-numbering, numbered-record, place-key, record-number,
  statement-parameters,
)
#let source(n, printed: none) = context [#metadata((
  kind: "source",
  file-page: n,
  printed-page: if printed != none { str(printed) } else if n < 15 {
    str(n - 1)
  } else { str(n) },
  position: here().position(),
))]
#let number-text(body) = text(weight: "semibold", style: "normal", body)
#let roman(n) = numbering("I", n)
#let reference-printing(target, record, local) = {
  let number = if record != none { record-number(record) }
  let pending = number == none
  let prefix = str(target).split(":").first()
  let unnumbered = record != none and record.value.kind == "unnumbered"
  let suffix = if record != none {
    record.value.at("suffix", default: "")
  } else { "" }
  if pending { "?" } else if unnumbered {
    record.value.name
  } else if prefix == "ax" {
    axiom-name(record.value)
  } else if prefix == "ch" {
    roman(number.first())
  } else if prefix == "bib" {
    let n = str(number.last())
    let star = record.value.at("star", default: none)
    if star == "inside" { "[" + n + "*]" } else if star == "outside" {
      "[" + n + "]*"
    } else { "[" + n + "]" }
  } else if prefix in ("sec", "part") {
    str(number.last())
  } else if prefix == "eq" {
    formula-numbering(str(target), record.location()).printed
  } else if prefix == "cond" {
    condition-name(record.value.format, number.last())
  } else {
    let key = number.slice(1).map(str).join(".")
    if number.first() != local.first() {
      "(" + roman(number.first()) + ", " + key + ")" + suffix
    } else { "(" + key + ")" + suffix }
  }
}
#let reference-body(it) = context {
  let record = if it.element != none { numbered-record(it.target) }
  let number = if record != none { record-number(record) }
  let pending = number == none
  let prefix = str(it.target).split(":").first()
  let local = place-key(here())
  let unnumbered = record != none and record.value.kind == "unnumbered"
  let suffix = if record != none {
    record.value.at("suffix", default: "")
  } else { "" }
  let printed = reference-printing(it.target, record, local)
  let caption = it.supplement not in (auto, none, [])
  let numeric-body = if pending { number-text("?") } else if unnumbered {
    printed
  } else if prefix == "ax" {
    axiom-display(record.value, number: number-text(str(number.last())))
  } else if prefix == "ch" {
    number-text(roman(number.first()))
  } else if prefix == "bib" {
    let n = number-text(str(number.last()))
    let star = record.value.at("star", default: none)
    if star == "inside" { [\[#n\*\]] } else if star == "outside" {
      [\[#n\]\*]
    } else { [\[#n\]] }
  } else if prefix in ("sec", "part") {
    number-text(str(number.last()))
  } else if prefix == "eq" {
    show regex("[0-9]+"): it => number-text(it)
    formula-display(formula-numbering(str(it.target), record.location()))
  } else if prefix == "cond" {
    show regex("[0-9]+"): it => number-text(it)
    condition-number(record.value.format, number.last(), reference: true)
  } else {
    let key = number.slice(1).map(str).join(".")
    let base = if number.first() != local.first() {
      [(#number-text(roman(number.first())), #number-text(key))]
    } else { [(#number-text(key))] }
    let parameter = record.value.at("parameter", default: none)
    if parameter == none { [#base#suffix] } else {
      math.attach(base, b: statement-parameters.at(parameter).body)
    }
  }
  let body = if caption { it.supplement } else { numeric-body }
  let destination = if pending { none } else if (
    it.element.func() == math.equation
  ) {
    it.element.location()
  } else { record.location() }
  metadata((
    kind: "cross-reference",
    target: str(it.target),
    resolved: not pending,
    printed: printed,
    position: here().position(),
    target-position: if not pending { destination.position() },
  ))
  if pending { body } else { link(destination, body) }
}
#import "bibliography-tools.typ": citation-point
#let reference-rules(body) = {
  show cite: it => [#citation-point(str(it.key))#it]
  show ref: it => {
    let shown = reference-body(it)
    if str(it.target).starts-with("bib:") {
      citation-point(str(it.target).slice(4))
    }
    if it.supplement in (auto, none, []) { box(shown) } else { shown }
  }
  body
}
#let idx(..path) = [#metadata((
  kind: "index-mark",
  path: path.pos(),
))<index-mark>]
#let name-idx(name) = [#metadata((
  kind: "name-index-mark",
  path: (name,),
))<name-index-mark>]
#let symbol-idx(symbol, sort: none, group: "symbols", order: none) = [#metadata(
  (
    kind: "symbol-index-mark",
    symbol: symbol,
    sort: sort,
    group: group,
    order: order,
  ),
)<symbol-index-mark>]
#let editorial-notes = sys.inputs.at("editorial-notes", default: "on") != "off"
#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = if editorial-notes {
  editorial-note-counter.step()
  context {
    let mark = "*" + str(editorial-note-counter.get().first()) + ")"
    footnote(numbering: _ => mark)[#body~— _Прим. ред._]
    counter(footnote).update(n => n - 1)
  }
}
#let editorial-bibliography = [
  #show bibliography: none
  #bibliography("../editorial.bib", style: "chicago-notes")
]
#let group-name(name) = math.class("normal", math.upright(name))
#let GL = group-name("GL")
#let PGL = group-name("PGL")
#let SL = group-name("SL")
#let E = group-name("E")
#let GE = group-name("GE")
#let Aff = group-name("Aff")
#let U = group-name("U")
#let K = group-name("K")
#let G = group-name("G")
#let GFunctor = math.italic("G")
#let GroupCat = math.bold(math.italic("G"))
#let FiniteGroupCat = math.bold(math.italic("FG"))
#let Frob = math.bold(math.italic("Frob"))
#let Sp = math.italic("Sp")
#let FrobModules(g) = math.class(
  "normal",
  $#g#text("-")#math.bold(math.italic("mod"))$,
)
#let H = group-name("H")
#let Homology = math.italic("H")
#let HFunctor = math.italic("H")
#let Rk = math.op("Rk")
#let rank = math.op("rank")
#let card = math.op("card")
#let divisor = math.op("div")
#let res = math.op("res")
#let FP = math.bold(math.italic("FP"))
#let Hom = math.op("Hom")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let Gal = math.op("Gal")
#let Lcm = math.op("НОК")
#let Gcd = math.op("НОД")
#let pr = math.op("pr")
#let Nil = math.overline(math.op("Nil"))
#let NilGroup = group-name("Nil")
#let NilCat = math.bold(math.italic("Nil"))
#let lcm = math.op("н. о. к.")
#let abelClass = math.class("normal", math.upright("(abel)"))
#let cyclicClass = math.class("normal", math.upright("(cyclic)"))
#let elemClass = math.class("normal", math.upright("(elem)"))
#let hyperelemClass = math.class("normal", math.upright("(hypelem)"))
#let fieldElemClass(field) = math.class(
  "normal",
  $(#field#text("-")#math.upright("elem"))$,
)
#let Ker = math.op("Ker")
#let Coker = math.op("Coker")
#let Coim = math.op("Coim")
#let ker = math.op("ker")
#let coker = math.op("coker")
#let colim = math.op("colim")
#let Im = math.op("Im")
#let im = math.op("im")
#let ob = math.op("ob")
#let mor = math.op("mor")
#let Tor = math.op("Tor")
#let Ext = math.op("Ext")
#let Ex = math.op("Ex")
#let Pic = math.op("Pic")
#let det = math.op("det")
#let rk = math.op("rk")
#let mod = math.op("mod")
#let Supp = math.op("Supp")
#let supp = math.op("supp")
#let Spec = math.op("Spec")
#let Tr = math.op("Tr")
#let id = math.op("id")
#let Id = math.op("Id")
#let Center = math.op("center")
#let ann = math.op("ann")
#let InAut = math.op("In Aut")
#let alg = math.italic("alg")
#let PicCat = math.bold(math.italic("Pic"))
#let AzCat = math.bold(math.italic("Az"))
#let tensor = sym.times.o
#let rad = math.op("rad")
#let dim = math.op("dim")
#let spec = math.op("spec")
#let Res = math.bold(math.italic("Res"))
#let MC = math.italic("MC")
#let Pd = math.italic("Pd")
#let projLim = math.op("proj. lim")
#let Tran = math.bold(math.italic("Tran"))
#let maxSpec = math.op("max")
#let ht = math.op("ht")
#let codim = math.op("codim")
#let nil = math.op("nil")
#let deg = math.op("deg")
#let fRank = math.op("f-rank")
#let hd = math.op("hd")
#let Ht = math.op("Ht")
#let Frac = math.op("Frac")
#let Cart = math.op("Cart")
#let CartCat = math.bold(math.italic("Cart"))
#let Div = math.op("div")
#let rtGlDim = math.op("rt gl dim")
#let HCat = math.bold(math.italic("H"))
#let gr = math.op("gr")
#let aug = math.italic("aug")
#let semidirect = $limits(times)_(italic("s-d"))$
#let Trd = math.op("Trd")
#let Nrd = math.op("Nrd")
#let Nr = math.op("Nr")
#let diag = math.op("diag")
#let transpose(body, mark: $t$) = math.attach(body, tl: mark)
#let SR = group-name("SR")
#let SK = group-name("SK")
#let directLim(index) = $limits(op("lim"))_(#math.accent(index, sym.arrow.r))$
#let systemLimit(system) = math.class(
  "normal",
  math.attach(math.limits(system), b: sym.arrow.r),
)
#let mennicke(b, a) = math.vec(delim: "[", b, a)
#let center = math.op("center")
#let char = math.op("char")
#let Quad = math.bold(math.italic("Quad"))
#let ContMaps = math.op("Cont. maps")
#let mennickeRelation(q) = math.attach(math.scripts(sym.tilde), b: q)
#let leftSign(x, f) = math.attach(f, bl: x)
#let intervalSymbol(a, f, g, b) = math.attach($[#f, #g]$, bl: a, b: b)
#let NatTran = math.op("Nat. Tran.")
#let Seq = math.op("Seq")
#let moduleCategory = math.italic("mod")
#let moduleCategoryOf(ring, side: "right") = {
  assert(side in ("right", "left"))
  math.class("normal", if side == "left" {
    $#ring#text("-")#moduleCategory$
  } else { $#moduleCategory#text("-")#ring$ })
}
#let GrCat = math.bold(math.italic("gr"))
#let sequenceTail(object) = math.class(
  "normal",
  box(math.equation(math.display($#object -> 0$))),
)
#let isoArrow = math.class("relation", math.accent(sym.arrow.r, sym.tilde))
#let Nat = math.upright(math.bold($N$))
#let Int = math.upright(math.bold($Z$))
#let notation-list(..entries) = block({
  set par(spacing: 0.25em, first-line-indent: 0pt)
  entries.pos().join(parbreak())
})
#let signature(body) = align(right, body)
#let dedication-text = state("dedication", none)
#let dedication(body) = dedication-text.update(body)
