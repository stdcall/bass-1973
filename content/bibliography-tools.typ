// Bibliographic data remain in BibLaTeX. DOI fields and addenda are read here;
// the original prose and numbering of each entry are preserved.
#let bibliography-context = state("book-bibliography-entry", none)
#let citation-point(key) = context {
  if bibliography-context.get() != key {
    [#metadata((key: key))<citation-point>]
  }
}
#let bibliography-dois = {
  let result = (:)
  let data = read("../references.bib") + "\n" + read("../editorial.bib")
  for entry in data.matches(regex("(?s)@[A-Za-z]+\\{([^,]+),(.*?)\n\\}")) {
    let doi = entry.captures.at(1).match(regex("doi\\s*=\\s*\\{([^}]+)\\}"))
    if doi != none {
      result.insert(entry.captures.first().trim(), doi.captures.first().trim())
    }
  }
  result
}
#let bibliography-addendum-dois = {
  let result = (:)
  let data = read("../references.bib") + "\n" + read("../editorial.bib")
  for entry in data.matches(regex("(?s)@[A-Za-z]+\\{([^,]+),(.*?)\n\\}")) {
    let addendum = entry
      .captures
      .at(1)
      .match(
        regex(
          "addendum\\s*=\\s*\\{([^}]+)\\}",
        ),
      )
    if addendum != none {
      let dois = addendum
        .captures
        .first()
        .matches(regex("https://doi\\.org/([^\\s}]+)"))
        .map(it => it.captures.first())
      result.insert(entry.captures.first().trim(), dois)
    }
  }
  result
}
#let bibliography-details(key, include-doi: true) = context {
  let references = query(<citation-point>)
    .filter(it => it.value.key == key)
    .sorted(key: it => {
      let pos = it.location().position()
      (pos.page, pos.y, pos.x)
    })
  let pages = ()
  let links = ()
  for reference in references {
    let loc = reference.location()
    let page = counter(page).at(loc).first()
    if page not in pages {
      pages.push(page)
      let position = loc.position()
      let destination = (
        page: position.page,
        x: 0pt,
        y: calc.max(0pt, position.y - 12pt),
      )
      // Typst applies a 10pt offset to explicit PDF positions.
      let exported = (..destination, y: destination.y + 10pt)
      links.push(link(exported, box[
        #metadata((
          kind: "bibliography-backlink",
          key: key,
          page-label: str(page),
          target-position: position,
          destination: destination,
          link-input: exported,
        ))#str(page)
      ]))
    }
  }
  let doi = bibliography-dois.at(key, default: none)
  let additional-dois = bibliography-addendum-dois.at(key, default: ())
  metadata((
    kind: "bibliography-entry",
    key: key,
    pages: pages,
    doi: doi,
    additional-dois: additional-dois,
  ))
  if include-doi and doi != none {
    [ DOI: #link("https://doi.org/" + doi, doi).]
  }
  for extra in additional-dois {
    [ DOI дополнения: #link("https://doi.org/" + extra, extra).]
  }
  if links.len() > 0 {
    text(size: 0.82em)[ Упоминается на с. #links.join(", ").]
  } else {
    text(size: 0.82em)[ Упоминания: —.]
  }
}
