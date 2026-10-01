"""Verify actual PDF link rectangles and destinations against Typst references.

Every resolved cross-reference of the book (`@pr:…`, `@eq:…`, `@bib:…`, ...)
records its own position and its target's in metadata. For this project's
unrotated, full-page Typst export, Typst puts the destination 10pt above its
target. Validate positions, not just page existence.
"""
import hashlib
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

from pypdf import PdfReader
from pypdf.generic import NameObject, TextStringObject


def pt(value):
    assert value.endswith('pt'), value
    return float(value[:-2])


def annotation_owners(reader):
    """Find each annotation's native tagged PDF Link element.

    Typst puts every glyph and wrapped line of one logical link in the
    same Link structure element. ParentTree and OBJR must agree; an extra
    overlapping annotation with a copied parent key is invalid.
    """
    tree = reader.trailer['/Root']['/StructTreeRoot']
    parents = {}

    def walk(node):
        node = node.get_object()
        nums = node.get('/Nums', [])
        assert len(nums) % 2 == 0, 'Malformed PDF ParentTree'
        for key, value in zip(nums[::2], nums[1::2]):
            assert int(key) not in parents, 'Duplicate PDF parent key'
            parents[int(key)] = value
        for child in node.get('/Kids', []):
            walk(child)

    walk(tree['/ParentTree'])
    owners, memberships, destinations = {}, {}, {}
    for page in reader.pages:
        for ref in page.get('/Annots', []):
            annotation = ref.get_object()
            if annotation.get('/Subtype') != '/Link':
                continue
            key = annotation.get('/StructParent')
            assert key is not None and int(key) in parents, \
                'Link annotation has no native tagged owner'
            owner_ref = parents[int(key)]
            owner = owner_ref.get_object()
            assert owner.get('/Type') == '/StructElem' \
                and owner.get('/S') == '/Link', 'Annotation parent is not Link'
            owner_id = (owner_ref.idnum, owner_ref.generation)
            if owner_id not in memberships:
                kids = owner.get('/K', [])
                if not isinstance(kids, list):
                    kids = [kids]
                objects = []
                for kid in kids:
                    kid = kid.get_object() if hasattr(kid, 'get_object') else kid
                    if isinstance(kid, dict) and kid.get('/Type') == '/OBJR':
                        obj = kid.raw_get('/Obj')
                        objects.append((obj.idnum, obj.generation))
                assert len(objects) == len(set(objects)), 'Duplicate link OBJR'
                memberships[owner_id] = set(objects)
            identity = (ref.idnum, ref.generation)
            assert identity in memberships[owner_id], \
                'ParentTree and link annotation OBJR disagree'
            owners[identity] = owner_id
            action = annotation.get('/A', {}).get_object() \
                if '/A' in annotation else {}
            if action.get('/S') == '/URI':
                destination = ('/URI', str(action['/URI']))
            else:
                assert not action or action.get('/S') == '/GoTo', \
                    'Unexpected link action'
                dest = annotation.get('/Dest', action.get('/D'))
                dest = dest.get_object() if hasattr(dest, 'get_object') else dest
                if isinstance(dest, str):
                    dest = reader.named_destinations[dest].dest_array
                assert isinstance(dest, list) and len(dest) == 5, \
                    'Malformed internal link destination'
                destination = ('/GoTo', dest[0].idnum, dest[0].generation,
                               *(str(value) for value in dest[1:]))
            previous = destinations.setdefault(owner_id, destination)
            assert destination == previous, \
                f'Logical PDF link {owner_id}: contradictory fragment destinations'
    return owners


def joined_fragments(records):
    """Join touching PDF glyph rectangles of the same native reference.

    A math reference exports a rectangle per glyph (sometimes nested).
    Its metadata marks the top of the complete math box, which can be
    above the first glyph's box, as for the lowercase q in q-R0.
    """
    by_target = {}
    identity = ('from_page', 'to_page', 'target_top_origin', 'target_left',
                'type', 'description')
    for record in records:
        key = tuple(record[k] for k in identity) + (
            tuple(record.get('link_owner', ())),)
        groups = by_target.setdefault(key, [])
        current = {**record, 'annotation_fragments': 1}
        while True:
            found = None
            a = current['rect_top_origin']
            for i, group in enumerate(groups):
                b = group['rect_top_origin']
                if (a[0] <= b[2]+0.03 and b[0] <= a[2]+0.03 and
                        a[1] <= b[3]+0.03 and b[1] <= a[3]+0.03):
                    found = i
                    break
            if found is None:
                break
            group = groups.pop(found)
            b = group['rect_top_origin']
            current['rect_top_origin'] = [min(a[0], b[0]), min(a[1], b[1]),
                                          max(a[2], b[2]), max(a[3], b[3])]
            current['annotation_fragments'] += group['annotation_fragments']
        groups.append(current)
    return [group for groups in by_target.values() for group in groups]


def set_link_descriptions(document, references):
    """Coordinate links need the printed page label, not a physical-page
    tooltip. Only references that carry a `description` are touched."""
    for ref in references:
        if not ref.get('description'):
            continue
        source = ref['position']
        page = document.pages[source['page'] - 1]
        height = float(page.mediabox.height)
        matches = []
        for item in page.get('/Annots', []):
            annotation = item.get_object()
            if annotation.get('/Subtype') != '/Link':
                continue
            rect = [float(v) for v in annotation['/Rect']]
            if (abs(rect[0] - pt(source['x'])) < 0.03 and
                    height - rect[3] - 0.03 <= pt(source['y'])
                    <= height - rect[1] + 0.03):
                matches.append(annotation)
        assert len(matches) == 1, 'Expected one link for its description'
        matches[0][NameObject('/Contents')] = TextStringObject(
            ref['description'])


def check_links(pdf, references):
    reader = PdfReader(pdf)
    owners = annotation_owners(reader)
    page_ids = {p.indirect_reference.idnum: i+1
                for i, p in enumerate(reader.pages)}
    records = []
    for number, page in enumerate(reader.pages, 1):
        assert page.get('/Rotate', 0) == 0
        assert list(page.cropbox) == list(page.mediabox)
        assert list(page.mediabox)[:2] == [0, 0]
        height = float(page.mediabox.height)
        for ref in page.get('/Annots', []):
            annotation = ref.get_object()
            if annotation.get('/Subtype') != '/Link':
                continue
            action = annotation.get('/A', {}).get_object() \
                if '/A' in annotation else {}
            if action.get('/S') == '/URI':
                continue
            assert not action or action.get('/S') == '/GoTo', \
                'Unexpected link action'
            dest = annotation.get('/Dest', action.get('/D'))
            if hasattr(dest, 'get_object'):
                dest = dest.get_object()
            if isinstance(dest, str):
                dest = reader.named_destinations[dest].dest_array
            assert len(dest) == 5 and dest[1] == '/XYZ', dest
            target_page = page_ids[dest[0].idnum]
            target_height = float(reader.pages[target_page-1].mediabox.height)
            assert 0 <= float(dest[3]) <= target_height
            rect = [float(v) for v in annotation['/Rect']]
            assert 0 <= rect[0] < rect[2] <= float(page.mediabox.width)
            assert 0 <= rect[1] < rect[3] <= height
            records.append({
                'from_page': number, 'to_page': target_page,
                'rect_top_origin': [rect[0], height-rect[3], rect[2],
                                    height-rect[1]],
                'target_top_origin': target_height-float(dest[3]),
                'target_left': float(dest[2]),
                'type': '/XYZ',
                'description': str(annotation.get('/Contents', '')),
                'link_owner': owners[(ref.idnum, ref.generation)]})
    by_owner = {}
    for record in records:
        by_owner.setdefault(tuple(record['link_owner']), []).append(record)
    for owner, owned in by_owner.items():
        destinations = {(r['to_page'], r['target_top_origin'],
                         r['target_left'], r['type'], r['description'])
                        for r in owned}
        assert len(destinations) == 1, \
            f'Logical PDF link {owner}: contradictory fragment destinations'
    fragments = joined_fragments(records)
    checked = []
    absent = []
    for ref in references:
        target = ref.get('target')
        if not ref['resolved']:
            absent.append(target)
            continue
        source = ref['position']
        destination = ref['target-position']
        matching = [r for r in fragments if r['from_page'] == source['page']
                    and r['rect_top_origin'][0]-0.03 <= pt(source['x'])
                    <= r['rect_top_origin'][2]+0.03
                    and r['rect_top_origin'][1]-0.03 <= pt(source['y'])
                    <= r['rect_top_origin'][3]+0.03]
        # Adjacent lines can have overlapping annotation rectangles. Their
        # actual destinations distinguish the two links at a shared edge.
        expected_top = max(0, pt(destination['y'])-10)
        expected_left = pt(ref.get('target-left', destination['x']))
        if len(matching) > 1:
            matching = [r for r in matching
                        if r['to_page'] == destination['page'] and
                        abs(r['target_top_origin']-expected_top) < 0.03 and
                        abs(r['target_left']-expected_left) < 0.03]
        assert matching, (f'{target}: expected a clickable rectangle '
                          f'at {source}; got {matching}')
        # Every glyph and wrapped tail of this tagged link was checked
        # above. A representative rectangle locates its semantic record.
        actual = min(matching, key=lambda r: abs(
            r['rect_top_origin'][1]-pt(source['y'])))
        assert actual['to_page'] == destination['page'], \
            f'{target}: wrong target page'
        assert abs(actual['target_top_origin']-expected_top) < 0.03, \
            f'{target}: wrong target height'
        assert abs(actual['target_left']-expected_left) < 0.03, \
            f'{target}: wrong target horizontal position'
        if ref.get('description'):
            assert actual['description'] == ref['description'], \
                f'{target}: wrong accessible page description'
        checked.append({'target': target, **actual,
                        'annotation_fragments': len(by_owner[
                            tuple(actual['link_owner'])])})
    return {'sha256': hashlib.sha256(Path(pdf).read_bytes()).hexdigest(),
            'status': 'passed', 'internal_link_annotations': len(records),
            'semantic_references_checked': len(checked),
            'bibliography_references_checked': sum(
                r['target'].startswith('bib:') for r in checked),
            'references': checked,
            'unresolved_targets': sorted(set(absent)),
            'links': records,
            'viewer_click_test': 'not performed; actual PDF objects checked'}


def link_at(records, position):
    """The link rectangles that start at a recorded position."""
    return [r for r in records if r['from_page'] == position['page']
            and abs(r['rect_top_origin'][0] - pt(position['x'])) < 0.03
            and r['rect_top_origin'][1] - 0.03 <= pt(position['y'])
            <= r['rect_top_origin'][3] + 0.03]


def check_bibliography_links(pdf, document, links, root):
    """Check the pages of citations and the actual clickable backlinks.

    Page lists are derived from the evaluated citations, including footnotes,
    rather than a manually maintained list. A full citation within its own
    bibliography entry is excluded by the entry's local show rule.
    """
    keys = []
    for name in ('80-bibliography.typ', '81-additional-bibliography.typ',
                 '82-editorial-bibliography.typ'):
        keys.extend(re.findall(r'<bib:([^>]+)>',
                               (root / 'content' / name).read_text()))
    assert len(keys) == len(set(keys)), 'Duplicate bibliography keys'
    citations, entries, backlinks, boundaries = {}, {}, {}, {}
    for item in document['metadata']:
        value = item['value']
        if not isinstance(value, dict):
            continue
        key = value.get('key')
        if item.get('label') == '<citation-point>':
            assert key in keys, f'Citation has no printed entry: {key}'
            citations.setdefault(key, []).append(item)
        elif value.get('kind') == 'bibliography-entry':
            assert key not in entries, f'Duplicate printed entry: {key}'
            entries[key] = item
        elif value.get('kind') == 'bibliography-backlink':
            backlinks.setdefault(key, []).append(item)
        elif value.get('kind') in ('bibliography-entry-start',
                                   'bibliography-entry-end',
                                   'bibliography-entry-finish'):
            boundaries.setdefault(key, {})[value['kind']] = item['position']
    assert set(entries) == set(keys), 'Missing bibliography entry metadata'
    assert set(backlinks) <= set(keys), 'Backlink has no printed entry'
    reader = PdfReader(pdf)
    records = links['links']
    checked, uncited, doi_checked = 0, [], 0
    doi_fields, additional_dois = {}, {}
    for name in ('references.bib', 'editorial.bib'):
        for key, fields in re.findall(r'@[A-Za-z]+\{([^,]+),(.*?)\n\}',
                                      (root / name).read_text(), re.S):
            match = re.search(r'\bdoi\s*=\s*\{([^}]+)\}', fields)
            if match:
                doi_fields[key.strip()] = match[1].strip()
            addendum = re.search(r'\baddendum\s*=\s*\{([^}]+)\}', fields)
            if addendum:
                additional_dois[key.strip()] = re.findall(
                    r'https://doi\.org/([^\s}]+)', addendum[1])
    doi_links = []
    for number, page in enumerate(reader.pages, 1):
        for reference in page.get('/Annots', []):
            annotation = reference.get_object()
            action = annotation.get('/A', {}).get_object() \
                if '/A' in annotation else {}
            if action.get('/S') != '/URI':
                continue
            uri = urlsplit(str(action['/URI']))
            if uri.hostname != 'doi.org':
                continue
            rect = [float(value) for value in annotation['/Rect']]
            height = float(page.mediabox.height)
            doi_links.append((unquote(uri.path.lstrip('/')).casefold(),
                              {'page': number, 'x': f'{rect[0]}pt',
                               'y': f'{height-rect[3]}pt'},
                              {'page': number, 'x': f'{rect[2]}pt',
                               'y': f'{height-rect[1]}pt'}))
    def reading_order(position):
        return (position['page'], pt(position['y']), pt(position['x']))
    for key in keys:
        span = boundaries[key]
        doi = doi_fields.get(key)
        assert entries[key]['value']['doi'] == doi, \
            f'{key}: printed DOI metadata differs from BibLaTeX'
        extra = additional_dois.get(key, [])
        assert entries[key]['value'].get('additional-dois', []) == extra, \
            f'{key}: additional DOI metadata differs from BibLaTeX'
        for expected_doi in ([doi] if doi else []) + extra:
            assert any(expected_doi.casefold() == actual and
                       reading_order(bottom) >=
                       reading_order(span['bibliography-entry-start']) and
                       reading_order(top) <=
                       reading_order(span['bibliography-entry-finish'])
                       for actual, top, bottom in doi_links), \
                f'{key}: no clickable DOI in the printed entry'
            doi_checked += 1
        mentions = sorted(citations.get(key, []), key=lambda item: (
            item['position']['page'], pt(item['position']['y']),
            pt(item['position']['x'])))
        expected = {}
        for mention in mentions:
            assert not (reading_order(span['bibliography-entry-start']) <=
                        reading_order(mention['position']) <=
                        reading_order(span['bibliography-entry-end'])), \
                f'{key}: the entry counts its own citation'
            expected.setdefault(str(mention['page-label']), mention)
        assert [str(p) for p in entries[key]['value']['pages']] == \
            list(expected), f'{key}: wrong pages of mentions'
        actual = backlinks.get(key, [])
        assert len(actual) == len(expected), f'{key}: missing/duplicate pages'
        assert [item['value']['page-label'] for item in actual] == \
            list(expected), f'{key}: wrong backlink order'
        if not expected:
            uncited.append(key)
        for backlink in actual:
            value = backlink['value']
            target = expected[value['page-label']]['position']
            assert value['target-position'] == target, \
                f'{key}: backlink does not target the first mention'
            found = link_at(records, backlink['position'])
            assert len(found) == 1, f'{key}: expected one clickable backlink'
            annotation = found[0]
            assert annotation['to_page'] == target['page'], \
                f'{key}: wrong physical page'
            assert reader.page_labels[target['page'] - 1] == \
                value['page-label'], f'{key}: wrong printed page label'
            assert abs(annotation['target_left']) < 0.03, \
                f'{key}: wrong horizontal destination'
            assert abs(annotation['target_top_origin'] -
                       max(0, pt(target['y']) - 12)) < 0.03, \
                f'{key}: wrong vertical destination'
            checked += 1
    return {'entries': len(keys), 'backlinks_checked': checked,
            'doi_links_checked': doi_checked,
            'entries_without_mentions': uncited,
            'viewer_click_test': 'not performed; actual PDF objects checked'}


def check_hint_links(links, hint_links):
    """A problem and its hint (the book's solution) lead to each other.

    `hint_links` are the records the book leaves (statements.typ,
    `hint-link`): the head of every problem, "Problem 3.", and every number
    of a hint, "3." or each of "1, 2.". The head of a problem with a hint
    must be a link to the hint, every number of a hint a link back to the
    head of its problem, both to the recorded place; the head of a problem
    without a hint must be no link. `links` is the report of `check_links`.
    """
    records = links['links']
    counts = {'problems_with_hint': 0, 'problems_without_hint': 0,
              'hint_numbers': 0}
    failures = []
    for item in hint_links:
        name = (item['from'] + ' '
                + '.'.join(str(n) for n in item['number']))
        found = link_at(records, item['position'])
        target = item.get('target-position')
        if target is None:
            if found:
                failures.append(f'{name}: a problem without a hint is a link')
            counts['problems_without_hint'] += 1
            continue
        if len(found) != 1:
            failures.append(f'{name}: expected one link at {item["position"]}'
                            f', got {len(found)}')
            continue
        actual = found[0]
        expected_top = max(0, pt(target['y']) - 10)
        if actual['to_page'] != target['page'] \
                or abs(actual['target_top_origin'] - expected_top) >= 0.03:
            failures.append(f'{name}: leads to page {actual["to_page"]}, not '
                            f'to the place on page {target["page"]}')
            continue
        counts['problems_with_hint' if item['from'] == 'problem'
               else 'hint_numbers'] += 1
    assert not failures, failures[:12]
    # Every problem that a hint names has its head linked to that hint.
    named = {tuple(i['number']) for i in hint_links if i['from'] == 'hint'}
    linked = {tuple(i['number']) for i in hint_links
              if i['from'] == 'problem' and i.get('target-position')}
    assert named <= linked, sorted(named - linked)[:12]
    return counts
