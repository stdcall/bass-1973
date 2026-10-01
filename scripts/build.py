"""Build the book, its no-notes edition and the corrections sheet, and check
every PDF before it replaces the previous one.

Bookmarks keep the reader's zoom: each outline destination is rewritten to
`[page /XYZ left top null]`. `left = null` would keep the horizontal
position as well, but MuPDF-based viewers drop the vertical target when left
is null (checked with PyMuPDF 1.27.2.3: `/XYZ null 300 null` resolves to no
point, `/XYZ 0 300 null` to the heading), so the left edge comes from
`pdf_navigation.outline_left` in config/project.json, 0. Zoom stays null:
the view keeps its scale.

Page labels are Typst's own: the cover is outside the count, the following
leaves carry Arabic labels from 1, including leaves with a hidden folio.
They are validated, not rewritten.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

import fitz
from pypdf import PdfReader, PdfWriter
from pypdf.generic import (ArrayObject, FloatObject, NameObject, NullObject,
                           NumberObject, TextStringObject)
from check_links import (check_bibliography_links, check_hint_links, check_links,
                         set_link_descriptions)
from check_whitespace import check_whitespace
from lint_typst import (lint, input_hashes, evaluate, tool_versions,
                        unresolved_references, write_unresolved, from_roman)
from project import settings, stage, tool_env, cache_path, typst_inputs
from check_fonts import book_font_names, check_fonts

ROOT = Path(__file__).resolve().parents[1]


def run(args):
    result = subprocess.run(args, cwd=ROOT, env=tool_env(ROOT),
                            capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{args[0]} failed:\n{result.stdout}\n'
                           f'{result.stderr}')
    if re.search(r'^warning: .*font', result.stderr, re.MULTILINE):
        raise RuntimeError(f'{args[0]} font warning:\n{result.stderr}')
    return result


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def accessibility_signature(reader):
    """Compare the tagged structure and embedded fonts across finalization."""
    from pypdf.generic import IndirectObject, StreamObject, BooleanObject
    seen = {}
    page_ids = {p.indirect_reference.idnum: i
                for i, p in enumerate(reader.pages)}
    embedded = set()
    structures = set()

    def canonical(value):
        if isinstance(value, IndirectObject):
            key = (value.idnum, value.generation)
            if value.idnum in page_ids:
                return ['page', page_ids[value.idnum]]
            if key in seen:
                return ['ref', seen[key]]
            seen[key] = len(seen)
            return ['object', seen[key], canonical(value.get_object())]
        if isinstance(value, dict):
            if value.get('/Type') == '/StructElem':
                structures.add(value.indirect_reference.idnum)
            for key in ['/FontFile', '/FontFile2', '/FontFile3']:
                if key in value:
                    embedded.add(hashlib.sha256(
                        value[key].get_data()).hexdigest())
            result = {str(k): canonical(v) for k, v in sorted(value.items())
                      if k not in ('/Length', '/Filter', '/DecodeParms')}
            if isinstance(value, StreamObject):
                result['decoded_stream_sha256'] = hashlib.sha256(
                    value.get_data()).hexdigest()
            return result
        if isinstance(value, (list, tuple)):
            return [canonical(v) for v in value]
        if isinstance(value, NullObject):
            return None
        if isinstance(value, BooleanObject):
            return value.value
        if isinstance(value, bytes):
            return value.hex()
        if isinstance(value, (int, float)):
            return float(value)
        return str(value)

    catalog = reader.trailer['/Root']
    assert '/StructTreeRoot' in catalog, 'PDF accessibility tags missing'
    tags = {key: catalog.raw_get(key) for key in
            ['/StructTreeRoot', '/MarkInfo', '/Lang'] if key in catalog}
    fonts = [page['/Resources'].get('/Font') for page in reader.pages]
    data = canonical([tags, fonts])
    assert embedded, 'No embedded fonts'
    return {'sha256': hashlib.sha256(
                json.dumps(data, sort_keys=True).encode()).hexdigest(),
            'structure_elements': len(structures),
            'embedded_font_programs': len(embedded),
            'font_program_sha256': sorted(embedded)}


def math_equations(value):
    """Return the native mathematical nodes; never render them as text."""
    if isinstance(value, dict):
        if value.get('func') == 'equation':
            yield value
        else:
            for child in value.values():
                yield from math_equations(child)
    elif isinstance(value, list):
        for child in value:
            yield from math_equations(child)


def splice_outline_math(title, equations, fragments):
    """Apply explicit, reviewed alternate text only to unchanged math ASTs."""
    changes, ordinals = [], set()
    for fragment in sorted(fragments, key=lambda f: -len(f['native_fragment'])):
        ordinal = fragment['equation_ordinal']
        assert type(ordinal) is int and 0 <= ordinal < len(equations), \
            'Invalid math equation ordinal'
        assert ordinal not in ordinals, 'Duplicate math alternate'
        ordinals.add(ordinal)
        actual = hashlib.sha256(json.dumps(equations[ordinal], sort_keys=True,
                                          ensure_ascii=False).encode()).hexdigest()
        assert actual == fragment['ast_sha256'], 'Changed heading math AST'
        token = fragment['native_fragment']
        assert token and fragment['alternate']
        candidates = [(m.start(), m.end()) for m in re.finditer(re.escape(token), title)
                      if not any(m.start() < end and m.end() > start
                                 for start, end, _ in changes)]
        assert len(candidates) == 1, ('Missing or ambiguous native math fragment', token)
        start, end = candidates[0]
        changes.append((start, end, fragment['alternate']))
    for start, end, alternate in sorted(changes, reverse=True):
        title = title[:start]+alternate+title[end:]
    return title


def native_outline_titles(writer, divisions, headings, references, math_alternates=(),
                          raw_pdf=None):
    """Preserve native titles, adding only evaluated reference/part strings.

    Typst omits custom references from bookmark titles and its plain-text
    metadata can lose spaces before mathematics. Match native destinations
    to evaluated heading positions instead of rebuilding mathematical titles
    or duplicating the book's counters in Python.
    """
    if not divisions or '/Outlines' not in writer.root_object:
        assert not headings, 'Heading title adaptation needs division anchors'
        return divisions, [], []

    def pt(value):
        return float(str(value).removesuffix('pt'))

    def normal(value):
        return re.sub(r'\s+', ' ', value).strip()

    pages = {}
    for n, page in enumerate(writer.pages, 1):
        assert page.get('/Rotate', 0) == 0 and list(page.mediabox)[:2] == [0, 0]
        pages[(page.indirect_reference.idnum, page.indirect_reference.generation)] = (
            n, float(page.mediabox.height))

    def walk(ref):
        while ref:
            node = ref.get_object()
            dest = node['/A'].get_object()['/D'] if '/A' in node else node['/Dest']
            assert isinstance(dest, list) and dest[1] == '/XYZ'
            page, height = pages[(dest[0].idnum, dest[0].generation)]
            yield node, {'page': page, 'x': float(dest[2]),
                         'y': height-float(dest[3])}
            if node.get('/First'):
                yield from walk(node['/First'])
            ref = node.get('/Next')

    nodes = list(walk(writer.root_object['/Outlines'].get('/First')))
    known = []
    for division in divisions:
        matches = [point for node, point in nodes
                   if normal(str(node['/Title'])) == normal(division['title'])
                   and point['page'] == division['position']['page']]
        if len(matches) == 1:
            known.append(pt(division['position']['y'])-matches[0]['y'])
    assert known, 'No unambiguous native division destination'
    padding = sorted(known)[len(known)//2]
    assert max(abs(value-padding) for value in known) < .03

    def at_heading(point, position):
        return (point['page'] == position['page']
                and abs(point['x']-pt(position['x'])) < .03
                and abs(point['y']+padding-pt(position['y'])) < .03)

    def contains_ref(value):
        if isinstance(value, dict):
            return value.get('func') == 'ref' or any(
                contains_ref(child) for child in value.values())
        return isinstance(value, list) and any(contains_ref(child) for child in value)

    repairs = []
    for heading in headings:
        body = heading['body']
        if not contains_ref(body):
            continue
        assert body.get('func') == 'sequence', 'Unsupported reference heading body'
        prefix, specs = '', []
        for child in body['children']:
            if child.get('func') == 'ref':
                specs.append((prefix, child['target'].strip('<>')))
            elif not specs:
                assert child.get('func') in ('space', 'text'), \
                    'Unsupported content before heading reference'
                prefix += ' ' if child['func'] == 'space' else child['text']
            else:
                assert not contains_ref(child), 'Nested heading reference'
        assert len(specs) == 1, 'Multiple heading references need explicit positioning'
        prefix, target = specs[0]
        position = heading['position']
        candidates = [item for item in references if item.get('target') == target
                      and item['position']['page'] == position['page']
                      and abs(pt(item['position']['y'])-pt(position['y'])) < .03
                      and pt(item['position']['x']) >= pt(position['x'])]
        assert len(candidates) == 1, ('Ambiguous heading reference', heading['label'])
        printed = candidates[0].get('printed')
        assert isinstance(printed, str) and printed
        matches = [node for node, point in nodes if at_heading(point, position)]
        assert len(matches) == 1, ('Ambiguous heading bookmark', heading['label'])
        node = matches[0]
        title = str(node['/Title'])
        assert prefix and title.count(prefix) == 1, (title, prefix)
        insertion = title.index(prefix)+len(prefix)
        assert not title[insertion:].startswith(printed), 'Native title already has reference'
        node[NameObject('/Title')] = TextStringObject(
            title[:insertion]+printed+title[insertion:])
        repairs.append({'label': heading['label'], 'target': target,
                        'before': title, 'after': str(node['/Title']),
                        'native_printed_reference': printed})

    math_repairs, matched_labels = [], set()
    requested_labels = [entry['label'] for entry in math_alternates]
    assert len(requested_labels) == len(set(requested_labels)), 'Duplicate alternate heading'
    with fitz.open(raw_pdf) if raw_pdf else fitz.open() as visible:
        for entry in math_alternates:
            matches = [heading for heading in headings
                       if heading['label'] and heading['label'].strip('<>') == entry['label']]
            assert len(matches) == 1, ('Missing or duplicate alternate heading', entry['label'])
            heading = matches[0]
            position = heading['position']
            bookmarks = [node for node, point in nodes if at_heading(point, position)]
            assert len(bookmarks) == 1, ('Ambiguous alternate bookmark', entry['label'])
            node = bookmarks[0]
            glyphs = entry.get('required_heading_glyphs', [])
            if glyphs:
                assert raw_pdf, 'Style alternatives need the actual PDF heading'
                # The serialized styled.styles field is opaque. Inspect only
                # the heading's own first-line block, never other page text.
                text = ''.join(block[4] for block in visible[position['page']-1].get_text('blocks')
                               if abs(block[1]-pt(position['y'])) < 3
                               and block[4].startswith('§ '))
                assert text and all(glyph in text for glyph in glyphs), \
                    ('Changed visible heading glyph', entry['label'], glyphs)
            title = str(node['/Title'])
            alternate = splice_outline_math(title, list(math_equations(heading['body'])),
                                            entry['fragments'])
            node[NameObject('/Title')] = TextStringObject(alternate)
            math_repairs.append({'label': heading['label'], 'before': title,
                                 'after': alternate, 'fragments': entry['fragments']})
            matched_labels.add(entry['label'])
    assert matched_labels == set(requested_labels)

    matched = []
    for division in divisions:
        matches = [node for node, point in nodes
                   if at_heading(point, division['position'])]
        assert len(matches) == 1, ('Ambiguous division bookmark', division['title'])
        title = str(matches[0]['/Title'])
        assert re.sub(r'\s+', '', title) == re.sub(r'\s+', '', division['title']), \
            ('Division position points at a different title', division['title'], title)
        prefix = re.match(r'^Часть\s+\d+\.\s*', division['printed-title'])
        matched.append({**division, 'title': title,
                        'printed-title': (prefix.group() if prefix else '')+title})
    return matched, repairs, math_repairs


def regroup_outline(writer, divisions):
    """Nest chapter bookmarks under their real major divisions.

    Native heading levels keep the chapter and section counters separate
    from the part counter. Only the PDF outline's links are regrouped.
    """
    if not divisions or '/Outlines' not in writer.root_object:
        return
    outline = writer.root_object['/Outlines']
    root_ref = outline.indirect_reference
    lookup = {re.sub(r'\s+', ' ', d['title']).strip(): d for d in divisions}

    def siblings(first):
        refs, seen = [], set()
        while first:
            identity = (first.idnum, first.generation)
            assert identity not in seen, 'Circular outline chain'
            seen.add(identity)
            refs.append(first)
            first = first.get_object().get('/Next')
        return refs

    roots, children, current = [], {}, None
    for ref in siblings(outline.get('/First')):
        node = ref.get_object()
        title = re.sub(r'\s+', ' ', str(node['/Title'])).strip()
        if title in lookup:
            assert not node.get('/First'), 'Division already has children'
            current = ref
            children[ref.idnum] = []
            node[NameObject('/Title')] = TextStringObject(
                lookup[title]['printed-title'])
            roots.append(ref)
        elif current is not None and re.match(r'^Глава [IVXLCDM]+\.', title):
            children[current.idnum].append(ref)
        else:
            current = None
            roots.append(ref)

    def relink(parent, parent_ref, refs):
        for key in ('/First', '/Last'):
            parent.pop(key, None)
        if not refs:
            return
        parent[NameObject('/First')] = refs[0]
        parent[NameObject('/Last')] = refs[-1]
        for i, ref in enumerate(refs):
            node = ref.get_object()
            node[NameObject('/Parent')] = parent_ref
            for key in ('/Prev', '/Next'):
                node.pop(key, None)
            if i:
                node[NameObject('/Prev')] = refs[i - 1]
            if i + 1 < len(refs):
                node[NameObject('/Next')] = refs[i + 1]

    relink(outline, root_ref, roots)
    for ref in roots:
        if ref.idnum in children:
            relink(ref.get_object(), ref, children[ref.idnum])

    def counts(node):
        total, visible = 0, 0
        for ref in siblings(node.get('/First')):
            child = ref.get_object()
            descendants, expanded = counts(child)
            total += 1 + descendants
            visible += 1 + expanded
        if total:
            closed = int(node.get('/Count', 0)) < 0
            node[NameObject('/Count')] = NumberObject(-total if closed else visible)
            return total, 0 if closed else visible
        node.pop('/Count', None)
        return 0, 0

    counts(outline)


def normalize_outline_destinations(writer, original, *, left=0):
    """Chapter starts target the page top; other headings retain their height."""
    count = 0
    page_map = {(p.indirect_reference.idnum, p.indirect_reference.generation): p
                for p in original.pages}

    def walk(ref, depth=0):
        nonlocal count
        while ref:
            node = ref.get_object()
            holder, key = node, '/Dest'
            if '/A' in node:
                holder = node['/A'].get_object()
                if holder.get('/S') != '/GoTo':
                    raise ValueError('Unexpected non-GoTo outline action')
                key = '/D'
            dest = holder.get(key)
            if hasattr(dest, 'get_object'):
                dest = dest.get_object()
            if isinstance(dest, str):
                dest = original.named_destinations[dest].dest_array
            if not isinstance(dest, (list, ArrayObject)) or len(dest) != 5 \
                    or dest[1] != '/XYZ':
                raise ValueError(f'Unexpected destination: {dest}')
            x = FloatObject(left)
            page = page_map[(dest[0].idnum, dest[0].generation)]
            assert page.get('/Rotate', 0) == 0 and list(page.mediabox)[:2] == [0, 0]
            height = float(page.mediabox.top)
            top = height if depth == 0 or re.match(
                r'^Глава [IVXLCDM]+\.', str(node['/Title']).strip()) else min(
                    height, float(dest[3]) + 3)
            holder[NameObject(key)] = ArrayObject([
                dest[0], NameObject('/XYZ'), x, FloatObject(top), NullObject()])
            count += 1
            if node.get('/First'):
                walk(node['/First'], depth + 1)
            ref = node.get('/Next')

    if '/Outlines' in writer.root_object:
        walk(writer.root_object['/Outlines'].get('/First'))
    return count


def page_label_problems(labels):
    """Page labels as Typst sets them, checked for sense.

    Unnumbered pages (the cover, blank pages) carry an empty label. The
    numbered ones form at most one roman run (front matter) and then one
    arabic run starting at 1 (the text). Within a run the number follows the
    physical page, so nothing repeats and nothing jumps.
    """
    problems, runs = [], []
    for index, label in enumerate(labels):
        if label == '':
            continue
        if label.isdecimal():
            style, value = 'arabic', int(label)
        elif re.fullmatch(r'[ivxlcdm]+|[IVXLCDM]+', label) \
                and from_roman(label):
            style, value = 'roman', from_roman(label)
        else:
            problems.append(f'PDF page {index + 1}: label {label!r} is '
                            'neither roman nor arabic')
            continue
        if runs and runs[-1][0] == style:
            expected = runs[-1][2] + index - runs[-1][1]
            if value != expected:
                problems.append(f'PDF page {index + 1}: label {label!r} '
                                f'breaks the {style} sequence')
                runs[-1] = [style, index, value]
        else:
            runs.append([style, index, value])
    styles = [run[0] for run in runs]
    if styles not in (['arabic'], ['roman', 'arabic']):
        problems.append(f'page numbering runs {styles}: expected roman front '
                        'matter (optional) and then one arabic run')
    arabic = [run for run in runs if run[0] == 'arabic']
    if arabic and arabic[0][2] != 1:
        problems.append(f'the text starts at page {arabic[0][2]}, not 1')
    return problems


def normalize_outlines(raw, output, *, book=True, references=(), divisions=(),
                       headings=(), math_alternates=()):
    """Write `output` from Typst's `raw` PDF: zoom-preserving bookmarks,
    link descriptions; everything else checked unchanged."""
    original = PdfReader(raw)
    writer = PdfWriter(raw, incremental=True)
    # Coordinate links get the printed page label as their description,
    # not Typst's physical-page tooltip (index locators).
    set_link_descriptions(original, references)
    set_link_descriptions(writer, references)
    preserved = accessibility_signature(original)
    left = settings()['pdf_navigation']['outline_left']
    divisions, title_repairs, math_repairs = native_outline_titles(
        writer, divisions, headings, references, math_alternates, raw)
    regroup_outline(writer, divisions)
    count = normalize_outline_destinations(writer, original, left=left)
    assert '/OpenAction' not in writer.root_object
    tmp = Path(output).with_suffix('.tmp.pdf')
    writer.write(tmp)
    checked = PdfReader(tmp)
    assert accessibility_signature(checked) == preserved, \
        'Tags or embedded fonts changed'
    labels = checked.page_labels
    if book:
        problems = page_label_problems(labels)
        assert not problems, 'Page labels: ' + '; '.join(problems)
    records = []

    def validate(items, depth=0):
        for item in items:
            if isinstance(item, list):
                validate(item, depth+1)
                continue
            dest = item.dest_array
            assert len(dest) == 5 and dest[1] == '/XYZ'
            assert (isinstance(dest[2], NullObject) if left is None
                    else float(dest[2]) == left)
            assert isinstance(dest[4], NullObject), 'Bookmark sets a zoom'
            page = checked.get_destination_page_number(item)
            assert page is not None and 0 <= page < len(checked.pages)
            assert 0 <= float(dest[3]) <= float(checked.pages[page].mediabox.top)
            records.append({'title': item.title, 'depth': depth,
                            'pdf_page': page+1, 'page_label': labels[page],
                            'top': float(dest[3]), 'left': left, 'zoom': None,
                            'type': 'XYZ'})

    validate(checked.outline)
    assert len(records) == count
    assert len(original.pages) == len(checked.pages)
    for before, after in zip(original.pages, checked.pages):
        assert list(before.mediabox) == list(after.mediabox)
        assert list(before.cropbox) == list(after.cropbox)
        assert before.get('/Rotate', 0) == after.get('/Rotate', 0)
        assert before.get_contents().get_data() == \
            after.get_contents().get_data()
        assert len(before.get('/Annots', [])) == len(after.get('/Annots', []))
    text = '\n'.join(p.extract_text() for p in checked.pages)
    phrases = settings().get('required_text', []) if book else []
    for phrase in phrases:
        assert phrase in text, f'Required text missing from the PDF: {phrase}'
    assert '\N{REPLACEMENT CHARACTER}' not in text and '\x00' not in text
    assert sum(len(p.images) for p in checked.pages) == 0, \
        'Unexpected raster image in the new setting'
    check_fonts(tmp, Path(output).name, book_font_names())
    tmp.replace(output)
    return {'pdf_pages': len(checked.pages), 'bookmark_count': count,
            'native_reference_title_repairs': title_repairs,
            'native_math_title_repairs': math_repairs,
            'accessibility_and_fonts_unchanged': preserved,
            'page_labels': labels, 'bookmarks': records,
            'page_streams_unchanged_after_outline_normalization': True,
            'geometry_and_annotation_counts_unchanged': True,
            'raster_images': 0, 'text_search_checks': phrases,
            'fonts_from_assets_only': True, 'missing_glyphs': 0,
            'viewer_zoom_test': 'not performed; PDF objects validated'}


def output_path(notes=True):
    output = ROOT/settings()['output']
    return output if notes else output.with_name(output.stem +
                                                 '.no-notes.pdf')


def ensure_lint(fingerprint):
    """Run the lint unless it has passed on exactly these inputs."""
    path = cache_path(ROOT)/'typst-lint.json'
    if path.exists() and (cache_path(ROOT)/'document.json').exists():
        report = json.loads(path.read_text())
        if report.get('status') == 'passed' and \
                report.get('fingerprint') == fingerprint:
            return
    if lint()['status'] != 'passed':
        raise SystemExit('Lint failed; PDF was not replaced.')


def build(force=False, thorough=False, exported=None, notes=True):
    """Build the book (`notes=False`: the edition without editorial notes)."""
    cache = cache_path(ROOT)
    cache.mkdir(parents=True, exist_ok=True)
    variant = '' if notes else '.no-notes'
    output = output_path(notes)
    # A fresh clone has no build/ yet (it is ignored by Git); the
    # intermediates are in the cache, not there.
    output.parent.mkdir(parents=True, exist_ok=True)
    current_stage = stage()
    fingerprint = {'sources': input_hashes(ROOT), 'tools': tool_versions(),
                   'stage': current_stage}
    state_path = cache/f'build-state{variant}.json'
    if not force and exported is None and state_path.exists() \
            and output.exists():
        state = json.loads(state_path.read_text())
        if state['fingerprint'] == fingerprint and \
                state['pdf_sha256'] == digest(output):
            print('PDF is current: '+str(output.relative_to(ROOT)))
            return
    ensure_lint(fingerprint)
    start = time.perf_counter()
    raw = cache/f'book{variant}-raw.pdf'
    if exported is None:
        result = run(['typst', 'compile', *typst_inputs(notes=notes),
                      settings()['entry'], str(raw)])
        (cache/f'typst{variant}.log').write_text(result.stdout+result.stderr)
    else:
        if not exported.is_file():
            raise RuntimeError('Tinymist produced no PDF at '+str(exported)
                               + '; inspect its export task log.')
        shutil.copyfile(exported, raw)
    raw_reader = PdfReader(raw)
    assert '/StructTreeRoot' in raw_reader.trailer['/Root'], \
        'PDF accessibility tags missing'
    if notes:
        # The lint evaluated exactly these inputs a moment ago.
        document = json.loads((cache/'document.json').read_text())
    else:
        result, document = evaluate(ROOT, notes=False)
        if document is None:
            raise RuntimeError('typst eval failed:\n' + result.stderr)
    metadata = [x['value'] for x in document['metadata']
                if isinstance(x['value'], dict)]
    references = [x for x in metadata
                  if x.get('kind') in ('cross-reference', 'page-reference')]
    unresolved = unresolved_references(document, current_stage)
    if current_stage == 'final' and unresolved['count']:
        raise SystemExit('Unresolved references in the final stage: '
                         + ', '.join(t['target'] for t in unresolved['targets']))
    staged = cache/f'book{variant}-checked.pdf'
    divisions = [x for x in metadata if x.get('kind') == 'major-division']
    math_alternates = json.loads((ROOT/'config/outline-math.json').read_text())['headings']
    report = normalize_outlines(raw, staged, references=references,
                                divisions=divisions, headings=document['headings'],
                                math_alternates=math_alternates)
    links = check_links(staged, references)
    # A problem's head leads to its hint and the hint's number back.
    links['hint_links'] = check_hint_links(
        links, [x for x in metadata if x.get('kind') == 'hint-link'])
    links['bibliography_backlinks'] = check_bibliography_links(
        staged, document, links, ROOT)
    report['output_sha256'] = digest(staged)
    report['source_input_sha256'] = fingerprint['sources']
    report['tools'] = fingerprint['tools']
    report['stage'] = current_stage
    report['editorial_notes'] = notes
    report['unresolved_references'] = unresolved['count']
    if thorough:
        whitespace = check_whitespace(staged, report['bookmarks'])
        (cache/f'whitespace-report{variant}.json').write_text(
            json.dumps(whitespace, indent=2)+'\n')
        if whitespace['status'] != 'passed':
            print('Layout advisory (does not fail the build): bottom gaps on '
                  'PDF pages ' + str(whitespace['pages_requiring_review'])
                  + '; see ' + str(cache/f'whitespace-report{variant}.json'))
    assert fingerprint['sources'] == input_hashes(ROOT), \
        'Sources changed during build'
    shutil.move(staged, output)
    raw.unlink()
    (cache/f'pdf-report{variant}.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    (cache/f'internal-links{variant}.json').write_text(
        json.dumps(links, ensure_ascii=False, indent=2)+'\n')
    state_path.write_text(json.dumps({
        'fingerprint': fingerprint,
        'pdf_sha256': report['output_sha256']}, indent=2)+'\n')
    summary = {'pdf': str(output.relative_to(ROOT)),
               'pages': report['pdf_pages'],
               'bookmarks': report['bookmark_count'],
               'links': links['internal_link_annotations'],
               'references_checked': links['semantic_references_checked'],
               'hint_links': links['hint_links'],
               'unresolved_references': unresolved['count'],
               'seconds': round(time.perf_counter()-start, 2)}
    print(json.dumps(summary))
    if notes and unresolved['count']:
        _, path = write_unresolved(ROOT, document)
        print(f'{unresolved["count"]} unresolved references to '
              f'{len(unresolved["targets"])} targets ({current_stage}; '
              f'printed unlinked, listed in {path})')


def build_corrections():
    """The reader's list of corrections, typeset from corrections.json.

    `corrections_entry` (content/corrections.typ) reads corrections.json and
    marks every entry it prints with `#metadata((correction: <id>))`; the
    marks must name each id of corrections.json exactly once.
    """
    config = settings()
    cache = cache_path(ROOT)
    cache.mkdir(parents=True, exist_ok=True)
    entry = config['corrections_entry']
    if not (ROOT/entry).is_file():
        raise SystemExit(
            f'{entry} is missing: it typesets corrections.json for the reader '
            'and marks every entry with #metadata((correction: id)).')
    raw = cache/'corrections-raw.pdf'
    run(['typst', 'compile', *typst_inputs(), entry, str(raw)])
    expr = ('query(metadata).map(m => m.value).filter(v => type(v) == '
            'dictionary and "correction" in v).map(v => v.correction)')
    ids = json.loads(run(['typst', 'eval', *typst_inputs(), expr, '--in',
                          entry, '--format', 'json']).stdout)
    expected = [e['id'] for e in
                json.loads((ROOT/'corrections.json').read_text())['entries']]
    missing = sorted(set(expected) - set(ids))
    unknown = sorted(set(ids) - set(expected))
    repeated = sorted({i for i in ids if ids.count(i) > 1})
    assert not (missing or unknown or repeated), (
        f'Correction list does not match corrections.json: missing {missing}, '
        f'unknown {unknown}, repeated {repeated}')
    output = ROOT/config['corrections_output']
    output.parent.mkdir(parents=True, exist_ok=True)
    staged = cache/'corrections-checked.pdf'
    report = normalize_outlines(raw, staged, book=False)
    report['output_sha256'] = digest(staged)
    shutil.move(staged, output)
    (cache/'corrections-report.json').write_text(
        json.dumps(report, indent=2)+'\n')
    raw.unlink()
    print(f'Corrections: {len(ids)} entries; {report["pdf_pages"]} pages')
