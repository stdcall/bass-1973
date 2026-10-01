"""Native counters, part hierarchy and every form of bookmark destination."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import fitz

from pypdf import PdfReader, PdfWriter
from pypdf.generic import (DictionaryObject, Fit, FloatObject, NameObject,
                           NullObject, TextStringObject)

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from build import (math_equations, normalize_outlines, normalize_outline_destinations,
                   splice_outline_math)
from check_links import annotation_owners, check_links
from lint_typst import EXPRESSION
from project import typst_inputs

STYLE = '''#import "/content/book-style.typ": book-style, part, appendix
#import "/content/statements.typ": proposition, assertion, condition-list, condition-item
#show: book-style
'''


def typst(command, source, *args):
    result = subprocess.run(['typst', command, '--root', str(ROOT),
                             *typst_inputs(), *args], input=source,
                            capture_output=True, text=True, cwd=ROOT)
    if result.returncode or 'warning:' in result.stderr:
        raise AssertionError(result.stderr)
    return result.stdout


class NativeLinkFragments(unittest.TestCase):
    def test_entire_math_and_wrapped_link_survives_target_checks(self):
        source = '''#set page(width:10cm,height:12cm,margin:1cm)
#set text(font:"Libertinus Serif",size:11pt)
#let checked(key,body)=context {
  metadata((kind:"cross-reference",target:key,resolved:true,
    position:here().position(),
    target-position:(page:2,x:0pt,y:70pt)))
  link((page:2,x:0pt,y:70pt),body)
}
#checked("ss:math-fragments",[$q-R_0$])

#checked("ss:wrapped-fragments",[
  $q-R_0$ и $q-R_1$ и $q-R_2$ и $q-R_3$ и $q-R_4$ и $q-R_5$.
])
#pagebreak()
Цель обеих ссылок.
'''
        refs = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        with tempfile.TemporaryDirectory(prefix='bass-link-fragments-') as tmp:
            raw = Path(tmp)/'valid.pdf'
            typst('compile', source, '-', str(raw))
            result = check_links(raw, refs)
            self.assertEqual(result['semantic_references_checked'], 2)
            self.assertTrue(all(r['annotation_fragments'] > 1
                                for r in result['references']))
            owners = annotation_owners(PdfReader(raw))
            for case in ('first-glyph', 'wrapped-tail', 'uri-fragment',
                         'horizontal-target', 'unowned-overlap'):
                with self.subTest(case=case):
                    writer = PdfWriter(raw, incremental=True)
                    groups = {}
                    for page in writer.pages:
                        for ref in page.get('/Annots', []):
                            owner = owners[(ref.idnum, ref.generation)]
                            groups.setdefault(owner, []).append(ref.get_object())
                    first, wrapped = list(groups.values())
                    if case in ('first-glyph', 'wrapped-tail'):
                        annotation = first[0] if case == 'first-glyph' else wrapped[-1]
                        annotation['/Dest'][3] = FloatObject(
                            float(annotation['/Dest'][3])-20)
                    elif case == 'uri-fragment':
                        first[0].pop('/Dest')
                        first[0][NameObject('/A')] = DictionaryObject({
                            NameObject('/S'): NameObject('/URI'),
                            NameObject('/URI'): TextStringObject('https://example.org')})
                    elif case == 'horizontal-target':
                        for annotation in first:
                            annotation['/Dest'][2] = FloatObject(20)
                    else:
                        duplicate = DictionaryObject(first[0])
                        writer.pages[0]['/Annots'].append(writer._add_object(duplicate))
                    broken = Path(tmp)/(case+'.pdf')
                    writer.write(broken)
                    with self.assertRaises(AssertionError):
                        check_links(broken, refs)


class NativeNavigation(unittest.TestCase):
    def test_variant_corollary_reuses_author_number_without_counter_step(self):
        source = STYLE + '''#import "/content/statements.typ": theorem, variant-corollary
= Конечные группы <ch:variant-corollary-test>
== Гомоморфизмы Картана <sec:variant-corollary-test>
#theorem[Первая теорема.] <th:finite-group-cartan-injectivity>
#variant-corollary[Следствие теоремы.] <cor:modular-group-ring-cartan-injectivity>
#proposition[Следующий пункт.] <prop:after-variant-corollary>
@th:finite-group-cartan-injectivity, @cor:modular-group-ring-cartan-injectivity,
@prop:after-variant-corollary.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(1.1)', '(1.1)', '(1.2)'])
        self.assertTrue(all(x['resolved'] for x in refs))

    def test_step_heading_and_bare_native_reference(self):
        source = STYLE + '''= Доказательство <ch:step-test>
== Шаги <sec:step-test>
#condition-list[
  #condition-item(format: "step")[Начало.] <cond:step-first>
  #condition-item(format: "step")[Продолжение.] <cond:step-second>
]
На шаге @cond:step-first и на шаге @cond:step-second.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['1', '2'])
        self.assertTrue(all(x['resolved'] for x in refs))
        with tempfile.TemporaryDirectory(prefix='bass-step-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            text = fitz.open(output)[0].get_text()
            self.assertIn('Шаг 1.', text)
            self.assertIn('Шаг 2.', text)
            self.assertIn('На шаге 1', text)

    def test_parameterized_formula_keeps_counter_and_native_reference(self):
        source = STYLE + '''#import "/content/statements.typ": numbered-condition
= Комплексы <ch:parameterized-formula-test>
== Однородная часть <sec:parameterized-formula-test>
$ x = y $ <eq:before-koszul-test>
#numbered-condition[$ A -> B -> 0 $] <eq:homogeneous-koszul-complex>
$ y = z $ <eq:after-koszul-test>
@eq:before-koszul-test, @eq:homogeneous-koszul-complex, @eq:after-koszul-test.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(1)', '(2)ₙ', '(3)'])
        self.assertTrue(all(x['resolved'] for x in refs))
        with tempfile.TemporaryDirectory(prefix='bass-formula-parameter-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            self.assertEqual(len(fitz.open(output)), 1)

    def test_formula_item_keeps_statement_and_equation_series_separate(self):
        source = STYLE + '''#import "/content/statements.typ": item-record
= Пункты и формулы <ch:formula-item-test>
== Последовательность <sec:formula-item-test>
#proposition[Первый пункт.] <prop:before-formula-item>
#item-record($ A -> B -> C $) <ss:formula-item-test>
$ x = y $ <eq:after-formula-item>
#proposition[Следующий пункт.] <prop:after-formula-item>
@prop:before-formula-item, @ss:formula-item-test,
@eq:after-formula-item, @prop:after-formula-item.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs],
                         ['(1.1)', '(1.2)', '(1)', '(1.3)'])
        self.assertTrue(all(x['resolved'] for x in refs))
        with tempfile.TemporaryDirectory(prefix='bass-formula-item-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            document = fitz.open(output)
            self.assertEqual(len(document), 1)
            text = document[0].get_text()
            self.assertIn('(1.2)', text)
            self.assertIn('(1)', text)

    def test_zero_based_conditions_and_default_reset(self):
        source = STYLE + '''= Условия <ch:zero-condition-test>
== Нумерация <sec:zero-condition-test>
#condition-list(start:0)[
  #condition-item[Первое.] <cond:zero-condition-first>
  #condition-item[Второе.] <cond:zero-condition-second>
]
@cond:zero-condition-first, @cond:zero-condition-second.
#condition-list[
  #condition-item[Обычное.] <cond:default-condition-first>
]
@cond:default-condition-first.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        conditions = [x for x in records if isinstance(x, dict)
                      and x.get('family') == 'cond']
        self.assertEqual([x['number'] for x in conditions], [[0], [1], [1]])
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(0)', '(1)', '(1)'])
        self.assertTrue(all(x['resolved'] for x in refs))

    def test_header_resolves_references_before_measuring(self):
        source = STYLE + '''#import "/content/main-defs.typ": K
= Заголовок <ch:header-test>
== Длинный заголовок с группой $K_1$ и ссылкой @prop:header-test: последовательность локализации и её свойства <sec:header-test>
#proposition[Первое утверждение.] <prop:header-test>
Ссылка @prop:header-test.
#lorem(1800)
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(1.1)', '(1.1)'])
        with tempfile.TemporaryDirectory(prefix='bass-header-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            document = fitz.open(output)
            self.assertGreater(len(document), 3)
            for page in document:
                for block in page.get_text('dict')['blocks']:
                    for line in block.get('lines', []):
                        for span in line['spans']:
                            if span['bbox'][3] < 45:
                                self.assertGreaterEqual(span['bbox'][0], 39.4)
                                self.assertLessEqual(span['bbox'][2], page.rect.width - 39.4)

    def test_wide_diagram_fits_and_keeps_formula_reference(self):
        source = STYLE + '''#import "/content/diagrams/commutative.typ": cd, edge
= Схема <ch:wide-diagram-test>
== Последовательность <sec:wide-diagram-test>
$ #cd(
  cell-size: (30mm, 15mm),
  $A_1 & A_2 & A_3 & A_4 & A_5 & A_6$,
  edge((0,0), "r", "->"), edge((1,0), "r", "->"),
  edge((2,0), "r", "->"), edge((3,0), "r", "->"),
  edge((4,0), "r", "->"),
) $ <eq:wide-diagram-test>
Ссылка @eq:wide-diagram-test.
'''
        with tempfile.TemporaryDirectory(prefix='bass-wide-diagram-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            document = fitz.open(output)
            for page in document:
                for block in page.get_text('dict')['blocks']:
                    for line in block.get('lines', []):
                        for span in line['spans']:
                            self.assertGreaterEqual(span['bbox'][0], 39.4)
                            self.assertLessEqual(span['bbox'][2], page.rect.width - 39.4)
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(1)'])
        self.assertTrue(all(x['resolved'] for x in refs))

    def test_condition_variant_keeps_base_and_next_letter(self):
        source = STYLE + '''#import "/content/statements.typ": variant-condition
= Условия <ch:condition-variant-test>
== Варианты <sec:condition-variant-test>
#condition-list[
  #condition-item(format:"cyrillic")[Первое.] <cond:reciprocity-family>
  #condition-item(format:"cyrillic")[Второе.] <cond:reciprocity-local-product-conditions>
  #variant-condition[Вариант второго.] <cond:reciprocity-integral-product-conditions>
  #condition-item(format:"cyrillic")[Третье.] <cond:condition-after-variant>
]
@cond:reciprocity-family, @cond:reciprocity-local-product-conditions,
@cond:reciprocity-integral-product-conditions, @cond:condition-after-variant.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs],
                         ['(а)', '(б)', '(б′)', '(в)'])
        self.assertTrue(all(x['resolved'] for x in refs))

    def test_named_axioms_keep_literal_names_and_native_references(self):
        schemes = {
            'ax:grothendieck-isomorphism': 'Ка)',
            'ax:grothendieck-product': 'Кб)',
            'ax:whitehead-composition': 'Кв)',
            'ax:mennicke-ideal-principal-normalization': 'M0',
            'ax:mennicke-ideal-unit-denominator': 'M1(а)',
            'ax:mennicke-ideal-denominator-translation': 'M1(б)',
            'ax:mennicke-ideal-numerator-multiplicativity': 'M2(а)',
            'ax:mennicke-ideal-denominator-multiplicativity': 'M2(б)',
            'ax:reciprocity-vanishing-normalization': 'q-R0',
            'ax:reciprocity-product-formula': 'q-R1',
            'ax:reciprocity-exponent-normalization': 'q-R0′',
            'ax:reciprocity-residue-characteristic-normalization': 'q-R0″',
            'ax:reciprocity-local-steinberg': '(0)',
            'ax:reciprocity-disjoint-product': '(1)',
            'ax:reciprocity-characteristic-vanishing': '(0′)',
            'ax:reciprocity-integral-product': '(1′)',
            'ax:reciprocity-local-filtration': '(0)ₚ',
        }
        source = STYLE + '''#import "/content/statements.typ": named-axiom
= Аксиомы <ch:named-axiom-test>
== Условия <sec:named-axiom-test>
'''
        source += '\n'.join(f'#named-axiom[Условие.] <{name}>'
                            for name in schemes)
        source += '\n' + ', '.join('@'+name for name in schemes) + '.\n'
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], list(schemes.values()))
        self.assertTrue(all(x['resolved'] for x in refs))

    def test_long_formula_wraps_once_and_keeps_native_references(self):
        source = STYLE + '''#import "/content/main-defs.typ": mennicke
= Формулы <ch:flow-test>
== Цепочка <sec:flow-test>
$ mennicke(b,a) = mennicke(b+1a,a) = mennicke(b+2a,a)
  = mennicke(b+3a,a) = mennicke(b+4a,a) = mennicke(b+5a,a)
  = mennicke(b+6a,a) = mennicke(b+7a,a) = mennicke(b+8a,a)
  = mennicke(b+9a,a) = mennicke(b+10a,a) = mennicke(b+11a,a) $
  <eq:flow-long>
$ c = d $ <eq:flow-next>
@eq:flow-long и @eq:flow-next.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs], ['(1)', '(2)'])
        self.assertTrue(all(x['resolved'] for x in refs))
        with tempfile.TemporaryDirectory(prefix='bass-flow-') as tmp:
            output = Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(output))
            document = fitz.open(output)
            text = ''.join(page.get_text() for page in document)
            self.assertEqual(text.count('𝑏'), 12, 'Formula repeated or lost')
            for page in document:
                for block in page.get_text('dict')['blocks']:
                    for line in block.get('lines', []):
                        for span in line['spans']:
                            self.assertGreaterEqual(span['bbox'][0], 39.4)
                            self.assertLessEqual(span['bbox'][2], page.rect.width - 39.4)

    def test_two_parts_appendix_and_preserved_pdf(self):
        source = STYLE + '''#part[Первая часть] <part:nav-first>
= Первая глава <ch:nav-first>
== Первый параграф <sec:nav-first>
Первый текст.
= Вторая глава <ch:nav-second>
== Второй параграф <sec:nav-second>
Второй текст.
#part[Вторая часть] <part:nav-second>
= Третья глава <ch:nav-third>
== Третий параграф <sec:nav-third>
Третий текст.
#appendix[Приложение] <front:nav-appendix>
= Четвёртая глава <ch:nav-fourth>
== Четвёртый параграф <sec:nav-fourth>
Четвёртый текст.
#heading(level:1,numbering:none)[Послесловие] <back:nav-after>
Ссылки @front:nav-appendix и @back:nav-after.
#outline()
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        divisions = [x for x in records if isinstance(x, dict)
                     and x.get('kind') == 'major-division']
        refs = {x['target']: x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference'}
        self.assertEqual(refs['front:nav-appendix']['printed'], 'Приложение')
        self.assertEqual(refs['back:nav-after']['printed'], 'Послесловие')
        self.assertTrue(all(x['resolved'] for x in refs.values()))
        with tempfile.TemporaryDirectory(prefix='bass-navigation-') as tmp:
            raw, output = Path(tmp)/'raw.pdf', Path(tmp)/'out.pdf'
            typst('compile', source, '-', str(raw))
            report = normalize_outlines(raw, output, book=False,
                                        divisions=divisions)
            nodes = report['bookmarks']
            self.assertEqual([x['title'] for x in nodes if x['depth'] == 0],
                ['Часть 1. Первая часть', 'Часть 2. Вторая часть',
                 'Приложение', 'Послесловие'])
            chapters = [x for x in nodes if x['title'].startswith('Глава ')]
            self.assertEqual([x['depth'] for x in chapters], [1, 1, 1, 1])
            sections = [x for x in nodes if x['title'].startswith('§ ')]
            self.assertEqual([x['depth'] for x in sections], [2, 2, 2, 2])
            reader = PdfReader(output)
            for node in chapters:
                page = reader.pages[node['pdf_page']-1]
                self.assertEqual(node['top'], float(page.mediabox.top))
            self.assertTrue(report['page_streams_unchanged_after_outline_normalization'])
            self.assertEqual(report['missing_glyphs'], 0)

    def test_math_part_and_reference_bookmark_titles_follow_native_counters(self):
        body = '''#part[Первая часть] <part:title-first>
= Первая глава <ch:title-first>
== Утверждения <sec:title-statements>
#proposition[Первое.] <prop:title-first>
{insertion}
#proposition[Второе.] <prop:title-target>
== Доказательство теоремы @prop:title-target: I. Конструкция гомоморфизма $chi'$ <sec:title-proof>
Доказательство.
#part[Алгебраическая $K$-теория] <part:title-math>
= Вторая глава <ch:title-second>
== Следующий параграф <sec:title-next>
Следующий текст.
'''
        printed_numbers = []
        for insertion in ('', '#proposition[Вставка.] <prop:title-inserted>'):
            source = STYLE + body.format(insertion=insertion)
            document = json.loads(typst('eval', source, EXPRESSION,
                                        '--in', '-', '--format', 'json'))
            records = [m['value'] for m in document['metadata']
                       if isinstance(m['value'], dict)]
            divisions = [m for m in records if m.get('kind') == 'major-division']
            refs = [m for m in records if m.get('kind') == 'cross-reference']
            reference, = [m for m in refs if m['target'] == 'prop:title-target']
            heading, = [h for h in document['headings'] if h['label'] == '<sec:title-proof>']
            equation, = math_equations(heading['body'])
            fragment = {'equation_ordinal': 0, 'native_fragment': 'χ', 'alternate': 'χ′',
                        'ast_sha256': hashlib.sha256(json.dumps(equation, sort_keys=True,
                                                ensure_ascii=False).encode()).hexdigest()}
            alternates = [{'label': 'sec:title-proof', 'fragments': [fragment]}]
            printed_numbers.append(reference['printed'])
            with tempfile.TemporaryDirectory(prefix='bass-bookmark-titles-') as tmp:
                raw, output = Path(tmp)/'raw.pdf', Path(tmp)/'out.pdf'
                typst('compile', source, '-', str(raw))
                report = normalize_outlines(raw, output, book=False,
                    references=refs, divisions=divisions, headings=document['headings'],
                    math_alternates=alternates)
                repaired, = report['native_reference_title_repairs']
                self.assertIn('теоремы '+reference['printed']+': I. Конструкция гомоморфизма χ',
                              repaired['after'])
                self.assertEqual(repaired['after'].replace(reference['printed'], ''),
                                 repaired['before'])
                math_repaired, = report['native_math_title_repairs']
                self.assertTrue(math_repaired['after'].endswith('χ′'))
                self.assertEqual(math_repaired['after'][:-1], math_repaired['before'])
                nodes = report['bookmarks']
                self.assertIn('Часть 2. Алгебраическая K-теория',
                              [n['title'] for n in nodes if n['depth'] == 0])
                chapter, = [n for n in nodes if n['title'].startswith('Глава II.')]
                self.assertEqual(chapter['depth'], 1)
                self.assertTrue(report['page_streams_unchanged_after_outline_normalization'])
                for bad_refs in ([], refs+[reference]):
                    with self.assertRaisesRegex(AssertionError, 'Ambiguous heading reference'):
                        normalize_outlines(raw, output, book=False,
                            references=bad_refs, divisions=divisions,
                            headings=document['headings'])
                for bad_fragment in ({**fragment, 'ast_sha256': '0'*64},
                                     {**fragment, 'native_fragment': 'ψ'}):
                    with self.assertRaises(AssertionError):
                        normalize_outlines(raw, output, book=False,
                            references=refs, divisions=divisions, headings=document['headings'],
                            math_alternates=[{'label': 'sec:title-proof',
                                              'fragments': [bad_fragment]}])
        self.assertNotEqual(*printed_numbers)

    def test_math_alternates_preserve_overlapping_native_tokens(self):
        equations = [{'func': 'equation', 'body': 'Gi'},
                     {'func': 'equation', 'body': 'Ki -> Gi'}]
        fragments = [{'equation_ordinal': i, 'native_fragment': native, 'alternate': alt,
                      'ast_sha256': hashlib.sha256(json.dumps(equations[i], sort_keys=True,
                                            ensure_ascii=False).encode()).hexdigest()}
                     for i, native, alt in [(0, 'Gi', 'Gᵢ'), (1, 'Ki → Gi', 'Kᵢ → Gᵢ')]]
        self.assertEqual(splice_outline_math('§ 2. Gi и Ki → Gi', equations, fragments),
                         '§ 2. Gᵢ и Kᵢ → Gᵢ')
        with self.assertRaisesRegex(AssertionError, 'ambiguous'):
            splice_outline_math('Gi и Gi и Ki → Gi', equations, fragments)

    def test_math_alternate_checks_visible_style_inside_the_heading(self):
        template = STYLE + '''#part[Часть] <part:style-first>
= Глава <ch:style-first>
== Идеал ${style}(q)$ <sec:style-ideal>
Текст содержит $frak(q)$, но не должен подменять символ заголовка.
'''
        source = template.format(style='frak')
        document = json.loads(typst('eval', source, EXPRESSION,
                                    '--in', '-', '--format', 'json'))
        heading, = [h for h in document['headings'] if h['label'] == '<sec:style-ideal>']
        equation, = math_equations(heading['body'])
        fragment = {'equation_ordinal': 0, 'native_fragment': 'q', 'alternate': '𝔮',
                    'ast_sha256': hashlib.sha256(json.dumps(equation, sort_keys=True,
                                            ensure_ascii=False).encode()).hexdigest()}
        alternates = [{'label': 'sec:style-ideal', 'fragments': [fragment],
                       'required_heading_glyphs': ['𝔮']}]
        with tempfile.TemporaryDirectory(prefix='bass-bookmark-style-') as tmp:
            for style in ('frak', 'cal'):
                source = template.format(style=style)
                document = json.loads(typst('eval', source, EXPRESSION,
                                            '--in', '-', '--format', 'json'))
                records = [m['value'] for m in document['metadata']
                           if isinstance(m['value'], dict)]
                divisions = [m for m in records if m.get('kind') == 'major-division']
                raw, output = Path(tmp)/'raw.pdf', Path(tmp)/'out.pdf'
                typst('compile', source, '-', str(raw))
                def export():
                    return normalize_outlines(raw, output, book=False,
                        divisions=divisions, headings=document['headings'],
                        math_alternates=alternates)
                if style == 'frak':
                    self.assertIn('𝔮', export()['native_math_title_repairs'][0]['after'])
                else:
                    with self.assertRaisesRegex(AssertionError, 'Changed visible heading glyph'):
                        export()

    def test_insertion_recalculates_native_references(self):
        body = '''= Проверка <ch:counter-test>
== Параграф <sec:counter-test>
#proposition[Первое.] <prop:counter-first>
{insertion}
#proposition[Второе.] <prop:counter-second>
Ссылка @prop:counter-second.
#assertion(parameter: "n")[Параметрическое утверждение.] <ss:counter-parameter>
#proposition[Следующее.] <prop:counter-after-parameter>
Ссылки @ss:counter-parameter и @prop:counter-after-parameter.
#condition-list[
  #condition-item(format:"cyrillic-prime-n")[Условие.] <cond:counter-prime>
]
Ссылка @cond:counter-prime.
'''
        for insertion, expected in [('', '(1.2)'),
            ('#proposition[Вставленное.] <prop:counter-inserted>', '(1.3)')]:
            source = STYLE + body.replace('{insertion}', insertion)
            records = json.loads(typst('eval', source,
                'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
            refs = {x['target']: x for x in records if isinstance(x, dict)
                    and x.get('kind') == 'cross-reference'}
            self.assertEqual(refs['prop:counter-second']['printed'], expected)
            self.assertEqual(refs['cond:counter-prime']['printed'], '(а′ₙ)')
            parameter_number = 3 if not insertion else 4
            self.assertEqual(refs['ss:counter-parameter']['printed'],
                             f'(1.{parameter_number})ₙ')
            self.assertEqual(refs['prop:counter-after-parameter']['printed'],
                             f'(1.{parameter_number + 1})')
            self.assertTrue(all(x['resolved'] for x in refs.values()))

    def test_prime_variant_keeps_base_number_and_cross_chapter_reference(self):
        source = STYLE + '''#import "/content/statements.typ": theorem, variant-proposition, definition, variant-definition
#counter(heading).update(4)
= Линейные группы <ch:variant-test>
#counter(heading).update((5,2))
== Определения <sec:definition-variant-test>
#definition[Базовое определение.] <def:relative-stable-rank>
#variant-definition[Первый вариант.] <def:relative-unimodular-transitivity>
#variant-definition[Второй вариант.] <def:relative-linked-matrix-stability>
#definition[Следующее определение.] <def:variant-next>
@def:relative-unimodular-transitivity, @def:relative-linked-matrix-stability и @def:variant-next.
#counter(heading).update((5,3))
== Основные теоремы <sec:variant-test>
#theorem[Базовое утверждение.] <th:linear-normal-subgroup-stability>
#variant-proposition[Относительный вариант.] <prop:relative-linear-normal-subgroup-stability>
#theorem[Следующее утверждение.] <th:variant-next>
@prop:relative-linear-normal-subgroup-stability и @th:variant-next.
= Следующая глава <ch:variant-following>
== Параграф <sec:variant-following>
@prop:relative-linear-normal-subgroup-stability и @def:relative-linked-matrix-stability.
'''
        records = json.loads(typst('eval', source,
            'query(metadata).map(m=>m.value)', '--in', '-', '--format', 'json'))
        refs = [x for x in records if isinstance(x, dict)
                and x.get('kind') == 'cross-reference']
        self.assertEqual([x['printed'] for x in refs],
                         ['(3.1)′', '(3.1)″', '(3.2)', '(4.1)′', '(4.2)',
                          '(V, 4.1)′', '(V, 3.1)″'])
        self.assertTrue(all(x['resolved'] for x in refs))


class DestinationForms(unittest.TestCase):
    def test_action_named_and_nested_destinations_keep_zoom(self):
        with tempfile.TemporaryDirectory(prefix='bass-destinations-') as tmp:
            raw, output = Path(tmp)/'raw.pdf', Path(tmp)/'out.pdf'
            writer = PdfWriter()
            writer.add_blank_page(width=400, height=600)
            parent = writer.add_outline_item('Глава I. Начало', 0,
                                             fit=Fit.xyz(10, 500, 1.25))
            child = writer.add_outline_item('§ 1. Внутри страницы', 0,
                parent=parent, fit=Fit.xyz(10, 320, 2))
            named = writer.add_outline_item('Именованная цель', 0,
                parent=child, fit=Fit.xyz(10, 200, 3))
            action = named.get_object()['/A'].get_object()
            writer.add_named_destination_array(TextStringObject('named'), action['/D'])
            action[NameObject('/D')] = TextStringObject('named')
            # Exercise a direct /Dest as well as /A → /GoTo → /D.
            child_node = child.get_object()
            child_node[NameObject('/Dest')] = child_node['/A']['/D']
            child_node.pop('/A')
            writer.write(raw)
            original = PdfReader(raw)
            checked_writer = PdfWriter(raw, incremental=True)
            self.assertEqual(normalize_outline_destinations(
                checked_writer, original), 3)
            checked_writer.write(output)
            checked = PdfReader(output)
            nodes = [checked.outline[0], checked.outline[1][0],
                     checked.outline[1][1][0]]
            self.assertEqual([float(x.dest_array[3]) for x in nodes],
                             [600, 323, 203])
            for node in nodes:
                self.assertEqual(node.dest_array[1], '/XYZ')
                self.assertEqual(float(node.dest_array[2]), 0)
                self.assertIsInstance(node.dest_array[4], NullObject)


if __name__ == '__main__':
    unittest.main()
