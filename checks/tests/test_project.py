"""Проверки читательского журнала и связи ограниченных доказательств с текстом."""
import copy
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'checks/lean'))
from project import editor_settings, settings, stage, typst_inputs
from check_axioms import load_records
from lint_typst import (scan, view, MATH, subscript_calls,
                        numbered_display_checks)


class Corrections(unittest.TestCase):
    def test_schema_and_independent_field_compilation(self):
        data = json.loads((ROOT / 'corrections.json').read_text())
        self.assertEqual(set(data), {'entries'})
        fields = {'id', 'printed_page', 'section', 'place', 'original',
                  'corrected', 'reason', 'verified_by'}
        ids, pages = [], []
        with tempfile.TemporaryDirectory(prefix='bass-corrections-') as tmp:
            output = str(Path(tmp) / 'field.pdf')
            for entry in data['entries']:
                self.assertEqual(set(entry), fields)
                self.assertNotEqual(entry['original'], entry['corrected'])
                self.assertIsInstance(entry['printed_page'], int)
                self.assertTrue(1 <= entry['printed_page'] <= 592)
                ids.append(entry['id'])
                pages.append(entry['printed_page'])
                for field in fields - {'printed_page', 'id'}:
                    value = entry[field]
                    self.assertTrue(value.strip(), (entry['id'], field))
                    self.assertNotRegex(value, r'@[a-z]+:')
                    kinds, _ = scan(value)
                    self.assertEqual(subscript_calls(view(value, kinds,
                                                         (MATH,))), [],
                                     (entry['id'], field))
                    with self.subTest(id=entry['id'], field=field):
                        driver = (
                            '#import "/content/main-defs.typ" as defs\n'
                            '#set page(width:145mm,height:225mm,margin:15mm)\n'
                            '#set text(font:"Libertinus Serif",lang:"ru")\n'
                            '#show math.equation: set text(font:"STIX Two Math")\n'
                            '#eval(' + json.dumps(value, ensure_ascii=False)
                            + ',mode:"markup",scope:dictionary(defs))\n')
                        result = subprocess.run(
                            ['typst', 'compile', '--root', str(ROOT),
                             *typst_inputs(), '-', output], input=driver,
                            cwd=ROOT, capture_output=True, text=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertNotRegex(result.stderr, r'warning: .*font')
        self.assertEqual(ids, [f'C{i:03d}' for i in range(1, len(ids) + 1)])
        self.assertEqual(pages, sorted(pages))


class NumberedDisplays(unittest.TestCase):
    def section_item(self):
        position = {'page': 2, 'x': '40pt', 'y': '90pt'}
        return {
            'equations': [{'label': None, 'block': True, 'numbered': True,
                           'position': position}],
            'labelled': {'ss:restriction': {'count': 1, 'record': {
                'value': {'kind': 'numbered', 'family': 'ss',
                          'number': [9, 1, 7]}, 'position': position}}}}

    def test_section_display_requires_its_unique_typed_record(self):
        valid = self.section_item()
        self.assertEqual(numbered_display_checks(valid), [])
        for field, value in [('kind', 'hint'), ('family', 'th'),
                             ('number', None)]:
            broken = copy.deepcopy(valid)
            broken['labelled']['ss:restriction']['record']['value'][field] = value
            self.assertEqual(len(numbered_display_checks(broken)), 1)
        for count in (0, 2):
            broken = copy.deepcopy(valid)
            broken['labelled']['ss:restriction']['count'] = count
            self.assertEqual(len(numbered_display_checks(broken)), 1)
        broken = copy.deepcopy(valid)
        broken['labelled'] = {}
        self.assertEqual(len(numbered_display_checks(broken)), 1)
        broken = copy.deepcopy(valid)
        broken['labelled']['ss:restriction']['record']['position']['y'] = '91pt'
        # Keep the equation's original position: it belongs to another item.
        broken['equations'][0]['position'] = valid['equations'][0]['position']
        self.assertEqual(len(numbered_display_checks(broken)), 1)

    def test_equation_label_still_requires_a_display(self):
        data = self.section_item()
        data['labelled'] = {}
        data['equations'][0]['label'] = '<eq:restriction>'
        self.assertEqual(numbered_display_checks(data), [])
        data['equations'][0]['block'] = False
        self.assertEqual(len(numbered_display_checks(data)), 1)


class MathematicalProofs(unittest.TestCase):
    def test_manifest_names_real_passages(self):
        _, problems = load_records()
        self.assertEqual(problems, [])


class Editor(unittest.TestCase):
    def test_stage_agrees_with_editor(self):
        self.assertIn('--input=stage=' + stage(),
                      editor_settings()['tinymist.typstExtraArgs'])


if __name__ == '__main__':
    unittest.main()
