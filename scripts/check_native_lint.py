#!/usr/bin/env python3
"""Compare whole native lint output of two binaries on small full-world fixtures.

This is a regression sample, not a replacement for the complete book's gate.
No diagnostics, hints, traces, ordering or duplicate lines are discarded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

SOURCES = {
    'pass.typ': '#set heading(numbering: "1.")\n#include "nested/pass.typ"\n#text[Ссылка @nested-pass.]\n',
    'nested/pass.typ': '= Вложенный раздел <nested-pass>\n$ (1 + 2) / 3 = 1 $\n',
    'warnings.typ': '#include "nested/warnings.typ"\n',
    'nested/warnings.typ': '''#let misplaced-break() = { break }
#let misplaced-continue() = { continue }
#let dead-math() = $unusedunknownmath$
#let discarded-content() = [Данные #return 1]
#let discarded-style() = { set text(size: 12pt); return }
#let variable-font() = text(font: "Imaginary VF")[unused]
#if true { set text(fill: red) }
#if true { show text: it => it }
#text(font: "Definitely Missing Font")[Проверка включённого файла.]
''',
    'compiler-error.typ': '#include "nested/warnings.typ"\n#include "nested/compiler-error.typ"\n',
    'nested/compiler-error.typ': '$compilerunknownmath$\n',
    'dynamic.typ': '''#let module-path() = "nested/dynamic-module.typ"
#import module-path(): *
#import "nested/nested-import.typ": nested-text
#exported-text()
#nested-text()
''',
    'nested/dynamic-module.typ': '#let exported-text() = [Динамический импорт.]\n#let dead() = $dynamicunknownmath$\n',
    'nested/nested-import.typ': '#import "second-level.typ": second-text\n#let nested-text() = second-text()\n',
    'nested/second-level.typ': '#let second-text() = [Импорт второго уровня.]\n#let dead() = $secondlevelunknownmath$\n',
    'cap-loader.typ': '''#let load(path) = {
  import path: *
  let dead-valid() = $binding$
  ""
}
''',
    'cap-early.typ': '#let binding = 1\n#let dead() = $earlyunknownmath$\n',
    'cap-late.typ': '#let binding = 2\n#let dead() = $lateunknownmath$\n',
    'cap-0.typ': '#import "cap-loader.typ": load\n#context load("cap-late.typ")\n',
    'cap-9.typ': '#import "cap-loader.typ": load\n#for i in range(9) { load("cap-early.typ") }\n#context load("cap-late.typ")\n',
    'cap-10.typ': '#import "cap-loader.typ": load\n#for i in range(10) { load("cap-early.typ") }\n#context load("cap-late.typ")\n',
    'cap-error-after-10.typ': '#import "cap-loader.typ": load\n#for i in range(10) { load("cap-early.typ") }\n#panic("deliberate error after repeated dynamic imports")\n',
}
CASES = {
    'pass': {'entry': 'pass.typ', 'exit': 0, 'required': []},
    'warnings': {'entry': 'warnings.typ', 'exit': 1, 'required': [
        'unusedunknownmath', '`break` statement in a non-loop context',
        '`continue` statement in a non-loop context', 'implicitly discarded by function return',
        'variable font is not supported', "This set statement doesn't take effect.",
        "This show statement doesn't take effect.", 'unknown font family']},
    'compiler-error': {'entry': 'compiler-error.typ', 'exit': 1, 'required': [
        'compilerunknownmath', 'unusedunknownmath', 'nested/compiler-error.typ', 'nested/warnings.typ']},
    'dynamic': {'entry': 'dynamic.typ', 'exit': 1, 'required': [
        'dynamicunknownmath', 'secondlevelunknownmath', 'nested/dynamic-module.typ', 'nested/second-level.typ']},
    'cap-0': {'entry': 'cap-0.typ', 'exit': 1,
        'required': ['unknown variable: lateunknownmath'],
        'required_diagnostics': ['cap-late.typ:2:15: warning: unknown variable: lateunknownmath'],
        'forbidden': ['unknown variable: binding']},
    'cap-9': {'entry': 'cap-9.typ', 'exit': 1,
        'required': ['unknown variable: lateunknownmath', 'unknown variable: earlyunknownmath'],
        'required_diagnostics': ['cap-late.typ:2:15: warning: unknown variable: lateunknownmath',
                                 'cap-early.typ:2:15: warning: unknown variable: earlyunknownmath'],
        'forbidden': ['unknown variable: binding']},
    'cap-10': {'entry': 'cap-10.typ', 'exit': 1,
        'required': ['unknown variable: lateunknownmath', 'unknown variable: earlyunknownmath'],
        'required_diagnostics': ['cap-late.typ:2:15: warning: unknown variable: lateunknownmath',
                                 'cap-early.typ:2:15: warning: unknown variable: earlyunknownmath'],
        'forbidden': ['unknown variable: binding']},
    'cap-error-after-10': {'entry': 'cap-error-after-10.typ', 'exit': 1,
        'required': ['unknown variable: earlyunknownmath',
                     'error: panicked with: deliberate error after repeated dynamic imports'],
        'required_diagnostics': ['cap-early.typ:2:15: warning: unknown variable: earlyunknownmath',
                                 'cap-error-after-10.typ:3:1: error: panicked with: deliberate error after repeated dynamic imports'],
        'forbidden': ['unknown variable: binding']},
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--baseline', required=True, type=Path)
    parser.add_argument('--candidate', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    fixture_root = (args.out / 'fixtures').resolve()
    fixture_root.mkdir(exist_ok=True)
    for name, content in SOURCES.items():
        path = fixture_root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    config = json.loads((args.project / 'config/project.json').read_text())
    common = ['--ignore-system-fonts']
    for font_path in config['font_paths']:
        common += ['--font-path', str((args.project / font_path).resolve())]
    common += ['--root', str(fixture_root), '--input', 'stage=final']
    env = os.environ.copy()
    env['TINYMIST_LOG'] = 'off'
    env['NO_COLOR'] = '1'
    report = {'scope': 'small full-world native regression fixtures only',
              'book_gate_replaced': False, 'results': {}, 'binaries': {},
              'fixture_sha256': {name: sha(fixture_root / name) for name in SOURCES}}
    for role in ('baseline', 'candidate'):
        binary = getattr(args, role).resolve()
        version = subprocess.run([str(binary), '--version'], env=env, capture_output=True,
                                 text=True, timeout=30)
        report['binaries'][role] = {'path': str(binary), 'sha256': sha(binary),
                                  'version_stdout': version.stdout, 'version_stderr': version.stderr,
                                  'version_exit': version.returncode}
    comparisons = []
    for name, case in CASES.items():
        for fmt in ('short', 'human'):
            key = name + ':' + fmt
            results = {}
            for role in ('baseline', 'candidate'):
                binary = str(getattr(args, role).resolve())
                command = [binary, 'lint', *common, '--diagnostic-format', fmt,
                           str(fixture_root / case['entry'])]
                started = time.monotonic()
                run = subprocess.run(command, env=env, cwd=fixture_root, capture_output=True,
                                     text=True, timeout=60)
                for stream in ('stdout', 'stderr'):
                    (args.out / (key.replace(':', '-') + '-' + role + '.' + stream)).write_text(getattr(run, stream))
                normalized = {stream: getattr(run, stream).replace(str(fixture_root), '<fixtures>')
                              .replace(str(args.project.resolve()), '<project>') for stream in ('stdout', 'stderr')}
                output = normalized['stdout'] + normalized['stderr']
                results[role] = {'command': command, 'exit': run.returncode,
                    'elapsed_seconds': time.monotonic() - started, **normalized,
                    'required_messages_present': all(item in output for item in case['required']),
                    'forbidden_messages_absent': all(item not in output for item in case.get('forbidden', []))}
                if fmt == 'short':
                    # These are complete native diagnostics, not string matches in hints.
                    lines = output.splitlines()
                    diagnostics = [line for line in lines if re.search(r': (error|warning): ', line)]
                    expected_counts = {'pass': 0, 'warnings': 10, 'compiler-error': 11, 'dynamic': 2,
                                       'cap-0': 1, 'cap-9': 2, 'cap-10': 2, 'cap-error-after-10': 2}
                    results[role]['diagnostic_count'] = len(diagnostics)
                    results[role]['diagnostic_count_passed'] = len(diagnostics) == expected_counts[name]
                    results[role]['required_diagnostics_present'] = all(
                        any(line.endswith(item) for line in diagnostics)
                        for item in case.get('required_diagnostics', []))
                    if name == 'compiler-error':
                        results[role]['known_unknown_ident_single_error'] = sum(
                            'error: unknown variable: compilerunknownmath' in line for line in diagnostics) == 1
                    if name in ('warnings', 'compiler-error'):
                        # Current native KnownIssues feeds the font enhancement rule;
                        # its compiler warning and enriched lint warning are both retained.
                        results[role]['native_font_diagnostics_retained'] = sum(
                            'warning: unknown font family:' in line for line in diagnostics) == 2
                if name not in ('compiler-error', 'cap-error-after-10'):
                    results[role]['no_compiler_error'] = not bool(re.search(r'(^|\n)(?:[^\n]*: )?error:', output))
                else:
                    results[role]['compiler_error_present'] = bool(re.search(r'(^|\n)(?:[^\n]*: )?error:', output))
            left, right = results['baseline'], results['candidate']
            exact = all(left[field] == right[field] for field in ('exit', 'stdout', 'stderr'))
            expected = all(result['exit'] == case['exit'] and result['required_messages_present']
                and result['forbidden_messages_absent']
                and result.get('no_compiler_error', result.get('compiler_error_present', False))
                and result.get('diagnostic_count_passed', True)
                and result.get('required_diagnostics_present', True)
                and result.get('known_unknown_ident_single_error', True)
                and result.get('native_font_diagnostics_retained', True)
                for result in results.values())
            comparisons.append(exact and expected)
            report['results'][key] = {'whole_output_exact': exact, 'expectations_passed': expected,
                                    'runs': results}
    same_binary = report['binaries']['baseline']['sha256'] == report['binaries']['candidate']['sha256']
    report['same_binary_smoke_test'] = same_binary
    valid_versions = all(item['version_exit'] == 0 for item in report['binaries'].values())
    passed = all(comparisons) and valid_versions and not same_binary
    report['status'] = 'differential_pass' if passed else 'failed'
    report['limitations'] = 'No full-book equivalence or memory reduction is claimed by this fixture run. All book checks remain mandatory.'
    (args.out / 'receipt.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(report['status'], len(comparisons), 'case-format comparisons')
    return 0 if passed else 1

if __name__ == '__main__':
    raise SystemExit(main())
