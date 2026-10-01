"""Совещательная проверка русской прозы через Vale и парсер typst2vast.

Математика и код не рассматриваются. Правила исправляют типографские
описки и сохраняют авторский слог. Отчёт хранится в кэше сборки.
"""
import argparse
import json
from pathlib import Path
import subprocess

from project import ROOT, cache_path


def check():
    sources = sorted((ROOT / 'content').rglob('*.typ'))
    result = subprocess.run(
        ['vale', '--config', str(ROOT / 'assets/prose/.vale.ini'),
         '--output', 'JSON', *map(str, sources)],
        cwd=ROOT, capture_output=True, text=True)
    if result.returncode not in (0, 1):
        raise RuntimeError(result.stderr or result.stdout)
    issues = json.loads(result.stdout or '{}')
    findings = []
    for filename, entries in issues.items():
        for entry in entries:
            findings.append({
                'file': str(Path(filename).relative_to(ROOT)),
                'line': entry['Line'], 'span': entry['Span'],
                'rule': entry['Check'], 'message': entry['Message'],
            })
    report = {'checker': 'vale', 'findings': findings,
              'source_files': len(sources)}
    cache = cache_path()
    cache.mkdir(parents=True, exist_ok=True)
    (cache / 'prose.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    for entry in findings[:60]:
        print(f"{entry['file']}:{entry['line']}: {entry['message']}")
    print(f'Vale: {len(findings)} находок; проверено файлов: {len(sources)}.')
    return findings


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fail-on-findings', action='store_true')
    args = parser.parse_args()
    findings = check()
    if findings and args.fail_on_findings:
        raise SystemExit(1)
