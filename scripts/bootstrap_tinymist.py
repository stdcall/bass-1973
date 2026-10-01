#!/usr/bin/env python3
"""Install or validate a project-scoped, pinned Tinymist build. Python >=3.12."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()


def pin(value):
    if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value):
        raise ValueError('A reviewed SHA-256 pin is required')
    return value


def checked(path, expected):
    if Path(path).is_symlink() or sha(path) != pin(expected):
        raise ValueError(f'Checksum mismatch: {Path(path).name}')


def run(args, **kwargs):
    return subprocess.run(args, check=True, text=True, **kwargs)


def toolchain():
    paths = {name: shutil.which(name) for name in ('cargo', 'rustc')}
    if not all(paths.values()):
        raise ValueError('Provide cargo and rustc 1.97.0 on PATH')
    versions = {name: run([path, '-Vv'], capture_output=True).stdout
                for name, path in paths.items()}
    for name, text in versions.items():
        if not text.startswith(name + ' 1.97.0 '):
            raise ValueError(f'{name} must be exactly 1.97.0')
    # Resolve rustup shims to the selected concrete toolchain before sanitizing
    # build environment variables. Never install or change the global default.
    sysroot = Path(run([paths['rustc'], '--print', 'sysroot'],
                      capture_output=True).stdout.strip())
    concrete = {name: str(sysroot / 'bin' / name) for name in ('cargo', 'rustc', 'rustdoc')}
    for name in ('cargo', 'rustc', 'rustdoc'):
        text = run([concrete[name], '-V'], capture_output=True).stdout
        if not text.startswith(name + ' 1.97.0 '):
            raise ValueError('Concrete toolchain version mismatch: ' + name)
    host = re.search(r'^host: (.+)$', versions['rustc'], re.M).group(1)
    if host not in ('x86_64-unknown-linux-gnu', 'aarch64-apple-darwin', 'x86_64-apple-darwin'):
        raise ValueError('No reviewed platform configuration for ' + host)
    return concrete, versions, host


def download(spec, path):
    pin(spec['sha256'])
    if not spec['url'].startswith('https://'):
        raise ValueError('HTTPS download required')
    with urllib.request.urlopen(spec['url'], timeout=60) as response:
        if not response.url.startswith('https://'):
            raise ValueError('Insecure redirect')
        with path.open('xb') as stream:
            size = 0
            while block := response.read(1024 * 1024):
                size += len(block)
                if size > 512 * 1024 * 1024:
                    raise ValueError('Archive size limit exceeded')
                stream.write(block)
    checked(path, spec['sha256'])


def extract(archive, directory):
    """Regular files/directories only; reject traversal, duplicates and links."""
    directory.mkdir()
    with tarfile.open(archive) as bundle:
        seen = set()
        total = 0
        members = bundle.getmembers()
        if len(members) > 100000:
            raise ValueError('Too many archive entries')
        for item in members:
            name = PurePosixPath(item.name)
            if name.is_absolute() or '..' in name.parts or '\\' in item.name:
                raise ValueError('Unsafe archive path')
            if name.as_posix() in seen or not (item.isdir() or item.isfile()):
                raise ValueError('Duplicate or nonregular archive entry')
            seen.add(name.as_posix())
            total += item.size
            if total > 1024 * 1024 * 1024:
                raise ValueError('Expanded archive size limit exceeded')
        bundle.extractall(directory, members=members, filter='data')


def identity(config, base):
    paths, versions, host = toolchain()
    patch = base / config['patch']['file']
    fixture = base / config['fixture_helper']
    checked(patch, config['patch']['sha256'])
    inputs = {'schema': 1, 'source': config['source'],
              'patch_sha256': sha(patch), 'cargo_lock_sha256': pin(config['cargo_lock_sha256']),
              'toolchain': versions, 'host': host, 'system': platform.platform(),
              'profile': 'release', 'features': 'full-default', 'jobs': 2,
              'helper_sha256': sha(__file__), 'fixture_helper_sha256': sha(fixture),
              'reference': config['references'][host],
              'patched_files': config['patched_files']}
    pin(inputs['source']['sha256'])
    pin(inputs['reference']['sha256'])
    return inputs, digest(inputs), paths


def validate(entry, inputs, key, *, return_sha=False):
    """Called before a cached executable is added to a subprocess PATH."""
    if any((entry / name).is_symlink() for name in ('', 'bin', 'fixtures')):
        raise ValueError('Symlinked cache directory')
    manifest_path = entry / 'manifest.json'
    if manifest_path.is_symlink():
        raise ValueError('Symlinked manifest')
    manifest = json.loads(manifest_path.read_text())
    if manifest['fingerprint'] != key or manifest['inputs'] != inputs:
        raise ValueError('Cached build provenance mismatch')
    binary = entry / 'bin/tinymist'
    checked(binary, manifest['binary_sha256'])
    receipt_path = entry / 'fixtures/receipt.json'
    checked(receipt_path, manifest['fixture_receipt_sha256'])
    receipt = json.loads(receipt_path.read_text())
    cases = {name + ':' + fmt for name in ('pass', 'warnings', 'compiler-error', 'dynamic')
             for fmt in ('short', 'human')}
    if receipt['status'] != 'differential_pass' or set(receipt['results']) != cases:
        raise ValueError('Native diagnostic fixture gate incomplete')
    if receipt['binaries']['candidate']['sha256'] != manifest['binary_sha256']:
        raise ValueError('Fixtures tested another candidate')
    if receipt['binaries']['baseline']['sha256'] != manifest['reference_binary_sha256']:
        raise ValueError('Fixtures tested another reference')
    if manifest['reference_binary_sha256'] == manifest['binary_sha256']:
        raise ValueError('Reference and candidate must be distinct binaries')
    if not all(row['whole_output_exact'] and row['expectations_passed']
               for row in receipt['results'].values()):
        raise ValueError('Native diagnostics changed')
    outputs = {case.replace(':', '-') + '-' + role + '.' + stream
               for case in cases for role in ('baseline', 'candidate')
               for stream in ('stdout', 'stderr')}
    if set(manifest['diagnostic_files']) != outputs:
        raise ValueError('Complete diagnostic output inventory required')
    for name, expected in manifest['diagnostic_files'].items():
        checked(entry / 'fixtures' / name, expected)
    return (binary, manifest['binary_sha256']) if return_sha else binary


def install(config, base, cache, project):
    inputs, key, tools = identity(config, base)
    cache.mkdir(parents=True, exist_ok=True)
    entry = cache / key
    if entry.exists():
        return validate(entry, inputs, key)
    # Never share a Cargo target with a differently patched tree. Fresh target
    # also avoids reuse when extracted sources have older modification times.
    with tempfile.TemporaryDirectory(prefix=key + '-', dir=cache) as temporary:
        work = Path(temporary)
        download(config['source'], work / 'source.tar')
        extract(work / 'source.tar', work / 'source')
        roots = list((work / 'source').iterdir())
        if len(roots) != 1 or not roots[0].is_dir():
            raise ValueError('Unexpected source archive root')
        source = roots[0]
        if source.name != 'tinymist-' + config['source']['commit']:
            raise ValueError('Source archive commit root mismatch')
        checked(source / 'Cargo.lock', config['cargo_lock_sha256'])
        for name, pins in config['patched_files'].items():
            checked(source / name, pins['before'])
        patch = (base / config['patch']['file']).resolve()
        run(['git', 'apply', '--check', str(patch)], cwd=source)
        run(['git', 'apply', str(patch)], cwd=source)
        for name, pins in config['patched_files'].items():
            checked(source / name, pins['after'])
        env = os.environ.copy()
        for name in list(env):
            if name.startswith(('CARGO_PROFILE_', 'CARGO_BUILD_', 'CARGO_TARGET_', 'RUST')) or name == 'CARGO_ENCODED_RUSTFLAGS':
                env.pop(name)
        env.update(CARGO_HOME=str(cache / 'cargo-downloads'),
                   CARGO_TARGET_DIR=str(work / 'target'),
                   RUSTC=tools['rustc'], RUSTDOC=tools['rustdoc'],
                   CARGO_INCREMENTAL='0', VERGEN_IDEMPOTENT='1')
        run([tools['cargo'], 'build', '--locked', '--release', '--jobs', '2',
             '-p', 'tinymist-cli'], cwd=source, env=env)
        checked(source / 'Cargo.lock', config['cargo_lock_sha256'])
        staged = work / 'installed'
        (staged / 'bin').mkdir(parents=True)
        candidate = staged / 'bin/tinymist'
        shutil.copy2(work / 'target/release/tinymist', candidate)
        reference_spec = inputs['reference']
        download(reference_spec, work / 'reference.tar')
        extract(work / 'reference.tar', work / 'reference')
        references = [p for p in (work / 'reference').rglob('tinymist') if p.is_file()]
        if len(references) != 1:
            raise ValueError('Ambiguous reference executable')
        reference = references[0]
        run([os.sys.executable, str(base / config['fixture_helper']),
             '--project', str(project), '--baseline', str(reference),
             '--candidate', str(candidate), '--out', str(staged / 'fixtures')])
        diagnostic_files = {p.name: sha(p) for p in (staged / 'fixtures').iterdir()
                            if p.is_file() and p.suffix in ('.stdout', '.stderr')}
        manifest = {'fingerprint': key, 'inputs': inputs, 'binary_sha256': sha(candidate),
                    'reference_binary_sha256': sha(reference),
                    'fixture_receipt_sha256': sha(staged / 'fixtures/receipt.json'),
                    'diagnostic_files': diagnostic_files}
        (staged / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        validate(staged, inputs, key)
        # Failure/timeout never creates a selectable incomplete entry.
        staged.rename(entry)
    return validate(entry, inputs, key)


def selected_environment(config_path, cache, env=None):
    """No build during version/lint/LSP checks. Missing/invalid cache fails closed."""
    config_path = Path(config_path).resolve()
    config = json.loads(config_path.read_text())
    inputs, key, _ = identity(config, config_path.parent)
    binary, binary_sha = validate(Path(cache).expanduser() / key, inputs, key,
                                  return_sha=True)
    # Expose identity only after the complete cache guard succeeds. Callers
    # reuse this environment for version reporting instead of reinspecting Rust.
    result = (os.environ if env is None else env).copy()
    result['PATH'] = str(binary.parent) + os.pathsep + result.get('PATH', '')
    result['BASS_TINYMIST_FINGERPRINT'] = key
    result['BASS_TINYMIST_SHA256'] = binary_sha
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('fingerprint', 'install', 'select'))
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--project', type=Path)
    args = parser.parse_args()
    config_path = args.config.resolve()
    config = json.loads(config_path.read_text())
    if args.command == 'install':
        if args.project is None:
            parser.error('--project is required for native fixture fonts')
        print(install(config, config_path.parent, args.cache.expanduser(), args.project.resolve()))
    else:
        inputs, key, _ = identity(config, config_path.parent)
        print(key if args.command == 'fingerprint' else
              validate(args.cache.expanduser() / key, inputs, key).parent)


if __name__ == '__main__':
    main()
