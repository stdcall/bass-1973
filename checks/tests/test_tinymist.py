"""Cheap installer integrity tests; no native compilation or performance claims."""
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import bootstrap_tinymist as module


class Guards(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.addCleanup(self.temp.cleanup)

    def archive(self, members):
        archive = self.root / 'archive.tar'
        with tarfile.open(archive, 'w') as stream:
            for name, kind in members:
                item = tarfile.TarInfo(name)
                if kind == 'link':
                    item.type, item.linkname = tarfile.SYMTYPE, '/outside'
                    stream.addfile(item)
                else:
                    item.size = 1
                    stream.addfile(item, io.BytesIO(b'x'))
        return archive

    def test_regular_archive(self):
        module.extract(self.archive([('root/file', 'file')]), self.root / 'out')
        self.assertEqual((self.root / 'out/root/file').read_bytes(), b'x')

    def test_traversal_archive(self):
        with self.assertRaises(ValueError):
            module.extract(self.archive([('../outside', 'file')]), self.root / 'out')

    def test_absolute_archive(self):
        with self.assertRaises(ValueError):
            module.extract(self.archive([('/outside', 'file')]), self.root / 'out')

    def test_link_archive(self):
        with self.assertRaises(ValueError):
            module.extract(self.archive([('root/link', 'link')]), self.root / 'out')

    def test_canonical_duplicate_archive(self):
        with self.assertRaises(ValueError):
            module.extract(self.archive([('root/file', 'file'), ('root//file', 'file')]), self.root / 'out')

    def cache(self):
        entry = self.root / 'cache'
        (entry / 'bin').mkdir(parents=True)
        (entry / 'fixtures').mkdir()
        binary = entry / 'bin/tinymist'
        binary.write_bytes(b'candidate')
        cases = {name + ':' + fmt: {'whole_output_exact': True, 'expectations_passed': True}
                 for name in ('pass', 'warnings', 'compiler-error', 'dynamic')
                 for fmt in ('short', 'human')}
        receipt = {'status': 'differential_pass', 'results': cases,
                   'binaries': {'candidate': {'sha256': module.sha(binary)},
                                'baseline': {'sha256': 'b' * 64}}}
        path = entry / 'fixtures/receipt.json'
        path.write_text(json.dumps(receipt))
        outputs = {}
        for name in cases:
            for role in ('baseline', 'candidate'):
                for stream in ('stdout', 'stderr'):
                    output = entry / 'fixtures' / (name.replace(':', '-') + '-' + role + '.' + stream)
                    output.write_text('complete output')
                    outputs[output.name] = module.sha(output)
        manifest = {'fingerprint': 'key', 'inputs': {'pinned': True},
                    'binary_sha256': module.sha(binary), 'reference_binary_sha256': 'b' * 64,
                    'fixture_receipt_sha256': module.sha(path), 'diagnostic_files': outputs}
        (entry / 'manifest.json').write_text(json.dumps(manifest))
        return entry, manifest

    def test_valid_cached_integrity(self):
        entry, _ = self.cache()
        self.assertEqual(module.validate(entry, {'pinned': True}, 'key'), entry / 'bin/tinymist')

    def test_corrupt_binary(self):
        entry, _ = self.cache()
        (entry / 'bin/tinymist').write_bytes(b'changed')
        with self.assertRaises(ValueError):
            module.validate(entry, {'pinned': True}, 'key')

    def test_wrong_fingerprint(self):
        entry, _ = self.cache()
        with self.assertRaises(ValueError):
            module.validate(entry, {'pinned': True}, 'other')

    def test_corrupt_diagnostic_output(self):
        entry, _ = self.cache()
        (entry / 'fixtures/pass-short-candidate.stdout').write_text('truncated')
        with self.assertRaises(ValueError):
            module.validate(entry, {'pinned': True}, 'key')

    def test_missing_output_inventory(self):
        entry, manifest = self.cache()
        manifest['diagnostic_files'] = {}
        (entry / 'manifest.json').write_text(json.dumps(manifest))
        with self.assertRaises(ValueError):
            module.validate(entry, {'pinned': True}, 'key')

    def test_same_binary_gate(self):
        entry, manifest = self.cache()
        manifest['reference_binary_sha256'] = manifest['binary_sha256']
        receipt_path = entry / 'fixtures/receipt.json'
        receipt = json.loads(receipt_path.read_text())
        receipt['binaries']['baseline']['sha256'] = manifest['binary_sha256']
        receipt_path.write_text(json.dumps(receipt))
        manifest['fixture_receipt_sha256'] = module.sha(receipt_path)
        (entry / 'manifest.json').write_text(json.dumps(manifest))
        with self.assertRaises(ValueError):
            module.validate(entry, {'pinned': True}, 'key')

    def test_environment_identity_after_guard(self):
        entry, manifest = self.cache()
        manifest['fingerprint'] = 'cache'
        (entry / 'manifest.json').write_text(json.dumps(manifest))
        config = self.root / 'config.json'
        config.write_text('{}')
        original = {'PATH': '/ordinary', 'BASS_TINYMIST_SHA256': 'untrusted'}
        with patch.object(module, 'identity', return_value=({'pinned': True}, 'cache', {})) as identity:
            result = module.selected_environment(config, self.root, original)
        identity.assert_called_once()
        self.assertEqual(result['BASS_TINYMIST_FINGERPRINT'], 'cache')
        self.assertEqual(result['BASS_TINYMIST_SHA256'], manifest['binary_sha256'])
        self.assertTrue(result['PATH'].startswith(str(entry / 'bin')))
        self.assertEqual(original['BASS_TINYMIST_SHA256'], 'untrusted')

    def test_corrupt_cache_exposes_no_environment(self):
        entry, manifest = self.cache()
        manifest['fingerprint'] = 'cache'
        (entry / 'manifest.json').write_text(json.dumps(manifest))
        (entry / 'bin/tinymist').write_bytes(b'changed')
        config = self.root / 'config.json'
        config.write_text('{}')
        original = {'PATH': '/ordinary'}
        with patch.object(module, 'identity', return_value=({'pinned': True}, 'cache', {})):
            with self.assertRaises(ValueError):
                module.selected_environment(config, self.root, original)
        self.assertEqual(original, {'PATH': '/ordinary'})


if __name__ == '__main__':
    unittest.main()
