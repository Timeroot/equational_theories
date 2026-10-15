"""The publishing contract for old and new deployment bundles."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import website_data as wd


class WebsiteDataTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.site = self.root / 'site'
        for name in wd.ASSETS:
            p = self.site / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('{}' if name.endswith('.json') else 'asset')
        self.index = dict(commit='abc123', repository='example/repo', generated='test', relations=[])
        (self.site / 'research/data/index.json').write_text(json.dumps(self.index))
        self.para = self.site / 'research/data/parastrophes.json'
        self.para.write_text(json.dumps(dict(commit='abc123', local=False)))
        self.bundle = self.root / 'bundle.tar.gz'
        self.manifest = self.root / 'manifest.json'
        self.patch = patch.multiple(wd, BUNDLE=self.bundle, MANIFEST=self.manifest)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_v2_roundtrip_includes_parastrophes(self):
        wd.pack(self.site)
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['version'], 2)
        self.assertIn('research/data/parastrophes.json', manifest['files'])
        target = self.root / 'restored'
        wd.unpack(target)
        self.assertEqual((target / 'research/data/parastrophes.json').read_bytes(), self.para.read_bytes())

    def test_reject_local_or_mismatched_sources(self):
        for data in [dict(commit='abc123', local=True), dict(commit='different', local=False)]:
            self.para.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'same committed sources'):
                wd.pack(self.site)
            self.assertFalse(self.bundle.exists())

    def test_historical_v1_and_stale_optional_asset(self):
        names = set(wd.ASSETS) - {'research/data/parastrophes.json'}
        manifest = dict(version=1, source_commit='old', files={})
        with tarfile.open(self.bundle, 'w:gz') as archive:
            for name in sorted(names):
                data = (self.site / name).read_bytes()
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
                manifest['files'][name] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        data = self.bundle.read_bytes()
        manifest['archive'] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        self.manifest.write_text(json.dumps(manifest))
        target = self.root / 'old-restored'
        stale = target / 'research/data/parastrophes.json'
        stale.parent.mkdir(parents=True)
        stale.write_text('stale data')
        wd.unpack(target)
        self.assertFalse(stale.exists())
        self.assertTrue((target / 'research/data/index.json').exists())

    def test_v2_cannot_omit_new_asset(self):
        wd.pack(self.site)
        manifest = json.loads(self.manifest.read_text())
        del manifest['files']['research/data/parastrophes.json']
        self.manifest.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            wd.unpack(self.root / 'restored')


if __name__ == '__main__':
    unittest.main()
